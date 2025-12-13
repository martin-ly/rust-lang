# Tier 4: 测试与基准

> **文档类型**: 高级主题
> **难度**: ⭐⭐⭐⭐
> **适用版本**: Rust 1.90+
> **前置知识**: [性能工程实践](./03_性能工程实践.md)

---

## 目录

- [Tier 4: 测试与基准](#tier-4-测试与基准)
  - [目录](#目录)
  - [1. 测试策略](#1-测试策略)
    - [1.1 单元测试](#11-单元测试)
    - [1.2 集成测试](#12-集成测试)
    - [1.3 端到端测试](#13-端到端测试)
  - [2. 进程测试技巧](#2-进程测试技巧)
    - [2.1 超时处理](#21-超时处理)
    - [2.2 错误注入](#22-错误注入)
    - [2.3 僵尸进程处理](#23-僵尸进程处理)
    - [2.4 信号处理测试](#24-信号处理测试)
  - [3. 基准测试](#3-基准测试)
    - [3.1 Criterion框架](#31-criterion框架)
    - [3.2 IPC基准](#32-ipc基准)
    - [3.3 进程池基准](#33-进程池基准)
  - [4. 压力测试](#4-压力测试)
    - [4.1 负载生成](#41-负载生成)
    - [4.2 稳定性测试](#42-稳定性测试)
    - [4.3 内存泄漏检测](#43-内存泄漏检测)
    - [4.4 资源耗尽测试](#44-资源耗尽测试)
  - [5. CI/CD集成](#5-cicd集成)
    - [5.1 GitHub Actions](#51-github-actions)
    - [5.2 性能回归检测](#52-性能回归检测)
  - [6. 实战案例](#6-实战案例)
    - [案例：完整测试套件](#案例完整测试套件)
  - [7. 最佳实践](#7-最佳实践)
  - [总结](#总结)

---

## 1. 测试策略

### 1.1 单元测试

**基础进程测试**:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;

    #[test]
    fn test_spawn_echo() {
        let output = Command::new("echo")
            .arg("test")
            .output()
            .expect("Failed to spawn");

        assert!(output.status.success());
        assert_eq!(output.stdout, b"test\n");
    }

    #[test]
    fn test_spawn_failure() {
        let result = Command::new("nonexistent_command_12345").spawn();
        assert!(result.is_err());
    }

    #[test]
    fn test_exit_code() {
        let status = Command::new("sh")
            .arg("-c")
            .arg("exit 42")
            .status()
            .unwrap();

        assert_eq!(status.code(), Some(42));
    }
}
```

**Mock进程**:

```rust
pub struct MockProcess {
    exit_code: i32,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    delay: Duration,
}

impl MockProcess {
    pub fn builder() -> MockProcessBuilder {
        MockProcessBuilder::default()
    }

    pub async fn run(&self) -> std::io::Result<MockOutput> {
        tokio::time::sleep(self.delay).await;

        Ok(MockOutput {
            status: MockStatus { code: self.exit_code },
            stdout: self.stdout.clone(),
            stderr: self.stderr.clone(),
        })
    }
}

// 使用示例
#[tokio::test]
async fn test_with_mock() {
    let mock = MockProcess::builder()
        .exit_code(0)
        .stdout(b"success")
        .delay(Duration::from_millis(10))
        .build();

    let output = mock.run().await.unwrap();
    assert_eq!(output.stdout, b"success");
}
```

### 1.2 集成测试

**进程通信测试**:

```rust
#[tokio::test]
async fn test_process_communication() {
    let mut child = tokio::process::Command::new("cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let mut stdin = child.stdin.take().unwrap();
    stdin.write_all(b"hello world").await.unwrap();
    drop(stdin);  // 关闭stdin以触发EOF

    let output = child.wait_with_output().await.unwrap();
    assert_eq!(output.stdout, b"hello world");
}

#[tokio::test]
async fn test_pipeline() {
    // 测试进程管道：echo "test" | wc -c
    let echo = tokio::process::Command::new("echo")
        .arg("test")
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let mut wc = tokio::process::Command::new("wc")
        .arg("-c")
        .stdin(echo.stdout.unwrap())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();

    let output = wc.wait_with_output().await.unwrap();
    let count = String::from_utf8_lossy(&output.stdout).trim().parse::<i32>().unwrap();
    assert_eq!(count, 5);  // "test\n" = 5 bytes
}
```

### 1.3 端到端测试

**完整工作流测试**:

```rust
#[tokio::test]
async fn test_process_pool_workflow() {
    let pool = ProcessPool::new(4);

    // 1. 提交任务
    let tasks: Vec<_> = (0..100).map(|i| Task { id: i }).collect();
    for task in tasks {
        pool.submit(task).await.unwrap();
    }

    // 2. 等待完成
    pool.wait_all().await;

    // 3. 验证结果
    let results = pool.get_results();
    assert_eq!(results.len(), 100);
    assert!(results.iter().all(|r| r.success));
}
```

---

## 2. 进程测试技巧

### 2.1 超时处理

**测试超时保护**:

```rust
use tokio::time::{timeout, Duration};

#[tokio::test]
async fn test_with_timeout() {
    let result = timeout(
        Duration::from_secs(5),
        async {
            let output = tokio::process::Command::new("sleep")
                .arg("10")
                .output()
                .await?;
            Ok::<_, std::io::Error>(output)
        }
    ).await;

    assert!(result.is_err(), "应该超时");
}

// 通用超时包装器
pub async fn with_timeout<F, T>(
    duration: Duration,
    future: F,
) -> Result<T, TimeoutError>
where
    F: Future<Output = T>,
{
    timeout(duration, future)
        .await
        .map_err(|_| TimeoutError::new(duration))
}
```

### 2.2 错误注入

**故障模拟**:

```rust
pub struct FaultInjector {
    fail_rate: f64,  // 0.0 - 1.0
}

impl FaultInjector {
    pub fn should_fail(&self) -> bool {
        use rand::Rng;
        rand::thread_rng().gen::<f64>() < self.fail_rate
    }

    pub fn maybe_fail<T, E>(&self, result: Result<T, E>) -> Result<T, E> {
        if self.should_fail() {
            // 随机失败
            Err(result.err().unwrap_or_else(|| panic!("No error to inject")))
        } else {
            result
        }
    }
}

#[tokio::test]
async fn test_with_fault_injection() {
    let injector = FaultInjector { fail_rate: 0.5 };

    let mut failures = 0;
    for _ in 0..100 {
        let result = injector.maybe_fail::<(), &str>(Ok(()));
        if result.is_err() {
            failures += 1;
        }
    }

    // 应该有大约50次失败
    assert!(failures > 30 && failures < 70);
}
```

### 2.3 僵尸进程处理

**自动清理**:

```rust
pub struct ProcessGuard {
    child: Option<Child>,
}

impl ProcessGuard {
    pub fn new(child: Child) -> Self {
        Self { child: Some(child) }
    }

    pub fn pid(&self) -> u32 {
        self.child.as_ref().unwrap().id()
    }
}

impl Drop for ProcessGuard {
    fn drop(&mut self) {
        if let Some(mut child) = self.child.take() {
            // 确保进程被清理
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

#[test]
fn test_no_zombie() {
    let guard = ProcessGuard::new(
        Command::new("sleep").arg("100").spawn().unwrap()
    );

    let pid = guard.pid();
    // guard会在作用域结束时自动清理进程
    drop(guard);

    std::thread::sleep(Duration::from_millis(100));

    // 验证进程已被清理
    #[cfg(unix)]
    {
        use nix::sys::signal::{kill, Signal};
        use nix::unistd::Pid;
        let result = kill(Pid::from_raw(pid as i32), Signal::SIGKILL);
        assert!(result.is_err());  // 进程应该已不存在
    }
}
```

### 2.4 信号处理测试

**信号测试**:

```rust
#[cfg(unix)]
#[test]
fn test_signal_handling() {
    use nix::sys::signal::{kill, Signal};
    use nix::unistd::Pid;

    let mut child = Command::new("sleep")
        .arg("100")
        .spawn()
        .unwrap();

    let pid = child.id();

    // 发送SIGTERM
    kill(Pid::from_raw(pid as i32), Signal::SIGTERM).unwrap();

    // 等待进程退出
    let status = child.wait().unwrap();

    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        assert_eq!(status.signal(), Some(15));  // SIGTERM
    }
}
```

---

## 3. 基准测试

### 3.1 Criterion框架

**完整基准测试**:

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use std::process::Command;

fn bench_process_spawn(c: &mut Criterion) {
    c.bench_function("spawn_echo", |b| {
        b.iter(|| {
            Command::new("echo")
                .arg(black_box("test"))
                .output()
                .unwrap()
        });
    });
}

fn bench_process_spawn_different_sizes(c: &mut Criterion) {
    let mut group = c.benchmark_group("spawn_with_args");

    for size in [1, 10, 100, 1000].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let args: Vec<_> = (0..size).map(|i| format!("arg{}", i)).collect();
            b.iter(|| {
                Command::new("echo")
                    .args(&args)
                    .output()
                    .unwrap()
            });
        });
    }
    group.finish();
}

criterion_group!(benches, bench_process_spawn, bench_process_spawn_different_sizes);
criterion_main!(benches);
```

### 3.2 IPC基准

**通信性能测试**:

```rust
use criterion::{criterion_group, criterion_main, Criterion, Throughput};

fn bench_pipe_throughput(c: &mut Criterion) {
    let mut group = c.benchmark_group("pipe_throughput");

    for size in [1024, 4096, 16384, 65536].iter() {
        group.throughput(Throughput::Bytes(*size as u64));

        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let data = vec![0u8; size];

            b.iter(|| {
                let mut child = Command::new("cat")
                    .stdin(Stdio::piped())
                    .stdout(Stdio::piped())
                    .spawn()
                    .unwrap();

                child.stdin.as_mut().unwrap().write_all(&data).unwrap();
                drop(child.stdin.take());

                let output = child.wait_with_output().unwrap();
                black_box(output);
            });
        });
    }

    group.finish();
}

criterion_group!(benches, bench_pipe_throughput);
criterion_main!(benches);
```

### 3.3 进程池基准

**池性能对比**:

```rust
fn bench_process_pool(c: &mut Criterion) {
    let mut group = c.benchmark_group("process_pool");

    // 基准：无池
    group.bench_function("no_pool", |b| {
        b.iter(|| {
            for _ in 0..10 {
                Command::new("true").status().unwrap();
            }
        });
    });

    // 基准：固定池
    group.bench_function("fixed_pool", |b| {
        let pool = ProcessPool::new(4);
        b.iter(|| {
            for _ in 0..10 {
                pool.execute(|| Command::new("true").status()).unwrap();
            }
        });
    });

    // 基准：动态池
    group.bench_function("dynamic_pool", |b| {
        let pool = DynamicProcessPool::new(2, 8);
        b.iter(|| {
            for _ in 0..10 {
                pool.execute(|| Command::new("true").status()).unwrap();
            }
        });
    });

    group.finish();
}
```

---

## 4. 压力测试

### 4.1 负载生成

**高并发测试**:

```rust
#[tokio::test(flavor = "multi_thread", worker_threads = 8)]
async fn test_concurrent_spawns() {
    let handles: Vec<_> = (0..1000)
        .map(|i| {
            tokio::spawn(async move {
                let output = tokio::process::Command::new("echo")
                    .arg(format!("task-{}", i))
                    .output()
                    .await
                    .unwrap();

                assert!(output.status.success());
            })
        })
        .collect();

    for handle in handles {
        handle.await.unwrap();
    }
}
```

### 4.2 稳定性测试

**长时间运行测试**:

```rust
#[tokio::test]
#[ignore]  // 使用 cargo test -- --ignored 运行
async fn test_stability_24h() {
    let start = Instant::now();
    let target_duration = Duration::from_secs(24 * 3600);

    let mut iterations = 0;
    let mut failures = 0;

    while start.elapsed() < target_duration {
        match spawn_and_run_task().await {
            Ok(_) => iterations += 1,
            Err(e) => {
                failures += 1;
                eprintln!("Failure: {:?}", e);
            }
        }

        if iterations % 1000 == 0 {
            println!("Iterations: {}, Failures: {}, Uptime: {:?}",
                iterations, failures, start.elapsed());
        }
    }

    let failure_rate = failures as f64 / iterations as f64;
    assert!(failure_rate < 0.001, "故障率过高: {:.4}%", failure_rate * 100.0);
}
```

### 4.3 内存泄漏检测

**内存增长测试**:

```rust
#[test]
fn test_no_memory_leak() {
    use sysinfo::{System, SystemExt, ProcessExt};

    let mut system = System::new_all();
    let pid = sysinfo::Pid::from(std::process::id() as usize);

    system.refresh_all();
    let initial_memory = system.process(pid).unwrap().memory();

    // 运行1000次操作
    for _ in 0..1000 {
        let child = Command::new("echo")
            .arg("test")
            .spawn()
            .unwrap();
        child.wait_with_output().unwrap();
    }

    system.refresh_all();
    let final_memory = system.process(pid).unwrap().memory();

    let growth = (final_memory as f64 - initial_memory as f64) / initial_memory as f64;

    // 允许10%的内存增长
    assert!(growth < 0.10, "内存增长过大: {:.2}%", growth * 100.0);
}
```

### 4.4 资源耗尽测试

**文件描述符测试**:

```rust
#[test]
fn test_fd_exhaustion() {
    let max_fds = 100;
    let mut children = Vec::new();

    for i in 0..max_fds {
        match Command::new("sleep").arg("1").spawn() {
            Ok(child) => children.push(child),
            Err(e) => {
                eprintln!("Failed at {}: {:?}", i, e);
                break;
            }
        }
    }

    // 清理
    for mut child in children {
        child.kill().ok();
        child.wait().ok();
    }
}
```

---

## 5. CI/CD集成

### 5.1 GitHub Actions

**完整CI配置**:

```yaml
# .github/workflows/test.yml
name: Process Tests

on: [push, pull_request]

jobs:
  test:
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        os: [ubuntu-latest, macos-latest, windows-latest]
        rust: [stable, beta, nightly]

    steps:
    - uses: actions/checkout@v2

    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        profile: minimal
        toolchain: ${{ matrix.rust }}
        override: true

    - name: Run tests
      run: cargo test --all-features

    - name: Run benchmarks
      run: cargo bench --no-run

    - name: Run stress tests
      run: cargo test --release -- --ignored --test-threads=1

  coverage:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v2

    - name: Install tarpaulin
      run: cargo install cargo-tarpaulin

    - name: Generate coverage
      run: cargo tarpaulin --out Xml

    - name: Upload coverage
      uses: codecov/codecov-action@v2
```

### 5.2 性能回归检测

**自动化性能测试**:

```yaml
name: Performance Regression

on:
  pull_request:
    branches: [ main ]

jobs:
  bench:
    runs-on: ubuntu-latest
    steps:
    - uses: actions/checkout@v2

    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: stable

    - name: Run benchmarks (baseline)
      run: |
        git checkout main
        cargo bench --bench process_bench -- --save-baseline main

    - name: Run benchmarks (PR)
      run: |
        git checkout ${{ github.sha }}
        cargo bench --bench process_bench -- --baseline main

    - name: Check for regression
      run: |
        if grep -q "regressed" target/criterion/*/report/index.html; then
          echo "Performance regression detected!"
          exit 1
        fi
```

---

## 6. 实战案例

### 案例：完整测试套件

**测试组织结构**:

```text
tests/
├── unit/
│   ├── process_spawn_test.rs
│   ├── process_pool_test.rs
│   └── ipc_test.rs
├── integration/
│   ├── workflow_test.rs
│   └── error_handling_test.rs
├── stress/
│   ├── concurrent_test.rs
│   └── stability_test.rs
└── benches/
    ├── spawn_bench.rs
    └── pool_bench.rs
```

**测试辅助工具**:

```rust
// tests/common/mod.rs
pub struct TestContext {
    temp_dir: TempDir,
    process_guard: Vec<ProcessGuard>,
}

impl TestContext {
    pub fn new() -> Self {
        Self {
            temp_dir: TempDir::new().unwrap(),
            process_guard: Vec::new(),
        }
    }

    pub fn spawn_guarded(&mut self, cmd: Command) -> std::io::Result<&mut Child> {
        let child = cmd.spawn()?;
        self.process_guard.push(ProcessGuard::new(child));
        Ok(self.process_guard.last_mut().unwrap().child())
    }

    pub fn temp_file(&self, name: &str) -> PathBuf {
        self.temp_dir.path().join(name)
    }
}

impl Drop for TestContext {
    fn drop(&mut self) {
        // 自动清理所有进程和临时文件
        self.process_guard.clear();
    }
}

// 使用示例
#[test]
fn test_with_context() {
    let mut ctx = TestContext::new();

    let child = ctx.spawn_guarded(
        Command::new("echo").arg("test")
    ).unwrap();

    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());

    // ctx被drop时自动清理
}
```

---

## 7. 最佳实践

**1. 测试隔离**:

```rust
// ✅ 推荐：每个测试独立
#[test]
fn test_isolated() {
    let temp_dir = tempfile::tempdir().unwrap();
    // 测试逻辑
} // temp_dir自动清理

// ❌ 避免：共享状态
static SHARED: Mutex<State> = Mutex::new(State::new());
```

**2. 确定性测试**:

```rust
// ✅ 推荐：确定性
#[test]
fn test_deterministic() {
    let output = Command::new("echo").arg("test").output().unwrap();
    assert_eq!(output.stdout, b"test\n");
}

// ❌ 避免：依赖时间
#[test]
fn test_timing_dependent() {
    let start = Instant::now();
    // 可能在不同机器上失败
    assert!(start.elapsed() < Duration::from_millis(10));
}
```

**3. 快速反馈**:

- ✅ 单元测试 < 100ms
- ✅ 集成测试 < 5s
- ✅ 压力测试标记为`#[ignore]`

**4. 清理资源**:

```rust
// ✅ 使用RAII
pub struct TestProcess(Child);

impl Drop for TestProcess {
    fn drop(&mut self) {
        self.0.kill().ok();
        self.0.wait().ok();
    }
}
```

**5. 有意义的断言**:

```rust
// ✅ 推荐：清晰的错误消息
assert_eq!(actual, expected, "进程输出不匹配: {:?}", actual);

// ❌ 避免：无信息的断言
assert!(condition);
```

---

## 总结

**测试与基准核心要素**:

1. ✅ **测试策略**: 单元/集成/端到端
2. ✅ **测试技巧**: 超时/错误注入/僵尸清理/信号测试
3. ✅ **基准测试**: Criterion框架/IPC性能/池对比
4. ✅ **压力测试**: 高并发/稳定性/内存泄漏/资源耗尽
5. ✅ **CI/CD**: GitHub Actions/性能回归检测
6. ✅ **最佳实践**: 隔离/确定性/快速反馈/清理/断言

**测试金字塔**:

```text
    /\        E2E测试 (少量, 慢)
   /  \
  /    \      集成测试 (中等)
 /      \
/________\    单元测试 (大量, 快)
```

---

**下一步**: [05_现代进程库.md](./05_现代进程库.md)

---

**文档维护**: Documentation Team
**创建日期**: 2025-10-22
**最后更新**: 2025-10-23
**适用版本**: Rust 1.90+
