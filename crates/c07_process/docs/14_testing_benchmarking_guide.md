# Rust 进程管理测试与基准测试指南

## 概述

本指南详细介绍 Rust 进程管理的测试策略、基准测试方法和性能评估技术，帮助开发者构建可靠、高性能的进程管理系统。

## 目录

- [Rust 进程管理测试与基准测试指南](#rust-进程管理测试与基准测试指南)
  - [概述](#概述)
  - [目录](#目录)
  - [测试策略](#测试策略)
    - [测试金字塔](#测试金字塔)
    - [测试类型](#测试类型)
  - [单元测试](#单元测试)
    - [基础进程操作测试](#基础进程操作测试)
    - [异步进程管理测试](#异步进程管理测试)
  - [集成测试](#集成测试)
    - [进程间通信测试](#进程间通信测试)
  - [性能基准测试](#性能基准测试)
    - [Criterion 基准测试](#criterion-基准测试)
    - [异步性能测试](#异步性能测试)
  - [压力测试](#压力测试)
    - [高并发进程测试](#高并发进程测试)
  - [安全测试](#安全测试)
    - [权限和安全测试](#权限和安全测试)
  - [跨平台测试](#跨平台测试)
    - [平台特定测试](#平台特定测试)
  - [持续集成测试](#持续集成测试)
    - [GitHub Actions 配置](#github-actions-配置)
    - [测试覆盖率](#测试覆盖率)
  - [测试工具和框架](#测试工具和框架)
    - [推荐工具](#推荐工具)
    - [测试辅助函数](#测试辅助函数)
  - [最佳实践](#最佳实践)
    - [测试设计原则](#测试设计原则)
    - [性能测试最佳实践](#性能测试最佳实践)
    - [安全测试最佳实践](#安全测试最佳实践)
  - [总结](#总结)

## 测试策略

### 测试金字塔

```text
    /\
   /  \     E2E 测试 (少量)
  /____\
 /      \   集成测试 (适量)
/________\
          单元测试 (大量)
```

### 测试类型

- **单元测试**: 测试单个函数或模块
- **集成测试**: 测试模块间的交互
- **端到端测试**: 测试完整的工作流程
- **性能测试**: 测试性能和资源使用
- **安全测试**: 测试安全漏洞和权限控制

## 单元测试

### 基础进程操作测试

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use std::process::Command;
    use std::time::Duration;
    use tokio::time::timeout;

    #[test]
    fn test_basic_process_spawn() {
        let mut cmd = Command::new("echo");
        cmd.arg("Hello, World!");

        let output = cmd.output().expect("Failed to execute command");
        assert!(output.status.success());
        assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "Hello, World!");
    }

    #[test]
    fn test_process_with_timeout() {
        let mut cmd = Command::new("sleep");
        cmd.arg("2");

        let start = std::time::Instant::now();
        let result = timeout(Duration::from_secs(1), async {
            cmd.output()
        }).await;

        assert!(result.is_err()); // 应该超时
        assert!(start.elapsed() >= Duration::from_secs(1));
    }

    #[test]
    fn test_process_error_handling() {
        let mut cmd = Command::new("nonexistent_command");
        let result = cmd.output();

        assert!(result.is_err());
        match result.unwrap_err().kind() {
            std::io::ErrorKind::NotFound => {
                // 预期的错误类型
            }
            _ => panic!("Unexpected error type"),
        }
    }
}
```

### 异步进程管理测试

```rust
#[cfg(test)]
mod async_tests {
    use super::*;
    use tokio::process::Command as TokioCommand;
    use tokio::time::{timeout, Duration};

    #[tokio::test]
    async fn test_async_process_spawn() {
        let mut cmd = TokioCommand::new("echo");
        cmd.arg("Async Hello");

        let output = cmd.output().await.expect("Failed to execute command");
        assert!(output.status.success());
        assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "Async Hello");
    }

    #[tokio::test]
    async fn test_concurrent_process_execution() {
        let handles: Vec<_> = (0..10)
            .map(|i| {
                tokio::spawn(async move {
                    let mut cmd = TokioCommand::new("echo");
                    cmd.arg(format!("Process {}", i));
                    cmd.output().await
                })
            })
            .collect();

        let results = futures::future::join_all(handles).await;

        for (i, result) in results.iter().enumerate() {
            let output = result.as_ref().unwrap().as_ref().unwrap();
            assert!(output.status.success());
            assert_eq!(
                String::from_utf8_lossy(&output.stdout).trim(),
                format!("Process {}", i)
            );
        }
    }

    #[tokio::test]
    async fn test_process_pool() {
        let pool = ProcessPool::new(5);

        let tasks: Vec<_> = (0..20)
            .map(|i| {
                let pool = pool.clone();
                tokio::spawn(async move {
                    pool.execute(format!("echo Task {}", i)).await
                })
            })
            .collect();

        let results = futures::future::join_all(tasks).await;

        for result in results {
            assert!(result.unwrap().is_ok());
        }
    }
}
```

## 集成测试

### 进程间通信测试

```rust
#[cfg(test)]
mod integration_tests {
    use super::*;
    use std::process::{Command, Stdio};
    use std::io::{BufRead, BufReader, Write};

    #[test]
    fn test_pipe_communication() {
        let mut child = Command::new("cat")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("Failed to spawn child process");

        let mut stdin = child.stdin.take().unwrap();
        let stdout = child.stdout.take().unwrap();

        // 写入数据
        stdin.write_all(b"Hello, Pipe!").unwrap();
        drop(stdin);

        // 读取输出
        let reader = BufReader::new(stdout);
        let output: String = reader.lines()
            .map(|line| line.unwrap())
            .collect::<Vec<_>>()
            .join("\n");

        assert_eq!(output, "Hello, Pipe!");

        // 等待进程结束
        let status = child.wait().unwrap();
        assert!(status.success());
    }

    #[test]
    fn test_process_chain() {
        // 测试命令链: echo "hello" | tr 'a-z' 'A-Z' | wc -c
        let echo_output = Command::new("echo")
            .arg("hello")
            .output()
            .unwrap();

        let tr_output = Command::new("tr")
            .arg("a-z")
            .arg("A-Z")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();

        let mut tr_stdin = tr_output.stdin.unwrap();
        tr_stdin.write_all(&echo_output.stdout).unwrap();
        drop(tr_stdin);

        let tr_result = tr_output.wait_with_output().unwrap();
        assert!(tr_result.status.success());

        let wc_output = Command::new("wc")
            .arg("-c")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();

        let mut wc_stdin = wc_output.stdin.unwrap();
        wc_stdin.write_all(&tr_result.stdout).unwrap();
        drop(wc_stdin);

        let wc_result = wc_output.wait_with_output().unwrap();
        assert!(wc_result.status.success());

        let count: usize = String::from_utf8_lossy(&wc_result.stdout)
            .trim()
            .parse()
            .unwrap();
        assert_eq!(count, 6); // "HELLO" + newline
    }
}
```

## 性能基准测试

### Criterion 基准测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use std::process::Command;

fn benchmark_process_spawn(c: &mut Criterion) {
    let mut group = c.benchmark_group("process_spawn");

    group.bench_function("echo_command", |b| {
        b.iter(|| {
            let output = Command::new("echo")
                .arg(black_box("Hello, World!"))
                .output()
                .unwrap();
            black_box(output)
        })
    });

    group.bench_function("true_command", |b| {
        b.iter(|| {
            let status = Command::new("true")
                .status()
                .unwrap();
            black_box(status)
        })
    });

    group.finish();
}

fn benchmark_concurrent_processes(c: &mut Criterion) {
    let mut group = c.benchmark_group("concurrent_processes");

    for &concurrency in &[1, 2, 4, 8, 16] {
        group.bench_with_input(
            BenchmarkId::new("spawn", concurrency),
            &concurrency,
            |b, &concurrency| {
                b.iter(|| {
                    let handles: Vec<_> = (0..concurrency)
                        .map(|_| {
                            std::thread::spawn(|| {
                                Command::new("echo")
                                    .arg("test")
                                    .output()
                                    .unwrap()
                            })
                        })
                        .collect();

                    for handle in handles {
                        black_box(handle.join().unwrap());
                    }
                })
            },
        );
    }

    group.finish();
}

fn benchmark_process_communication(c: &mut Criterion) {
    let mut group = c.benchmark_group("process_communication");

    group.bench_function("pipe_small_data", |b| {
        b.iter(|| {
            let mut child = Command::new("cat")
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::piped())
                .spawn()
                .unwrap();

            let mut stdin = child.stdin.take().unwrap();
            stdin.write_all(black_box(b"small data")).unwrap();
            drop(stdin);

            let output = child.wait_with_output().unwrap();
            black_box(output)
        })
    });

    group.bench_function("pipe_large_data", |b| {
        let large_data = vec![b'A'; 1024 * 1024]; // 1MB

        b.iter(|| {
            let mut child = Command::new("cat")
                .stdin(std::process::Stdio::piped())
                .stdout(std::process::Stdio::piped())
                .spawn()
                .unwrap();

            let mut stdin = child.stdin.take().unwrap();
            stdin.write_all(black_box(&large_data)).unwrap();
            drop(stdin);

            let output = child.wait_with_output().unwrap();
            black_box(output)
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    benchmark_process_spawn,
    benchmark_concurrent_processes,
    benchmark_process_communication
);
criterion_main!(benches);
```

### 异步性能测试

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use tokio::process::Command as TokioCommand;
use tokio::runtime::Runtime;

fn benchmark_async_process_spawn(c: &mut Criterion) {
    let rt = Runtime::new().unwrap();

    let mut group = c.benchmark_group("async_process_spawn");

    group.bench_function("tokio_echo", |b| {
        b.iter(|| {
            rt.block_on(async {
                let output = TokioCommand::new("echo")
                    .arg(black_box("Hello, Async!"))
                    .output()
                    .await
                    .unwrap();
                black_box(output)
            })
        })
    });

    group.bench_function("tokio_concurrent", |b| {
        b.iter(|| {
            rt.block_on(async {
                let handles: Vec<_> = (0..10)
                    .map(|_| {
                        tokio::spawn(async {
                            TokioCommand::new("echo")
                                .arg("test")
                                .output()
                                .await
                                .unwrap()
                        })
                    })
                    .collect();

                for handle in handles {
                    black_box(handle.await.unwrap());
                }
            })
        })
    });

    group.finish();
}

criterion_group!(async_benches, benchmark_async_process_spawn);
criterion_main!(async_benches);
```

## 压力测试

### 高并发进程测试

```rust
#[cfg(test)]
mod stress_tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::Arc;
    use tokio::sync::Semaphore;

    #[tokio::test]
    async fn test_high_concurrency_processes() {
        const CONCURRENT_LIMIT: usize = 1000;
        const TOTAL_PROCESSES: usize = 10000;

        let semaphore = Arc::new(Semaphore::new(CONCURRENT_LIMIT));
        let counter = Arc::new(AtomicUsize::new(0));

        let handles: Vec<_> = (0..TOTAL_PROCESSES)
            .map(|i| {
                let semaphore = semaphore.clone();
                let counter = counter.clone();

                tokio::spawn(async move {
                    let _permit = semaphore.acquire().await.unwrap();

                    let mut cmd = TokioCommand::new("echo");
                    cmd.arg(format!("Process {}", i));

                    let result = cmd.output().await;
                    counter.fetch_add(1, Ordering::Relaxed);

                    assert!(result.is_ok());
                    result
                })
            })
            .collect();

        // 等待所有进程完成
        for handle in handles {
            handle.await.unwrap().unwrap();
        }

        assert_eq!(counter.load(Ordering::Relaxed), TOTAL_PROCESSES);
    }

    #[tokio::test]
    async fn test_memory_pressure() {
        const MEMORY_INTENSIVE_PROCESSES: usize = 100;

        let handles: Vec<_> = (0..MEMORY_INTENSIVE_PROCESSES)
            .map(|i| {
                tokio::spawn(async move {
                    // 创建大量数据的进程
                    let mut cmd = TokioCommand::new("dd");
                    cmd.args(&["if=/dev/zero", "bs=1M", "count=10"]);

                    let result = cmd.output().await;
                    assert!(result.is_ok());

                    println!("Memory intensive process {} completed", i);
                })
            })
            .collect();

        for handle in handles {
            handle.await.unwrap();
        }
    }

    #[tokio::test]
    async fn test_cpu_intensive_processes() {
        const CPU_INTENSIVE_PROCESSES: usize = 50;

        let handles: Vec<_> = (0..CPU_INTENSIVE_PROCESSES)
            .map(|i| {
                tokio::spawn(async move {
                    // CPU 密集型进程
                    let mut cmd = TokioCommand::new("yes");
                    cmd.arg("CPU intensive test");

                    // 运行 1 秒后终止
                    let mut child = cmd.spawn().unwrap();
                    tokio::time::sleep(Duration::from_secs(1)).await;
                    child.kill().unwrap();

                    println!("CPU intensive process {} completed", i);
                })
            })
            .collect();

        for handle in handles {
            handle.await.unwrap();
        }
    }
}
```

## 安全测试

### 权限和安全测试

```rust
#[cfg(test)]
mod security_tests {
    use super::*;
    use std::fs::File;
    use std::io::Write;
    use tempfile::TempDir;

    #[test]
    fn test_file_permission_restriction() {
        let temp_dir = TempDir::new().unwrap();
        let protected_file = temp_dir.path().join("protected.txt");

        // 创建受保护的文件
        let mut file = File::create(&protected_file).unwrap();
        file.write_all(b"sensitive data").unwrap();

        // 尝试通过进程访问
        let output = Command::new("cat")
            .arg(&protected_file)
            .output();

        // 根据系统权限，可能成功或失败
        match output {
            Ok(output) => {
                if output.status.success() {
                    println!("File access successful");
                } else {
                    println!("File access denied");
                }
            }
            Err(e) => {
                println!("Process execution failed: {}", e);
            }
        }
    }

    #[test]
    fn test_command_injection_prevention() {
        // 测试命令注入防护
        let malicious_input = "test; rm -rf /";

        let output = Command::new("echo")
            .arg(malicious_input) // 应该被安全处理
            .output()
            .unwrap();

        assert!(output.status.success());
        let result = String::from_utf8_lossy(&output.stdout);

        // 验证输入被正确转义
        assert!(result.contains("test; rm -rf /"));
        assert!(!result.contains("rm -rf /")); // 不应该执行恶意命令
    }

    #[test]
    fn test_process_isolation() {
        // 测试进程隔离
        let temp_dir = TempDir::new().unwrap();
        let test_file = temp_dir.path().join("test.txt");

        // 在子进程中创建文件
        let output = Command::new("touch")
            .arg(&test_file)
            .output()
            .unwrap();

        assert!(output.status.success());
        assert!(test_file.exists());

        // 验证文件权限
        let metadata = std::fs::metadata(&test_file).unwrap();
        println!("File permissions: {:?}", metadata.permissions());
    }

    #[test]
    fn test_environment_variable_isolation() {
        // 测试环境变量隔离
        let mut cmd = Command::new("env");
        cmd.env("TEST_VAR", "test_value");
        cmd.env_remove("PATH"); // 移除 PATH 环境变量

        let output = cmd.output().unwrap();

        if output.status.success() {
            let env_output = String::from_utf8_lossy(&output.stdout);
            assert!(env_output.contains("TEST_VAR=test_value"));
            // PATH 应该被移除或为空
        }
    }
}
```

## 跨平台测试

### 平台特定测试

```rust
#[cfg(test)]
mod platform_tests {
    use super::*;
    use std::env;

    #[test]
    fn test_windows_specific_commands() {
        #[cfg(target_os = "windows")]
        {
            let output = Command::new("cmd")
                .args(&["/C", "echo Windows test"])
                .output()
                .unwrap();

            assert!(output.status.success());
            let result = String::from_utf8_lossy(&output.stdout);
            assert!(result.contains("Windows test"));
        }

        #[cfg(not(target_os = "windows"))]
        {
            // 在非 Windows 系统上跳过
            println!("Skipping Windows-specific test");
        }
    }

    #[test]
    fn test_unix_specific_commands() {
        #[cfg(unix)]
        {
            let output = Command::new("sh")
                .arg("-c")
                .arg("echo 'Unix test'")
                .output()
                .unwrap();

            assert!(output.status.success());
            let result = String::from_utf8_lossy(&output.stdout);
            assert!(result.contains("Unix test"));
        }

        #[cfg(not(unix))]
        {
            println!("Skipping Unix-specific test");
        }
    }

    #[test]
    fn test_path_separator_handling() {
        let path_separator = if cfg!(windows) { "\\" } else { "/" };

        let test_path = format!("test{}file.txt", path_separator);

        let output = Command::new("echo")
            .arg(&test_path)
            .output()
            .unwrap();

        assert!(output.status.success());
        let result = String::from_utf8_lossy(&output.stdout);
        assert!(result.contains(&test_path));
    }
}
```

## 持续集成测试

### GitHub Actions 配置

```yaml
name: Process Management Tests

on:
  push:
    branches: [ main, develop ]
  pull_request:
    branches: [ main ]

jobs:
  test:
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        os: [ubuntu-latest, windows-latest, macos-latest]
        rust: [stable, beta, nightly]

    steps:
    - uses: actions/checkout@v3

    - name: Install Rust
      uses: actions-rs/toolchain@v1
      with:
        toolchain: ${{ matrix.rust }}
        override: true

    - name: Run tests
      run: cargo test --verbose

    - name: Run integration tests
      run: cargo test --test integration --verbose

    - name: Run security tests
      run: cargo test --test security --verbose

    - name: Run benchmarks
      run: cargo bench --verbose

    - name: Check formatting
      run: cargo fmt -- --check

    - name: Run clippy
      run: cargo clippy -- -D warnings
```

### 测试覆盖率

```rust
// 在 Cargo.toml 中添加
[dev-dependencies]
tarpaulin = "0.20"

// 运行覆盖率测试
// cargo tarpaulin --out html
```

## 测试工具和框架

### 推荐工具

1. **criterion**: 性能基准测试
2. **tokio-test**: 异步测试工具
3. **tempfile**: 临时文件处理
4. **mockall**: 模拟对象
5. **proptest**: 属性测试
6. **tarpaulin**: 代码覆盖率

### 测试辅助函数

```rust
pub mod test_utils {
    use super::*;
    use std::process::Command;
    use std::time::Duration;
    use tempfile::TempDir;

    pub fn create_test_command() -> Command {
        Command::new("echo")
    }

    pub fn create_temp_directory() -> TempDir {
        TempDir::new().expect("Failed to create temp directory")
    }

    pub fn wait_for_process_with_timeout(
        mut child: std::process::Child,
        timeout: Duration,
    ) -> Result<std::process::Output, Box<dyn std::error::Error>> {
        let start = std::time::Instant::now();

        loop {
            if let Some(status) = child.try_wait()? {
                return Ok(child.wait_with_output()?);
            }

            if start.elapsed() > timeout {
                child.kill()?;
                return Err("Process timeout".into());
            }

            std::thread::sleep(Duration::from_millis(10));
        }
    }

    pub fn assert_process_success(output: &std::process::Output) {
        assert!(output.status.success(),
            "Process failed with status: {:?}", output.status);
    }

    pub fn assert_process_output_contains(
        output: &std::process::Output,
        expected: &str
    ) {
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(stdout.contains(expected),
            "Expected '{}' in output: {}", expected, stdout);
    }
}
```

## 最佳实践

### 测试设计原则

1. **测试独立性**: 每个测试应该独立运行
2. **确定性**: 测试结果应该可重复
3. **快速执行**: 单元测试应该快速完成
4. **清晰命名**: 测试名称应该描述测试内容
5. **单一职责**: 每个测试只测试一个功能

### 性能测试最佳实践

1. **预热**: 在基准测试前进行预热
2. **多次运行**: 多次运行取平均值
3. **环境控制**: 在相同环境下运行测试
4. **资源监控**: 监控 CPU、内存使用
5. **趋势分析**: 跟踪性能变化趋势

### 安全测试最佳实践

1. **权限测试**: 测试各种权限级别
2. **输入验证**: 测试恶意输入处理
3. **隔离验证**: 验证进程隔离
4. **资源限制**: 测试资源限制功能
5. **审计日志**: 验证安全事件记录

## 总结

本指南提供了全面的 Rust 进程管理测试策略，包括：

- **多层次测试**: 从单元测试到端到端测试
- **性能评估**: 使用 Criterion 进行基准测试
- **安全验证**: 权限控制和隔离测试
- **跨平台兼容**: 不同操作系统的测试
- **持续集成**: 自动化测试流程

通过遵循这些测试策略和最佳实践，可以构建可靠、高性能、安全的 Rust 进程管理系统。
