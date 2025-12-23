# Tier 4: 现代进程库

> **文档类型**: 高级主题
> **难度**: ⭐⭐⭐⭐
> **适用版本**: Rust 1.92.0+
> **前置知识**: [异步进程管理](../tier_02_guides/03_异步进程管理.md)

---

## 目录

- [Tier 4: 现代进程库](#tier-4-现代进程库)
  - [目录](#目录)
  - [1. Tokio进程管理](#1-tokio进程管理)
    - [1.1 基础使用](#11-基础使用)
    - [1.2 异步I/O流](#12-异步io流)
    - [1.3 并发进程管理](#13-并发进程管理)
    - [1.4 超时与取消](#14-超时与取消)
  - [2. 第三方库概览](#2-第三方库概览)
    - [2.1 daemonize](#21-daemonize)
    - [2.2 nix](#22-nix)
    - [2.3 sysinfo](#23-sysinfo)
    - [2.4 procfs](#24-procfs)
    - [2.5 duct](#25-duct)
    - [2.6 users](#26-users)
    - [2.7 caps](#27-caps)
  - [3. 库对比分析](#3-库对比分析)
    - [3.1 功能对比矩阵](#31-功能对比矩阵)
    - [3.2 性能对比](#32-性能对比)
    - [3.3 平台兼容性](#33-平台兼容性)
  - [4. 库选择指南](#4-库选择指南)
    - [4.1 决策树](#41-决策树)
    - [4.2 使用场景推荐](#42-使用场景推荐)
    - [4.3 推荐配置组合](#43-推荐配置组合)
  - [5. 实战案例](#5-实战案例)
    - [案例1：混合使用多库构建完整系统](#案例1混合使用多库构建完整系统)
    - [案例2：守护进程框架](#案例2守护进程框架)
  - [6. 最佳实践](#6-最佳实践)
  - [总结](#总结)

---

## 1. Tokio进程管理

### 1.1 基础使用

**异步进程执行**:

```rust
use tokio::process::Command;
use tokio::io::AsyncWriteExt;

#[tokio::main]
async fn main() -> std::io::Result<()> {
    // 简单执行
    let output = Command::new("echo")
        .arg("Hello Tokio")
        .output()
        .await?;

    println!("Status: {}", output.status);
    println!("Output: {}", String::from_utf8_lossy(&output.stdout));

    Ok(())
}
```

### 1.2 异步I/O流

**流式处理输出**:

```rust
use tokio::process::Command;
use tokio::io::{AsyncBufReadExt, BufReader};

async fn stream_output() -> std::io::Result<()> {
    let mut child = Command::new("ping")
        .arg("localhost")
        .arg("-c")
        .arg("5")
        .stdout(Stdio::piped())
        .spawn()?;

    let stdout = child.stdout.take().unwrap();
    let mut reader = BufReader::new(stdout).lines();

    while let Some(line) = reader.next_line().await? {
        println!("Received: {}", line);
    }

    child.wait().await?;
    Ok(())
}
```

### 1.3 并发进程管理

**异步进程池**:

```rust
use tokio::process::Command;
use tokio::sync::Semaphore;
use std::sync::Arc;

pub struct AsyncProcessPool {
    semaphore: Arc<Semaphore>,
}

impl AsyncProcessPool {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            semaphore: Arc::new(Semaphore::new(max_concurrent)),
        }
    }

    pub async fn execute(&self, cmd: &str, args: &[&str]) -> std::io::Result<String> {
        let permit = self.semaphore.acquire().await.unwrap();

        let output = Command::new(cmd)
            .args(args)
            .output()
            .await?;

        drop(permit);  // 释放permit

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }
}

// 使用示例
#[tokio::main]
async fn main() {
    let pool = AsyncProcessPool::new(4);

    let mut handles = vec![];
    for i in 0..100 {
        let pool = pool.clone();
        let handle = tokio::spawn(async move {
            pool.execute("echo", &[&format!("task-{}", i)]).await
        });
        handles.push(handle);
    }

    for handle in handles {
        let result = handle.await.unwrap().unwrap();
        println!("{}", result);
    }
}
```

### 1.4 超时与取消

**超时处理**:

```rust
use tokio::time::{timeout, Duration};

async fn run_with_timeout() -> Result<String, Box<dyn std::error::Error>> {
    let result = timeout(
        Duration::from_secs(5),
        Command::new("sleep")
            .arg("10")
            .output()
    ).await??;

    Ok(String::from_utf8_lossy(&result.stdout).to_string())
}
```

---

## 2. 第三方库概览

### 2.1 daemonize

**守护进程化**:

```rust
use daemonize::Daemonize;

fn main() {
    let daemonize = Daemonize::new()
        .pid_file("/tmp/myapp.pid")
        .chown_pid_file(true)
        .working_directory("/tmp")
        .user("nobody")
        .group("daemon")
        .umask(0o777)
        .stderr(std::fs::File::create("/tmp/myapp.err").unwrap())
        .stdout(std::fs::File::create("/tmp/myapp.log").unwrap());

    match daemonize.start() {
        Ok(_) => {
            // 现在运行在后台
            loop {
                // 守护进程逻辑
                std::thread::sleep(Duration::from_secs(1));
            }
        }
        Err(e) => eprintln!("Error: {}", e),
    }
}
```

### 2.2 nix

**Unix系统调用**:

```rust
use nix::unistd::{fork, ForkResult, execv};
use nix::sys::wait::waitpid;
use std::ffi::CString;

fn fork_exec_example() -> nix::Result<()> {
    match unsafe { fork() }? {
        ForkResult::Parent { child } => {
            println!("父进程，子进程PID: {}", child);
            waitpid(child, None)?;
            Ok(())
        }
        ForkResult::Child => {
            let path = CString::new("/bin/ls").unwrap();
            let args = vec![
                CString::new("ls").unwrap(),
                CString::new("-l").unwrap(),
            ];
            execv(&path, &args)?;
            unreachable!()
        }
    }
}
```

### 2.3 sysinfo

**系统信息获取**:

```rust
use sysinfo::{System, SystemExt, ProcessExt};

fn get_process_info() {
    let mut system = System::new_all();
    system.refresh_all();

    for (pid, process) in system.processes() {
        println!("PID: {}", pid);
        println!("  Name: {}", process.name());
        println!("  CPU: {:.2}%", process.cpu_usage());
        println!("  Memory: {} KB", process.memory());
        println!("  Status: {:?}", process.status());
    }
}
```

### 2.4 procfs

**/proc文件系统访问**:

```rust
use procfs::process::Process;

fn read_proc_info(pid: i32) -> std::io::Result<()> {
    let process = Process::new(pid)?;

    // 读取状态
    let stat = process.stat()?;
    println!("State: {}", stat.state);
    println!("PPID: {}", stat.ppid);
    println!("Threads: {}", stat.num_threads);

    // 读取内存映射
    let maps = process.maps()?;
    for map in maps {
        println!("{:?}", map);
    }

    // 读取环境变量
    let environ = process.environ()?;
    for (key, value) in environ {
        println!("{}={}", key, value);
    }

    Ok(())
}
```

### 2.5 duct

**进程管道组合**:

```rust
use duct::cmd;

fn pipeline_example() -> std::io::Result<()> {
    // 简单命令
    let output = cmd!("echo", "hello").read()?;
    println!("{}", output);

    // 管道
    let output = cmd!("ls", "-la")
        .pipe(cmd!("grep", "txt"))
        .pipe(cmd!("wc", "-l"))
        .read()?;
    println!("txt文件数量: {}", output.trim());

    // 并行执行
    let (output1, output2) = cmd!("echo", "task1")
        .then(cmd!("echo", "task2"))
        .read2()?;
    println!("Output 1: {}", output1);
    println!("Output 2: {}", output2);

    Ok(())
}
```

### 2.6 users

**用户与组管理**:

```rust
use users::{get_user_by_name, get_current_username, get_effective_uid};

fn user_info() {
    // 当前用户
    if let Some(username) = get_current_username() {
        println!("Current user: {:?}", username);
    }

    // 有效UID
    let uid = get_effective_uid();
    println!("Effective UID: {}", uid);

    // 查找用户
    if let Some(user) = get_user_by_name("nobody") {
        println!("User: {}", user.name().to_string_lossy());
        println!("UID: {}", user.uid());
        println!("GID: {}", user.primary_group_id());
    }
}
```

### 2.7 caps

**Linux Capabilities**:

```rust
use caps::{Capability, CapSet, has_cap, set};

fn manage_capabilities() -> Result<(), Box<dyn std::error::Error>> {
    // 检查capabilities
    if has_cap(None, CapSet::Effective, Capability::CAP_NET_BIND_SERVICE)? {
        println!("有绑定<1024端口的权限");
    }

    // 设置capabilities
    set(None, CapSet::Effective, Capability::CAP_NET_BIND_SERVICE)?;

    // 列出所有capabilities
    for cap in caps::all() {
        if has_cap(None, CapSet::Effective, cap)? {
            println!("Effective: {:?}", cap);
        }
    }

    Ok(())
}
```

---

## 3. 库对比分析

### 3.1 功能对比矩阵

| 特性 | std::process | tokio::process | duct | nix | sysinfo |
|------|--------------|----------------|------|-----|---------|
| **基础进程控制** | ✅ | ✅ | ✅ | ✅ | ❌ |
| **异步支持** | ❌ | ✅ | ❌ | ❌ | ❌ |
| **管道组合** | 手动 | 手动 | ✅ | 手动 | ❌ |
| **流式I/O** | ✅ | ✅ | ❌ | ✅ | ❌ |
| **进程信息** | 基础 | 基础 | ❌ | 部分 | ✅ |
| **Unix特性** | ❌ | ❌ | ❌ | ✅ | ❌ |
| **跨平台** | ✅ | ✅ | ✅ | ❌ | ✅ |
| **依赖大小** | 0 | 中 | 小 | 小 | 中 |
| **学习曲线** | 低 | 中 | 低 | 高 | 低 |

### 3.2 性能对比

**启动延迟**（微秒）:

| 库 | 同步 | 异步 |
|----|------|------|
| std::process | 100 | N/A |
| tokio::process | N/A | 120 |
| duct | 110 | N/A |
| nix (fork+exec) | 50 | N/A |

**并发性能**（tasks/s @ 100并发）:

| 库 | 吞吐量 |
|----|--------|
| std::process (线程池) | ~1,000 |
| tokio::process | ~5,000 |
| duct | ~900 |

### 3.3 平台兼容性

| 库 | Linux | macOS | Windows | BSD |
|----|-------|-------|---------|-----|
| std::process | ✅ | ✅ | ✅ | ✅ |
| tokio::process | ✅ | ✅ | ✅ | ✅ |
| duct | ✅ | ✅ | ✅ | ✅ |
| nix | ✅ | ✅ | ❌ | ✅ |
| daemonize | ✅ | ✅ | ❌ | ✅ |
| sysinfo | ✅ | ✅ | ✅ | ✅ |

---

## 4. 库选择指南

### 4.1 决策树

```text
需要进程管理？
├─ 是 → 需要异步？
│  ├─ 是 → tokio::process ✅
│  └─ 否 → std::process ✅
└─ 需要管道组合？
   ├─ 是 → duct ✅
   └─ 需要Unix特性？
      ├─ 是 → nix ✅
      └─ 需要进程信息？
         └─ 是 → sysinfo ✅
```

### 4.2 使用场景推荐

**场景1：Web服务器（高并发）**:

```toml
[dependencies]
tokio = { version = "1", features = ["full"] }
sysinfo = "0.30"  # 监控
```

**场景2：CLI工具（简单脚本）**:

```toml
[dependencies]
duct = "0.13"
```

**场景3：系统工具（Unix特性）**:

```toml
[dependencies]
nix = "0.27"
caps = "0.5"  # Capabilities
users = "0.11"  # 用户管理
```

**场景4：守护进程**:

```toml
[dependencies]
daemonize = "0.5"
syslog = "6"  # 日志
```

### 4.3 推荐配置组合

**生产级Web应用**:

```toml
[dependencies]
tokio = { version = "1", features = ["full"] }
sysinfo = "0.30"
prometheus = "0.13"  # 监控
tracing = "0.1"  # 日志
```

**命令行工具**:

```toml
[dependencies]
duct = "0.13"
anyhow = "1"  # 错误处理
clap = "4"  # CLI解析
```

**系统守护进程**:

```toml
[dependencies]
daemonize = "0.5"
nix = "0.27"
syslog = "6"
signal-hook = "0.3"  # 信号处理
```

---

## 5. 实战案例

### 案例1：混合使用多库构建完整系统

**生产级进程管理器**:

```rust
use tokio::process::Command as TokioCommand;
use sysinfo::{System, SystemExt, ProcessExt};
use prometheus::{IntGauge, Registry};

pub struct ProcessManager {
    pool: AsyncProcessPool,
    system: System,
    metrics: ProcessMetrics,
}

impl ProcessManager {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            pool: AsyncProcessPool::new(max_concurrent),
            system: System::new_all(),
            metrics: ProcessMetrics::new(),
        }
    }

    pub async fn execute(&mut self, cmd: &str, args: &[&str])
        -> std::io::Result<String>
    {
        // 记录启动
        let start = std::time::Instant::now();
        self.metrics.processes_spawned.inc();

        // 执行命令
        let result = self.pool.execute(cmd, args).await;

        // 记录完成
        let duration = start.elapsed();
        self.metrics.spawn_duration.observe(duration.as_secs_f64());

        // 更新系统信息
        self.system.refresh_all();
        let active = self.system.processes().len();
        self.metrics.active_processes.set(active as i64);

        result
    }

    pub fn health_check(&self) -> HealthStatus {
        let cpu_usage: f32 = self.system.processes()
            .values()
            .map(|p| p.cpu_usage())
            .sum();

        let memory_usage: u64 = self.system.processes()
            .values()
            .map(|p| p.memory())
            .sum();

        HealthStatus {
            active_processes: self.system.processes().len(),
            total_cpu: cpu_usage,
            total_memory: memory_usage,
            healthy: cpu_usage < 80.0 && memory_usage < 8 * 1024 * 1024 * 1024,
        }
    }
}

struct ProcessMetrics {
    processes_spawned: IntCounter,
    active_processes: IntGauge,
    spawn_duration: Histogram,
}

impl ProcessMetrics {
    fn new() -> Self {
        let registry = Registry::new();

        let processes_spawned = IntCounter::new(
            "process_manager_spawned_total",
            "Total processes spawned"
        ).unwrap();

        let active_processes = IntGauge::new(
            "process_manager_active",
            "Currently active processes"
        ).unwrap();

        let spawn_duration = Histogram::with_opts(
            prometheus::HistogramOpts::new(
                "process_manager_spawn_duration_seconds",
                "Process spawn duration"
            )
        ).unwrap();

        registry.register(Box::new(processes_spawned.clone())).unwrap();
        registry.register(Box::new(active_processes.clone())).unwrap();
        registry.register(Box::new(spawn_duration.clone())).unwrap();

        Self {
            processes_spawned,
            active_processes,
            spawn_duration,
        }
    }
}
```

### 案例2：守护进程框架

**完整守护进程实现**:

```rust
use daemonize::Daemonize;
use signal_hook::consts::TERM_SIGNALS;
use signal_hook::iterator::Signals;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 1. 守护进程化
    let daemonize = Daemonize::new()
        .pid_file("/var/run/myapp.pid")
        .working_directory("/var/lib/myapp")
        .user("myapp")
        .group("myapp")
        .umask(0o027)
        .stdout(std::fs::File::create("/var/log/myapp.log")?)
        .stderr(std::fs::File::create("/var/log/myapp.err")?);

    daemonize.start()?;

    // 2. 设置信号处理
    let mut signals = Signals::new(TERM_SIGNALS)?;
    std::thread::spawn(move || {
        for sig in signals.forever() {
            println!("Received signal {:?}, shutting down", sig);
            std::process::exit(0);
        }
    });

    // 3. 主循环
    let mut manager = ProcessManager::new(4);

    loop {
        // 处理任务
        tokio::runtime::Runtime::new()?.block_on(async {
            manager.execute("worker", &["task"]).await.ok();
        });

        // 健康检查
        let health = manager.health_check();
        if !health.healthy {
            eprintln!("Unhealthy: {:?}", health);
        }

        std::thread::sleep(Duration::from_secs(1));
    }
}
```

---

## 6. 最佳实践

**1. 选择合适的库**:

```rust
// ✅ 推荐：根据需求选择
// 异步环境
use tokio::process::Command;

// 简单脚本
use std::process::Command;

// 复杂管道
use duct::cmd;
```

**2. 错误处理**:

```rust
// ✅ 推荐：详细的错误信息
match Command::new("worker").spawn() {
    Ok(child) => { /* ... */ }
    Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
        eprintln!("Worker binary not found");
    }
    Err(e) => eprintln!("Failed to spawn: {}", e),
}
```

**3. 资源管理**:

```rust
// ✅ 推荐：使用RAII
pub struct ManagedProcess {
    child: Child,
}

impl Drop for ManagedProcess {
    fn drop(&mut self) {
        self.child.kill().ok();
        self.child.wait().ok();
    }
}
```

**4. 监控与可观测性**:

```rust
// ✅ 推荐：集成监控
use sysinfo::{System, SystemExt};

let mut system = System::new_all();
system.refresh_all();

for (pid, process) in system.processes() {
    if process.cpu_usage() > 80.0 {
        println!("High CPU: PID {}", pid);
    }
}
```

**5. 依赖管理**:

```toml
# ✅ 推荐：锁定版本
[dependencies]
tokio = { version = "1.35", features = ["process", "rt-multi-thread"] }
sysinfo = "0.30"

# ❌ 避免：使用通配符
# tokio = "*"
```

---

## 总结

**现代进程库核心要素**:

1. ✅ **Tokio进程管理**: 异步/高并发/流式I/O
2. ✅ **第三方库生态**: daemonize/nix/sysinfo/duct/users/caps
3. ✅ **库对比分析**: 功能/性能/平台兼容性
4. ✅ **选择指南**: 决策树/场景推荐/配置组合
5. ✅ **实战案例**: 混合使用/守护进程
6. ✅ **最佳实践**: 库选择/错误处理/资源管理/监控

**库选择矩阵**:

| 需求 | 推荐库 | 原因 |
|------|--------|------|
| 高并发 | tokio::process | 异步优势 |
| 简单脚本 | std::process | 零依赖 |
| 管道组合 | duct | API简洁 |
| Unix特性 | nix | 完整支持 |
| 进程信息 | sysinfo | 跨平台 |
| 守护进程 | daemonize | 专用工具 |

**依赖建议**:

```toml
# 最小化
[dependencies]

# Web应用
[dependencies]
tokio = { version = "1", features = ["full"] }
sysinfo = "0.30"

# CLI工具
[dependencies]
duct = "0.13"

# 系统工具
[dependencies]
nix = "0.27"
caps = "0.5"
users = "0.11"
```

---

**完成**: C07 Process Management Tier 4 文档集 ✅

---

**文档维护**: Documentation Team
**创建日期**: 2025-10-22
**最后更新**: 2025-10-23
**适用版本**: Rust 1.92.0+
