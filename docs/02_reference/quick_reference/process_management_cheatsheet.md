# 进程管理快速参考卡片

**模块**: C07 Process Management
**创建日期**: 2026-01-27
**最后更新**: 2026-01-27
**Rust 版本**: 1.93.0+ (Edition 2024)
**状态**: ✅ 已完成

---

## 📋 目录

- [进程管理快速参考卡片](#进程管理快速参考卡片)
  - [📋 目录](#-目录)
  - [🚀 快速开始](#-快速开始)
    - [基本使用](#基本使用)
  - [📋 常用 API](#-常用-api)
    - [进程管理](#进程管理)
    - [异步进程管理](#异步进程管理)
    - [IPC 通信](#ipc-通信)
    - [同步原语](#同步原语)
  - [🔧 配置选项](#-配置选项)
    - [ProcessConfig](#processconfig)
    - [跨平台注意事项](#跨平台注意事项)
  - [⚡ 性能优化](#-性能优化)
    - [启用性能监控](#启用性能监控)
  - [🐛 错误处理](#-错误处理)
  - [🚫 反例速查](#-反例速查)
    - [反例 1: 不检查子进程退出状态](#反例-1-不检查子进程退出状态)
    - [反例 2: 在 Unix 信号处理中调用非 async-signal-safe 函数](#反例-2-在-unix-信号处理中调用非-async-signal-safe-函数)
  - [📚 相关文档](#-相关文档)
  - [🧩 相关示例代码](#-相关示例代码)
  - [📚 相关资源](#-相关资源)
    - [官方文档](#官方文档)
    - [项目内部文档](#项目内部文档)
    - [相关速查卡](#相关速查卡)

---

## 🚀 快速开始

### 基本使用

```rust
use c07_process::prelude::*;

// 创建进程管理器
let mut manager = ProcessManager::new();

// 创建进程配置
let config = ProcessConfig {
    program: "echo".to_string(),
    args: vec!["Hello".to_string()],
    env: HashMap::new(),
    working_dir: None,
    user_id: None,
    group_id: None,
    priority: None,
    resource_limits: ResourceLimits::default(),
};

// 启动进程
let pid = manager.spawn(config)?;

// 获取进程信息
let info = manager.get_info(pid)?;

// 终止进程
manager.kill(pid)?;
```

---

## 📋 常用 API

### 进程管理

| 操作     | 方法            | 说明         |
| :--- | :--- | :--- || 创建进程 | `spawn(config)` | 启动新进程   |
| 获取信息 | `get_info(pid)` | 获取进程状态 |
| 终止进程 | `kill(pid)`     | 发送终止信号 |
| 等待进程 | `wait(pid)`     | 等待进程结束 |
| 列出所有 | `list_all()`    | 获取所有进程 |

### 异步进程管理

```rust
use c07_process::AsyncProcessManager;

let manager = AsyncProcessManager::new().await;

// 异步启动
let pid = manager.spawn(config).await?;

// 异步写入标准输入
manager.write_stdin(pid, b"data").await?;

// 异步读取标准输出
let output = manager.read_stdout(pid).await?;

// 带超时等待
manager.wait_with_timeout(pid, Duration::from_secs(5)).await?;
```

### IPC 通信

```rust
use c07_process::IpcManager;

let mut ipc = IpcManager::new(IpcConfig::default());

// 创建命名管道
let pipe = ipc.create_named_pipe("my_pipe")?;

// 创建共享内存
let memory = ipc.create_shared_memory("my_memory", 1024)?;

// 创建消息队列
let queue = ipc.create_message_queue("my_queue", 100)?;
```

### 同步原语

```rust
use c07_process::SyncManager;

let mut sync = SyncManager::new(SyncConfig::default());

// 创建互斥锁
let mutex = sync.create_mutex("my_mutex")?;

// 创建信号量
let semaphore = sync.create_semaphore("my_semaphore", 5)?;

// 创建读写锁
let rwlock = sync.create_rwlock("my_rwlock")?;
```

---

## 🔧 配置选项

### ProcessConfig

```rust
ProcessConfig {
    program: String,           // 程序路径
    args: Vec<String>,        // 命令行参数
    env: HashMap<String, String>, // 环境变量
    working_dir: Option<String>,  // 工作目录
    user_id: Option<u32>,     // 用户ID (Unix)
    group_id: Option<u32>,    // 组ID (Unix)
    priority: Option<i32>,    // 优先级
    resource_limits: ResourceLimits, // 资源限制
}
```

### 跨平台注意事项

**Windows**:

- 使用 `cmd /c` 适配命令
- `working_dir` 设为 `.`
- `PATH` 包含 `C:\\Windows\\System32`

**Linux/macOS**:

- 直接使用命令名
- `working_dir` 设为 `/tmp` 或当前目录

---

## ⚡ 性能优化

### 启用性能监控

```rust
use c07_process::performance::enhanced::*;

let config = PerformanceConfig {
    memory_threshold: 0.8,
    cpu_threshold: 0.7,
    auto_optimization: true,
    ..Default::default()
};

let manager = EnhancedPerformanceManager::new(config).await;

// 执行优化
let result = manager.optimize_memory().await;
```

---

## 🐛 错误处理

```rust
use c07_process::error::ProcessError;

match manager.spawn(config) {
    Ok(pid) => println!("进程启动: {}", pid),
    Err(ProcessError::NotFound(_)) => println!("进程不存在"),
    Err(ProcessError::PermissionDenied) => println!("权限不足"),
    Err(e) => println!("其他错误: {}", e),
}
```

---

## 🚫 反例速查

### 反例 1: 不检查子进程退出状态

**错误示例**:

```rust
let mut child = Command::new("cat").arg("file").spawn()?;
// 不调用 wait() 可能导致僵尸进程
```

**原因**: 未 wait 时子进程可能变成僵尸。

**修正**:

```rust
let status = child.wait()?;
assert!(status.success());
```

---

### 反例 2: 在 Unix 信号处理中调用非 async-signal-safe 函数

**错误示例**:

```rust
fn handler(_: i32) {
    println!("signal");  // ❌ 在信号处理中 unsafe
}
```

**原因**: 信号处理函数中只能调用 async-signal-safe 函数。

**修正**: 仅设置原子标志，在主循环中处理；或使用 `signal-hook` 等库。

---

## 📚 相关文档

- [进程管理完整文档](../../../crates/c07_process/docs/)
- [进程管理 README](../../../crates/c07_process/README.md)

## 🧩 相关示例代码

以下示例位于 `crates/c07_process/examples/`，可直接运行（例如：`cargo run -p c07_process --example process_management_demo`）。

- [进程管理演示](../../../crates/c07_process/examples/process_management_demo.rs)
- [异步进程与 IPC](../../../crates/c07_process/examples/async_process_demo.rs)、[ipc_communication_demo.rs](../../../crates/c07_process/examples/ipc_communication_demo.rs)
- [信号处理与进程组](../../../crates/c07_process/examples/signal_handling_demo.rs)、[process_group_demo.rs](../../../crates/c07_process/examples/process_group_demo.rs)
- [进程监控与性能优化](../../../crates/c07_process/examples/process_monitoring_demo.rs)、[performance_optimization_demo.rs](../../../crates/c07_process/examples/performance_optimization_demo.rs)
- [跨平台演示](../../../crates/c07_process/examples/cross_platform_demo.rs)

---

## 📚 相关资源

### 官方文档

- [std::process 文档](https://doc.rust-lang.org/std/process/)
- [std::io 文档](https://doc.rust-lang.org/std/io/)

### 项目内部文档

- [完整文档](../../../crates/c07_process/README.md)
- [异步IO指南](../../../crates/c07_process/docs/async_stdio_guide.md)
- [性能优化指南](../../../crates/c07_process/docs/performance_optimization_usage_guide.md)

### 相关速查卡

- [异步编程速查卡](./async_patterns.md) - 异步进程管理
- [错误处理速查卡](./error_handling_cheatsheet.md) - 进程错误处理
- [线程与并发速查卡](./threads_concurrency_cheatsheet.md) - 进程与线程

---

**最后更新**: 2026-01-27
**Rust 版本**: 1.93.0+ (Edition 2024)
**提示**: 使用 `cargo doc --open` 查看完整 API 文档
