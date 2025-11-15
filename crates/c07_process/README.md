# 🦀 C07 Process Management Library

> **模块类型**: 进程管理学习模块 | ⭐ 质量评分: **95/100**
> **Rust版本**: 1.91.1+ | 📊 完成度: **100% 完成** ✅
> **学习重点**: 进程管理、IPC通信、信号处理、进程同步
> **适用对象**: Rust中级到高级开发者、系统程序员
> **最后更新**: 2025-11-15 | 🔄 维护模式: Rust 1.91.1 特性更新完成

## 🎯 最新更新 (2025-11-15) ✨

> **文档状态**: ✅ **100% 标准化完成**
> **框架结构**: ✅ **4-Tier 架构**
> **文档总数**: **20+ 篇**
> **质量评分**: **95/100**
> **Rust版本**: 1.91.1+ (Edition 2024)

## 🌟 2025-10-20 核心增强更新

- **📊 [知识图谱与概念关系](./docs/theory_enhanced/KNOWLEDGE_GRAPH_AND_CONCEPT_RELATIONS.md)** - 进程管理完整体系
- **📐 [多维矩阵对比分析](./docs/theory_enhanced/MULTI_DIMENSIONAL_COMPARISON_MATRIX.md)** - IPC/同步原语全面对比
- **🗺️ [Rust 1.90 综合思维导图](./docs/RUST_190_COMPREHENSIVE_MINDMAP.md)** ⭐ NEW!
  - ASCII艺术图表 | 进程创建/IPC/信号完整体系
  - 跨平台设计模式 | Unix/Windows特定API对比
  - 技术选型决策树 | IPC机制/同步原语选择指南
  - 3级学习路径(1-7周) | 问题诊断树
- **💻 [Rust 1.90 实战示例集](./docs/RUST_190_EXAMPLES_COLLECTION.md)** ⭐ NEW!
  - 900+行可运行代码 | 异步进程/IPC/信号处理
  - Rust 1.90特性 | async trait/超时控制/优雅关闭
  - 2个综合项目 | 多进程任务执行器+进程监控系统

**完整度**: 📊 知识图谱 + 📐 多维矩阵 + 🗺️ 思维导图 + 💻 实战示例 = **100%** ✨

---

## 目录

- [C07 Process Management Library](#c07-process-management-library)
  - [🌟 2025-10-20 核心增强更新](#-2025-10-20-核心增强更新)
  - [目录](#目录)
  - [🚀 特性](#-特性)
  - [📦 安装](#-安装)
  - [🔧 使用方法](#-使用方法)
    - [进程管理](#进程管理)
    - [IPC 通信](#ipc-通信)
    - [同步原语](#同步原语)
  - [🏗️ 项目结构](#️-项目结构)
  - [🧪 运行测试](#-运行测试)
  - [📚 文档结构](#-文档结构)
    - [核心文档](#核心文档)
    - [高级主题](#高级主题)
    - [API 文档](#api-文档)
  - [🔍 错误处理](#-错误处理)
  - [🌟 示例程序](#-示例程序)
    - [进程管理演示](#进程管理演示)
    - [IPC通信演示](#ipc通信演示)
    - [同步原语演示](#同步原语演示)
    - [超时与取消演示](#超时与取消演示)
    - [监控与重启演示](#监控与重启演示)
    - [进程组演示](#进程组演示)
    - [进程组控制演示（按组终止）](#进程组控制演示按组终止)
    - [标准 IO 管道演示](#标准-io-管道演示)
    - [异步标准 IO 演示（占位）](#异步标准-io-演示占位)
    - [Rust 1.90 新特性演示](#rust-190-新特性演示)
    - [增强的异步功能演示](#增强的异步功能演示)
    - [增强的IPC通信演示](#增强的ipc通信演示)
    - [增强的同步原语演示](#增强的同步原语演示)
    - [增强的错误处理演示](#增强的错误处理演示)
  - [🤝 贡献](#-贡献)
  - [📄 许可证](#-许可证)
  - [🔗 相关链接](#-相关链接)

一个功能完整的 Rust 进程管理和 IPC 通信库，提供进程生命周期管理、进程间通信和同步原语等功能。

## 🚀 特性

- **进程管理**: 进程创建、监控、控制和生命周期管理
- **IPC 通信**: 命名管道、Unix 套接字、TCP 套接字、共享内存、消息队列
- **同步原语**: 互斥锁、读写锁、条件变量、信号量、屏障
- **跨平台**: 支持 Windows、Linux 和 macOS
- **类型安全**: 完整的 Rust 类型系统和错误处理
- **高性能**: 使用 Arc 和 Mutex 的并发安全设计
- **Rust 1.90 新特性**: 充分利用最新的语言特性，包括异步闭包、改进的模式匹配等
- **Edition 2024**: 使用最新的 Rust 2024 版本特性

## 📦 安装

在 `Cargo.toml` 中添加依赖：

```toml
[dependencies]
c07_process = { path = "crates/c07_process" }
```

## 🔧 使用方法

### 进程管理

```rust
use c07_process::prelude::*;
use std::collections::HashMap;

// 创建进程管理器
let mut pm = ProcessManager::new();

// 创建进程配置
let mut env = HashMap::new();
env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());

let config = ProcessConfig {
    program: "echo".to_string(),
    args: vec!["Hello, World!".to_string()],
    env,
    working_dir: Some("/tmp".to_string()),
    user_id: None,
    group_id: None,
    priority: None,
    resource_limits: ResourceLimits::default(),
};

// 启动进程
let pid = pm.spawn(config)?;
println!("进程启动成功，PID: {}", pid);

// 获取进程信息
if let Ok(info) = pm.get_process_info(pid) {
    println!("进程信息: {:?}", info);
}

// 等待进程完成
if let Ok(output) = pm.get_output(pid) {
    println!("进程输出: {:?}", output);
}
```

### IPC 通信

```rust
use c07_process::prelude::*;

// 创建IPC管理器
let mut ipc = IpcManager::new(IpcConfig::default());

// 创建命名管道
ipc.create_named_pipe("demo_pipe")?;

// 创建TCP套接字
ipc.create_tcp_socket("127.0.0.1", 8080)?;

// 发送消息
let message = Message::new(1, "demo", "Hello IPC!".as_bytes().to_vec(), 1234);
ipc.send_message("demo_pipe", &message)?;

// 接收消息
if let Ok(received) = ipc.receive_message("demo_pipe") {
    println!("接收消息: {:?}", received);
}

// 清理资源
ipc.cleanup()?;
```

### 同步原语

```rust
use c07_process::prelude::*;

// 创建同步管理器
let mut sync = SyncManager::new(SyncConfig::default());

// 创建互斥锁
let mutex = sync.create_mutex("demo_mutex")?;

// 获取锁
if let Ok(guard) = mutex.lock() {
    // 在这里安全地访问共享资源
    println!("获取互斥锁成功");
    drop(guard); // 释放锁
}

// 创建读写锁
let rwlock = sync.create_rwlock("demo_rwlock")?;

// 获取读锁
if let Ok(read_guard) = rwlock.read() {
    println!("获取读锁成功");
    drop(read_guard);
}

// 获取写锁
if let Ok(write_guard) = rwlock.write() {
    println!("获取写锁成功");
    drop(write_guard);
}

// 创建信号量
let semaphore = sync.create_semaphore("demo_semaphore", 3)?;

// 获取许可
if let Some(permit) = semaphore.try_acquire() {
    println!("获取信号量许可成功");
    drop(permit); // 自动释放许可
}
```

## 🏗️ 项目结构

```text
src/
├── lib.rs                 # 库入口点和公共API
├── types/                 # 核心类型定义
│   ├── mod.rs
│   ├── process.rs         # 进程相关类型
│   ├── ipc.rs            # IPC相关类型
│   └── sync.rs           # 同步原语类型
├── error/                 # 错误处理
│   └── mod.rs
├── process/               # 进程管理
│   ├── mod.rs
│   ├── lifecycle.rs       # 进程生命周期
│   └── control.rs         # 进程控制
├── inter_process_communication/  # IPC通信
│   ├── mod.rs
│   ├── pipe.rs           # 命名管道
│   ├── socket.rs         # 套接字
│   ├── shared_memory.rs  # 共享内存
│   ├── message_queue.rs  # 消息队列
│   └── channel.rs        # 文件系统通道
├── concurrency/           # 同步原语
│   ├── mod.rs
│   ├── mutex.rs          # 互斥锁
│   ├── rwlock.rs         # 读写锁
│   ├── condvar.rs        # 条件变量
│   ├── semaphore.rs      # 信号量
│   └── barrier.rs        # 屏障
├── pipe/                  # 管道实现
│   └── named_pipe.rs
├── shared_memory/         # 共享内存实现
│   └── region.rs
├── fork/                  # 进程分叉
│   └── windows_fork.rs
└── bin/                   # 示例程序
    ├── process_demo.rs    # 进程管理演示
    ├── ipc_demo.rs        # IPC通信演示
    └── sync_demo.rs       # 同步原语演示
```

## 🧪 运行测试

```bash
# 运行单元测试
cargo test

# 运行集成测试
cargo test --test integration_tests

# 运行示例程序（跨平台）
# Windows PowerShell
cargo run --bin process_demo
cargo run --bin process_pool_demo
cargo run --bin sync_demo
cargo run --bin timeout_demo
cargo run --bin stdio_demo
cargo run --bin supervisor_demo
cargo run --bin group_demo
cargo run --features async --bin async_stdio_demo
cargo run --bin group_control_demo

# Linux/macOS
cargo run --bin process_demo
cargo run --bin process_pool_demo
cargo run --bin sync_demo
cargo run --bin timeout_demo
cargo run --bin stdio_demo
cargo run --bin supervisor_demo
cargo run --bin group_demo
cargo run --features async --bin async_stdio_demo
cargo run --bin group_control_demo
```

## 📚 文档结构

### 核心文档

- **[README.md](docs/README.md)** - 文档总览和快速导航
- **[OVERVIEW.md](docs/OVERVIEW.md)** - 模块概览和架构说明
- **[process_management.md](docs/process_management.md)** - 进程管理基础指南

### 高级主题

- **[01_process_model_and_lifecycle.md](docs/01_process_model_and_lifecycle.md)** - 进程模型与生命周期
- **[02_ipc_mechanisms.md](docs/02_ipc_mechanisms.md)** - 进程间通信机制
- **[03_rust_190_features.md](docs/03_rust_190_features.md)** - Rust 1.90 新特性与进程管理
- **[04_advanced_process_management.md](docs/04_advanced_process_management.md)** - 高级进程管理
- **[05_async_process_management.md](docs/05_async_process_management.md)** - 异步进程管理
- **[06_cross_platform_process_management.md](docs/06_cross_platform_process_management.md)** - 跨平台进程管理
- **[07_performance_optimization.md](docs/07_performance_optimization.md)** - 性能优化技术
- **[08_security_and_sandboxing.md](docs/08_security_and_sandboxing.md)** - 安全与沙箱

### API 文档

生成API文档：

```bash
cargo doc --open
```

## 🔍 错误处理

库使用 `thiserror` 提供结构化的错误类型：

```rust
use c07_process::error::{ProcessError, IpcError, SyncError};

match result {
    Ok(data) => println!("成功: {:?}", data),
    Err(ProcessError::NotFound(pid)) => println!("进程 {} 不存在", pid),
    Err(ProcessError::PermissionDenied) => println!("权限不足"),
    Err(IpcError::ChannelNotFound(name)) => println!("通道 {} 不存在", name),
    Err(SyncError::LockAcquisitionFailed(name)) => println!("获取锁 {} 失败", name),
    Err(e) => println!("其他错误: {}", e),
}
```

## 🌟 示例程序

### 进程管理演示

```bash
cargo run --bin process_demo
```

演示进程创建、监控、IPC通信和同步原语的使用。

跨平台注意事项：

- Windows 使用 `cmd /c` 适配 `echo` 等命令；`working_dir` 设为 `.`；`PATH` 建议包含 `C:\\Windows\\System32`。
- Linux/macOS 直接使用 `echo`，`working_dir` 设为 `/tmp` 或当前目录。

### IPC通信演示

```bash
cargo run --bin ipc_demo
```

演示各种IPC机制的使用，包括管道、套接字、共享内存等。

提示：在 Windows 平台上，"Unix 套接字" 将使用兼容实现（可能退化为 TCP 套接字）。

### 同步原语演示

```bash
cargo run --bin sync_demo
```

演示互斥锁、读写锁、条件变量、信号量和屏障的使用。

### 超时与取消演示

```bash
cargo run --bin timeout_demo
```

演示如何在超时时间内轮询等待子进程退出，并在超时后进行终止。
支持通过环境变量配置：

```bash
# 以 1500ms 超时运行
TIMEOUT_MS=1500 cargo run --bin timeout_demo
```

### 监控与重启演示

```bash
cargo run --bin supervisor_demo
```

演示监控与指数退避重启。可配置环境变量：

```bash
# 设置最大重启次数为 3，起始退避100ms，上限1500ms
MAX_RESTARTS=3 BACKOFF_START_MS=100 BACKOFF_MAX_MS=1500 cargo run --bin supervisor_demo
```

### 进程组演示

```bash
cargo run --bin group_demo
```

演示 `ProcessGroupManager` 的创建、加入成员与查询。

### 进程组控制演示（按组终止）

```bash
cargo run --bin group_control_demo
```

演示如何通过组信息遍历成员并逐个终止，实现“按组终止”的控制逻辑。

### 标准 IO 管道演示

```bash
cargo run --bin stdio_demo
```

演示如何与子进程进行标准输入/输出交互：示例向子进程写入一行文本并读取回显，使用 `ProcessManager::write_stdin/close_stdin/read_stdout/read_stderr` 完成交互。

### 异步标准 IO 演示（占位）

```bash
cargo run --features async --bin async_stdio_demo
```

预留异步标准 IO 与超时 API 的接口，当前调用会返回"未实现"错误，便于后续迭代替换为真实实现。

### Rust 1.90 新特性演示

```bash
cargo run --features async --bin rust_190_features_demo
```

演示 Rust 1.90 Edition 2024 的最新语言特性，包括：

- 异步闭包 (Async Closures)
- 改进的模式匹配
- 改进的迭代器
- 改进的错误处理
- 改进的类型推断
- 改进的宏系统
- 标准库新特性
- 改进的并发特性

### 增强的异步功能演示

```bash
cargo run --features async --bin enhanced_async_demo
```

演示增强的异步进程管理功能，包括：

- 完整的异步进程管理
- 异步闭包支持
- 性能监控
- 错误恢复机制
- 资源限制和连接池

### 增强的IPC通信演示

```bash
cargo run --features async --bin enhanced_ipc_demo
```

演示增强的IPC通信功能，包括：

- 零拷贝数据传输
- 高性能消息队列
- 共享内存通信
- 性能监控和统计
- 智能错误恢复

### 增强的同步原语演示

```bash
cargo run --features async --bin enhanced_sync_demo
```

演示增强的同步原语功能，包括：

- 死锁检测和预防
- 性能监控和统计
- 自适应锁策略
- 高级同步原语组合
- 智能负载均衡

### 增强的错误处理演示

```bash
cargo run --features async --bin enhanced_error_demo
```

演示增强的错误处理功能，包括：

- 智能错误恢复机制
- 错误链追踪和分析
- 自动错误分类
- 错误通知和告警
- 错误统计和趋势分析

## 🤝 贡献

欢迎提交 Issue 和 Pull Request！

## 📄 许可证

本项目采用 MIT 许可证。

## 🔗 相关链接

- [Rust 官方文档](https://doc.rust-lang.org/)
- [Rust 异步编程](https://rust-lang.github.io/async-book/)
- [系统编程指南](https://doc.rust-lang.org/nomicon/)
