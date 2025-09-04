# C07 Process Management Library

一个功能完整的 Rust 进程管理和 IPC 通信库，提供进程生命周期管理、进程间通信和同步原语等功能。

## 🚀 特性

- **进程管理**: 进程创建、监控、控制和生命周期管理
- **IPC 通信**: 命名管道、Unix 套接字、TCP 套接字、共享内存、消息队列
- **同步原语**: 互斥锁、读写锁、条件变量、信号量、屏障
- **跨平台**: 支持 Windows、Linux 和 macOS
- **类型安全**: 完整的 Rust 类型系统和错误处理
- **高性能**: 使用 Arc 和 Mutex 的并发安全设计

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

# 运行示例程序
cargo run --bin process_demo
cargo run --bin ipc_demo
cargo run --bin sync_demo
```

## 📚 API 文档

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

### IPC通信演示

```bash
cargo run --bin ipc_demo
```

演示各种IPC机制的使用，包括管道、套接字、共享内存等。

### 同步原语演示

```bash
cargo run --bin sync_demo
```

演示互斥锁、读写锁、条件变量、信号量和屏障的使用。

## 🤝 贡献

欢迎提交 Issue 和 Pull Request！

## 📄 许可证

本项目采用 MIT 许可证。

## 🔗 相关链接

- [Rust 官方文档](https://doc.rust-lang.org/)
- [Rust 异步编程](https://rust-lang.github.io/async-book/)
- [系统编程指南](https://doc.rust-lang.org/nomicon/)
