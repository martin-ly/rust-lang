# C07 Process - 异步标准 IO 使用指南

> **创建日期**: 2025-12-11
> **最后更新**: 2025-12-11
> **适用版本**: Rust 1.92.0+ | Edition 2024
> **功能状态**: ✅ 完全实现

---

## 📋 概述

本指南介绍如何使用 C07 Process 模块的异步标准 IO 接口。这些接口允许您异步地写入进程的标准输入、读取标准输出和标准错误，以及等待进程完成。

---

## 🚀 快速开始

### 启用异步功能

在 `Cargo.toml` 中启用 `async` feature：

```toml
[dependencies]
c07_process = { path = "crates/c07_process", features = ["async"] }
tokio = { version = "1.0", features = ["full"] }
```

### 基本使用示例

```rust
use c07_process::AsyncProcessManager;
use c07_process::prelude::*;
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<()> {
    // 创建异步进程管理器
    let manager = AsyncProcessManager::new().await;

    // 配置进程
    let mut env = HashMap::new();
    env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());

    let config = ProcessConfig {
        program: "echo".to_string(),
        args: vec!["hello".to_string()],
        env,
        working_dir: Some(".".to_string()),
        user_id: None,
        group_id: None,
        priority: None,
        resource_limits: ResourceLimits::default(),
    };

    // 启动进程
    let pid = manager.spawn(config).await?;
    println!("✅ 启动进程，PID: {}", pid);

    // 等待进程输出
    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    // 读取标准输出
    let output = manager.read_stdout(pid).await?;
    let output_str = String::from_utf8_lossy(&output);
    println!("标准输出: {}", output_str);

    Ok(())
}
```

---

## 📚 API 参考

### `AsyncProcessManager`

#### `new() -> Self`

创建新的异步进程管理器。

```rust
let manager = AsyncProcessManager::new().await;
```

#### `spawn(config: ProcessConfig) -> ProcessResult<u32>`

异步启动进程。

**参数:**

- `config`: 进程配置（程序路径、参数、环境变量等）

**返回:**

- `Ok(pid)`: 成功启动，返回进程 ID
- `Err(e)`: 启动失败，返回错误

**示例:**

```rust
let pid = manager.spawn(config).await?;
```

#### `write_stdin(pid: u32, data: &[u8]) -> ProcessResult<()>`

异步写入进程的标准输入。

**参数:**

- `pid`: 进程 ID
- `data`: 要写入的数据

**返回:**

- `Ok(())`: 写入成功
- `Err(e)`: 写入失败

**示例:**

```rust
manager.write_stdin(pid, b"hello world\n").await?;
```

#### `close_stdin(pid: u32) -> ProcessResult<()>`

关闭进程的标准输入（EOF）。

**参数:**

- `pid`: 进程 ID

**返回:**

- `Ok(())`: 关闭成功
- `Err(e)`: 关闭失败

**示例:**

```rust
manager.close_stdin(pid).await?;
```

#### `read_stdout(pid: u32) -> ProcessResult<Vec<u8>>`

异步读取进程的标准输出。

**参数:**

- `pid`: 进程 ID

**返回:**

- `Ok(data)`: 成功读取，返回输出数据
- `Err(e)`: 读取失败

**示例:**

```rust
let output = manager.read_stdout(pid).await?;
let output_str = String::from_utf8_lossy(&output);
println!("输出: {}", output_str);
```

#### `read_stderr(pid: u32) -> ProcessResult<Vec<u8>>`

异步读取进程的标准错误。

**参数:**

- `pid`: 进程 ID

**返回:**

- `Ok(data)`: 成功读取，返回错误输出数据
- `Err(e)`: 读取失败

**示例:**

```rust
let error = manager.read_stderr(pid).await?;
if !error.is_empty() {
    let error_str = String::from_utf8_lossy(&error);
    eprintln!("错误: {}", error_str);
}
```

#### `wait_with_timeout(pid: u32, timeout: Duration) -> ProcessResult<Option<ExitStatus>>`

带超时的等待进程完成。

**参数:**

- `pid`: 进程 ID
- `timeout`: 超时时间

**返回:**

- `Ok(Some(status))`: 进程在超时前完成，返回退出状态
- `Ok(None)`: 超时，进程仍在运行
- `Err(e)`: 等待失败

**示例:**

```rust
use std::time::Duration;

match manager.wait_with_timeout(pid, Duration::from_secs(5)).await? {
    Some(status) => println!("进程完成，退出码: {:?}", status.code()),
    None => println!("进程超时，仍在运行"),
}
```

#### `kill(pid: u32) -> ProcessResult<()>`

异步终止进程。

**参数:**

- `pid`: 进程 ID

**返回:**

- `Ok(())`: 终止成功
- `Err(e)`: 终止失败

**示例:**

```rust
manager.kill(pid).await?;
```

#### `get_info(pid: u32) -> ProcessResult<ProcessInfo>`

获取进程信息。

**参数:**

- `pid`: 进程 ID

**返回:**

- `Ok(info)`: 成功获取进程信息
- `Err(e)`: 获取失败（进程不存在）

**示例:**

```rust
let info = manager.get_info(pid).await?;
println!("进程名称: {}", info.name);
println!("进程状态: {:?}", info.status);
```

#### `list_all() -> Vec<ProcessInfo>`

列出所有管理的进程。

**返回:**

- `Vec<ProcessInfo>`: 所有进程的信息列表

**示例:**

```rust
let processes = manager.list_all().await;
for process in processes {
    println!("PID: {}, 名称: {}", process.pid, process.name);
}
```

---

## 💡 完整示例

### 示例 1: 与交互式进程通信

```rust
use c07_process::AsyncProcessManager;
use c07_process::prelude::*;
use std::collections::HashMap;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<()> {
    let manager = AsyncProcessManager::new().await;

    // 启动一个交互式进程（示例：cat 命令）
    let mut env = HashMap::new();
    env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());

    let config = ProcessConfig {
        program: "cat".to_string(),
        args: vec![],
        env,
        working_dir: Some(".".to_string()),
        user_id: None,
        group_id: None,
        priority: None,
        resource_limits: ResourceLimits::default(),
    };

    let pid = manager.spawn(config).await?;

    // 写入数据到标准输入
    manager.write_stdin(pid, b"Hello\n").await?;
    manager.write_stdin(pid, b"World\n").await?;

    // 关闭标准输入（发送 EOF）
    manager.close_stdin(pid).await?;

    // 等待进程完成
    tokio::time::sleep(Duration::from_millis(100)).await;

    // 读取输出
    let output = manager.read_stdout(pid).await?;
    let output_str = String::from_utf8_lossy(&output);
    println!("进程输出:\n{}", output_str);

    Ok(())
}
```

### 示例 2: 监控长时间运行的进程

```rust
use c07_process::AsyncProcessManager;
use c07_process::prelude::*;
use std::collections::HashMap;
use std::time::Duration;

#[tokio::main]
async fn main() -> Result<()> {
    let manager = AsyncProcessManager::new().await;

    let mut env = HashMap::new();
    env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());

    let config = ProcessConfig {
        program: "sleep".to_string(),
        args: vec!["10".to_string()],  // 运行 10 秒
        env,
        working_dir: Some(".".to_string()),
        user_id: None,
        group_id: None,
        priority: None,
        resource_limits: ResourceLimits::default(),
    };

    let pid = manager.spawn(config).await?;
    println!("启动长时间运行的进程，PID: {}", pid);

    // 使用超时等待
    match manager.wait_with_timeout(pid, Duration::from_secs(5)).await? {
        Some(status) => {
            println!("进程在超时前完成，退出码: {:?}", status.code());
        }
        None => {
            println!("进程超时，仍在运行，终止它");
            manager.kill(pid).await?;
        }
    }

    Ok(())
}
```

### 示例 3: 跨平台兼容示例

```rust
use c07_process::AsyncProcessManager;
use c07_process::prelude::*;
use std::collections::HashMap;

#[tokio::main]
async fn main() -> Result<()> {
    let manager = AsyncProcessManager::new().await;

    let mut env = HashMap::new();

    // 跨平台环境变量设置
    if cfg!(windows) {
        env.insert("PATH".to_string(), "C:\\Windows\\System32".to_string());
    } else {
        env.insert("PATH".to_string(), "/usr/bin:/bin".to_string());
    }

    // 跨平台命令配置
    let config = if cfg!(windows) {
        ProcessConfig {
            program: "cmd".to_string(),
            args: vec!["/c".to_string(), "echo Hello from Windows".to_string()],
            env,
            working_dir: Some(".".to_string()),
            user_id: None,
            group_id: None,
            priority: None,
            resource_limits: ResourceLimits::default(),
        }
    } else {
        ProcessConfig {
            program: "echo".to_string(),
            args: vec!["Hello from Unix".to_string()],
            env,
            working_dir: Some(".".to_string()),
            user_id: None,
            group_id: None,
            priority: None,
            resource_limits: ResourceLimits::default(),
        }
    };

    let pid = manager.spawn(config).await?;

    tokio::time::sleep(tokio::time::Duration::from_millis(100)).await;

    let output = manager.read_stdout(pid).await?;
    let output_str = String::from_utf8_lossy(&output);
    println!("{}", output_str);

    Ok(())
}
```

---

## ⚠️ 注意事项

1. **进程生命周期**: 确保在进程退出后不要尝试读取或写入。使用 `wait_with_timeout` 来检查进程状态。

2. **标准输入关闭**: 对于某些进程（如 `cat`），必须在写入完所有数据后关闭标准输入（发送 EOF），进程才会完成。

3. **超时处理**: 长时间运行的进程应该使用 `wait_with_timeout` 设置超时，避免无限期等待。

4. **错误处理**: 所有 IO 操作都可能失败，务必处理错误情况。

5. **跨平台兼容性**: Windows 和 Unix 系统的命令和参数可能不同，使用条件编译确保跨平台兼容性。

---

## 🔗 相关文档

- [C07 Process README](../README.md) - 主模块文档
- [异步进程管理文档](./05_async_process_management.md) - 异步进程管理详细文档
- [错误处理指南](../docs/error_handling.md) - 错误处理最佳实践

---

**最后更新**: 2025-12-11
**维护者**: C07 Process 团队
