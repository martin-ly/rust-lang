# C07 进程管理: 常见问题解答 (FAQ)

> **文档定位**: 进程管理常见问题快速解答，涵盖进程生命周期、IPC通信、跨平台等核心疑问
> **使用方式**: 通过问题索引快速定位问题，获取详细答案和示例
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [README](./README.md) | [Glossary](./Glossary.md)

## 📊 目录

- [C07 进程管理: 常见问题解答 (FAQ)](#c07-进程管理-常见问题解答-faq)
  - [📊 目录](#-目录)
  - [问答详解](#问答详解)
    - [Q1: 如何创建和管理子进程？](#q1-如何创建和管理子进程)
    - [Q2: 进程间如何通信？最好的方式是什么？](#q2-进程间如何通信最好的方式是什么)
    - [Q3: 如何实现跨平台的进程管理？](#q3-如何实现跨平台的进程管理)
    - [Q4: 如何避免和处理僵尸进程？](#q4-如何避免和处理僵尸进程)
    - [Q5: 什么时候应该使用异步进程管理？](#q5-什么时候应该使用异步进程管理)
  - [📚 延伸阅读](#-延伸阅读)

**最后更新**: 2025-12-25
**适用版本**: Rust 1.92.0+ (Edition 2024)
**文档类型**: ❓ 问答手册

---

## 问答详解

### Q1: 如何创建和管理子进程？

**A1**:

Rust的`std::process::Command`提供了创建和管理子进程的标准方式：

```rust
use std::process::Command;

// 创建子进程
let output = Command::new("ls")
    .arg("-la")
    .output()
    .expect("failed to execute process");

println!("status: {}", output.status);
println!("stdout: {}", String::from_utf8_lossy(&output.stdout));
```

**核心方法**:

- `spawn()` - 启动进程，立即返回
- `output()` - 等待进程完成，获取输出
- `status()` - 只获取退出状态
- `stdin()`/`stdout()`/`stderr()` - 配置标准I/O

**相关**: [01_process_model_and_lifecycle](./01_process_model_and_lifecycle.md)

---

### Q2: 进程间如何通信？最好的方式是什么？

**A2**:

Rust支持多种IPC机制，选择取决于具体需求：

**1. 管道 (Pipe)** - 简单、父子进程

```rust
use std::process::{Command, Stdio};

let child = Command::new("cat")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .spawn()?;
```

**2. 通道 (Channel)** - 线程间通信

```rust
use std::sync::mpsc::channel;

let (tx, rx) = channel();
// 在不同进程的线程间通信
```

**3. 共享内存** - 高性能、大数据量

- 使用`shared_memory` crate
- 适合高吞吐量场景

**4. Socket** - 网络通信、分布式

- TCP/UDP
- Unix Domain Socket

**选择建议**:

- **简单场景**: 管道
- **高性能**: 共享内存
- **灵活性**: Socket
- **跨网络**: TCP/IP

**相关**: [02_ipc_mechanisms](./02_ipc_mechanisms.md) | [13_ipc_communication_advanced](./11_practical_examples/13_ipc_communication_advanced.md)

---

### Q3: 如何实现跨平台的进程管理？

**A3**:

跨平台进程管理的关键是处理Unix和Windows的差异：

**核心差异**:

| 特性         | Unix/Linux             | Windows        |
| :--- | :--- | :--- || **进程创建** | fork/exec              | CreateProcess  |
| **信号**     | SIGTERM, SIGKILL       | 不支持         |
| **进程组**   | 进程组ID               | 作业对象       |
| **IPC**      | 管道、Socket、共享内存 | 命名管道、邮槽 |

**Rust解决方案**:

```rust
#[cfg(unix)]
use std::os::unix::process::CommandExt;

#[cfg(windows)]
use std::os::windows::process::CommandExt;

let mut cmd = Command::new("my_app");

#[cfg(unix)]
{
    // Unix特定配置
    cmd.process_group(0);
}

#[cfg(windows)]
{
    // Windows特定配置
    use std::os::windows::process::CommandExt;
    cmd.creation_flags(0x08000000); // CREATE_NO_WINDOW
}
```

**推荐库**:

- `nix` - Unix系统调用封装
- `winapi` - Windows API封装
- `tokio` - 异步跨平台进程管理

**相关**: [06_cross_platform_process_management](./06_cross_platform_process_management.md) | [10_cross_platform_guide](./10_cross_platform_guide.md)

---

### Q4: 如何避免和处理僵尸进程？

**A4**:

僵尸进程是已终止但父进程未读取其退出状态的进程。

**产生原因**:

- 父进程创建子进程后未调用`wait()`
- 父进程提前退出
- 异常情况未处理

**Rust解决方案**:

```rust
use std::process::Command;

// 方法1: 使用output()自动等待
let output = Command::new("child").output()?;

// 方法2: 手动wait()
let mut child = Command::new("child").spawn()?;
let status = child.wait()?; // 回收子进程

// 方法3: 使用try_wait()非阻塞检查
loop {
    match child.try_wait() {
        Ok(Some(status)) => {
            println!("子进程退出: {}", status);
            break;
        }
        Ok(None) => {
            // 仍在运行
        }
        Err(e) => eprintln!("错误: {}", e),
    }
}

// 方法4: 信号处理(Unix)
#[cfg(unix)]
{
    use nix::sys::signal::{signal, SigHandler, Signal};
    unsafe {
        signal(Signal::SIGCHLD, SigHandler::SigIgn)?;
    }
}
```

**最佳实践**:

- ✅ 始终调用`wait()`或`output()`
- ✅ 使用RAII模式确保清理
- ✅ 在`Drop`实现中kill和wait
- ⚠️ 注意信号处理(Unix)

**相关**: [01_process_model_and_lifecycle](./01_process_model_and_lifecycle.md)

---

### Q5: 什么时候应该使用异步进程管理？

**A5**:

异步进程管理适合需要同时管理多个进程的场景。

**适合异步的场景**:

- ✅ 同时管理多个子进程
- ✅ 进程I/O密集型操作
- ✅ 需要超时控制
- ✅ 与其他异步操作协同

**Tokio示例**:

```rust
use tokio::process::Command;
use tokio::time::{timeout, Duration};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 并发启动多个进程
    let tasks = vec![
        tokio::spawn(run_process("process1")),
        tokio::spawn(run_process("process2")),
        tokio::spawn(run_process("process3")),
    ];

    // 等待所有进程完成
    for task in tasks {
        task.await??;
    }

    Ok(())
}

async fn run_process(name: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 带超时的进程执行
    let result = timeout(
        Duration::from_secs(30),
        Command::new(name).output()
    ).await??;

    println!("{} 完成: {:?}", name, result.status);
    Ok(())
}
```

**优势**:

- 高效的并发处理
- 轻量级任务切换
- 统一的async/await语法
- 与异步生态集成

**不适合异步**:

- ❌ 单个进程简单执行
- ❌ CPU密集型任务
- ❌ 需要实时保证的场景

**相关**: [05_async_process_management](./05_async_process_management.md)

---

## 📚 延伸阅读

- [01_process_model_and_lifecycle](./01_process_model_and_lifecycle.md) - 进程模型基础
- [02_ipc_mechanisms](./02_ipc_mechanisms.md) - IPC通信机制
- [05_async_process_management](./05_async_process_management.md) - 异步进程管理
- [06_cross_platform_process_management](./06_cross_platform_process_management.md) - 跨平台实现
- [主索引](./00_MASTER_INDEX.md) - 返回主索引
