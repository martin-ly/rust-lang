# C07 进程管理: 术语表 (Glossary)

> **文档定位**: 进程管理核心术语快速参考，涵盖进程、IPC、信号等关键概念
> **使用方式**: 通过术语索引快速查找定义，理解进程管理核心概念
> **相关文档**: [主索引](./00_MASTER_INDEX.md) | [README](./README.md) | [FAQ](./FAQ.md)

## 📊 目录

- [C07 进程管理: 术语表 (Glossary)](#c07-进程管理-术语表-glossary)
  - [📊 目录](#-目录)
  - [📋 术语索引](#-术语索引)
  - [术语详解](#术语详解)
    - [进程 (Process)](#进程-process)
    - [Fork](#fork)
    - [Exec](#exec)
    - [IPC (Inter-Process Communication)](#ipc-inter-process-communication)
    - [管道 (Pipe)](#管道-pipe)
    - [共享内存 (Shared Memory)](#共享内存-shared-memory)
    - [信号 (Signal)](#信号-signal)
    - [僵尸进程 (Zombie Process)](#僵尸进程-zombie-process)
    - [孤儿进程 (Orphan Process)](#孤儿进程-orphan-process)
    - [进程组 (Process Group)](#进程组-process-group)
    - [守护进程 (Daemon)](#守护进程-daemon)
    - [文件描述符 (File Descriptor)](#文件描述符-file-descriptor)
    - [退出状态 (Exit Status)](#退出状态-exit-status)
  - [📚 延伸阅读](#-延伸阅读)

**最后更新**: 2025-10-19
**适用版本**: Rust 1.75+
**文档类型**: 📚 参考资料

---

## 📋 术语索引

[F](#fork) | [I](#ipc-inter-process-communication) | [P](#进程-process) | [S](#信号-signal) | [Z](#僵尸进程-zombie-process)

**快速跳转**:

- [C07 进程管理: 术语表 (Glossary)](#c07-进程管理-术语表-glossary)
  - [📊 目录](#-目录)
  - [📋 术语索引](#-术语索引)
  - [术语详解](#术语详解)
    - [进程 (Process)](#进程-process)
    - [Fork](#fork)
    - [Exec](#exec)
    - [IPC (Inter-Process Communication)](#ipc-inter-process-communication)
    - [管道 (Pipe)](#管道-pipe)
    - [共享内存 (Shared Memory)](#共享内存-shared-memory)
    - [信号 (Signal)](#信号-signal)
    - [僵尸进程 (Zombie Process)](#僵尸进程-zombie-process)
    - [孤儿进程 (Orphan Process)](#孤儿进程-orphan-process)
    - [进程组 (Process Group)](#进程组-process-group)
    - [守护进程 (Daemon)](#守护进程-daemon)
    - [文件描述符 (File Descriptor)](#文件描述符-file-descriptor)
    - [退出状态 (Exit Status)](#退出状态-exit-status)
  - [📚 延伸阅读](#-延伸阅读)

---

## 术语详解

### 进程 (Process)

**定义**: 程序在操作系统中的一次执行实例，包含代码、数据、堆栈和系统资源。

**Rust中的实现**: `std::process::Command`

**相关**: [01_process_model_and_lifecycle](./01_process_model_and_lifecycle.md)

---

### Fork

**定义**: Unix系统调用，创建当前进程的完整副本（子进程）。

**特点**:

- 父子进程内存空间独立（写时复制）
- 子进程继承父进程的文件描述符
- 返回值：父进程中返回子进程PID，子进程中返回0

**Rust示例**:

```rust
#[cfg(unix)]
use nix::unistd::fork;

match unsafe { fork() } {
    Ok(ForkResult::Parent { child }) => {
        println!("父进程，子PID: {}", child);
    }
    Ok(ForkResult::Child) => {
        println!("子进程");
    }
    Err(e) => eprintln!("Fork失败: {}", e),
}
```

**注意**: Windows不支持fork，使用`CreateProcess`代替

**相关**: [01_process_model_and_lifecycle](./01_process_model_and_lifecycle.md)

---

### Exec

**定义**: 用新程序替换当前进程的内存空间。

**Unix exec家族**:

- `execl`, `execv`, `execle`, `execve`, `execlp`, `execvp`

**Rust中**: `Command::new()` + `spawn()` 实际上是fork+exec的组合

**相关**: [01_process_model_and_lifecycle](./01_process_model_and_lifecycle.md)

---

### IPC (Inter-Process Communication)

**定义**: 进程间通信机制的总称，用于不同进程之间交换数据。

**常见IPC机制**:

- 管道 (Pipe)
- 命名管道 (Named Pipe/FIFO)
- 消息队列 (Message Queue)
- 共享内存 (Shared Memory)
- 信号 (Signal)
- Socket
- 内存映射文件 (Memory-Mapped File)

**相关**: [02_ipc_mechanisms](./02_ipc_mechanisms.md)

---

### 管道 (Pipe)

**定义**: 单向数据流通道，用于父子进程或相关进程间通信。

**特点**:

- 单向通信（需要双向则创建两个管道）
- 缓冲区有限
- 数据按顺序传递

**Rust示例**:

```rust
use std::process::{Command, Stdio};

let child = Command::new("cat")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .spawn()?;
```

**相关**: [02_ipc_mechanisms](./02_ipc_mechanisms.md)

---

### 共享内存 (Shared Memory)

**定义**: 多个进程可以访问的同一块物理内存区域。

**特点**:

- 最快的IPC方式
- 需要同步机制（信号量、互斥锁）
- 跨平台实现复杂

**Rust实现**: 使用`shared_memory` crate

**相关**: [13_ipc_communication_advanced](./11_practical_examples/13_ipc_communication_advanced.md)

---

### 信号 (Signal)

**定义**: Unix/Linux中进程间异步通知机制。

**常见信号**:

- `SIGTERM` - 优雅终止请求
- `SIGKILL` - 强制终止
- `SIGINT` - 中断 (Ctrl+C)
- `SIGCHLD` - 子进程状态改变

**Rust处理**:

```rust
#[cfg(unix)]
use nix::sys::signal::{kill, Signal};

// 发送信号
kill(child_pid, Signal::SIGTERM)?;
```

**注意**: Windows不支持Unix信号

**相关**: [01_process_model_and_lifecycle](./01_process_model_and_lifecycle.md)

---

### 僵尸进程 (Zombie Process)

**定义**: 已终止但父进程未读取其退出状态的进程。

**状态**: 进程已死但仍占用进程表项

**解决方案**:

- 父进程调用`wait()`或`waitpid()`
- 设置`SIGCHLD`信号处理器
- 确保父进程存活期间处理子进程

**相关**: [FAQ Q4](./FAQ.md#q4-如何避免和处理僵尸进程)

---

### 孤儿进程 (Orphan Process)

**定义**: 父进程先于子进程退出，子进程被init进程(PID 1)收养。

**特点**:

- 不会成为僵尸进程（init会自动回收）
- 继续正常运行

**Rust中**: 守护进程(daemon)通常是故意创建的孤儿进程

**相关**: [01_process_model_and_lifecycle](./01_process_model_and_lifecycle.md)

---

### 进程组 (Process Group)

**定义**: 一组相关进程的集合，可以一起接收信号。

**用途**:

- 作业控制
- 批量信号发送
- 会话管理

**Rust设置**:

```rust
#[cfg(unix)]
use std::os::unix::process::CommandExt;

Command::new("app")
    .process_group(0) // 创建新进程组
    .spawn()?;
```

**相关**: [04_advanced_process_management](./04_advanced_process_management.md)

---

### 守护进程 (Daemon)

**定义**: 在后台运行的长期服务进程，不与任何终端关联。

**特征**:

- 父进程为init(PID 1)
- 无控制终端
- 通常在系统启动时启动

**创建步骤**:

1. Fork并让父进程退出
2. 调用`setsid()`创建新会话
3. 再次fork防止获取控制终端
4. 改变工作目录到`/`
5. 关闭文件描述符
6. 重定向stdin/stdout/stderr到`/dev/null`

**相关**: [04_advanced_process_management](./04_advanced_process_management.md)

---

### 文件描述符 (File Descriptor)

**定义**: 内核为进程维护的打开文件表的索引。

**标准文件描述符**:

- 0 - stdin (标准输入)
- 1 - stdout (标准输出)
- 2 - stderr (标准错误)

**Rust配置**:

```rust
Command::new("app")
    .stdin(Stdio::null())
    .stdout(Stdio::piped())
    .stderr(Stdio::inherit())
    .spawn()?;
```

**相关**: [12_std_process_deep_dive](./11_practical_examples/12_std_process_deep_dive.md)

---

### 退出状态 (Exit Status)

**定义**: 进程终止时返回给父进程的整数值。

**约定**:

- 0 - 成功
- 非0 - 错误（具体含义由程序定义）

**Rust获取**:

```rust
let status = child.wait()?;
if status.success() {
    println!("成功");
} else {
    println!("失败: {:?}", status.code());
}
```

**相关**: [01_process_model_and_lifecycle](./01_process_model_and_lifecycle.md)

---

## 📚 延伸阅读

- [主索引](./00_MASTER_INDEX.md) - 完整文档导航
- [FAQ](./FAQ.md) - 常见问题解答
- [01-10核心系列](./01_process_model_and_lifecycle.md) - 系统学习
- [11-18实践系列](./11_practical_examples/11_practical_examples.md) - 实践指南
