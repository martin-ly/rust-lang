# Rust 进程、通信与同步机制：深入分析与形式化视角

## 目录

- [Rust 进程、通信与同步机制：深入分析与形式化视角](#rust-进程通信与同步机制深入分析与形式化视角)
  - [目录](#目录)
  - [1. 引言：超越线程的并发维度](#1-引言超越线程的并发维度)
  - [2. Rust 中的进程管理](#2-rust-中的进程管理)
    - [2.1 概念：进程作为隔离单元](#21-概念进程作为隔离单元)
    - [2.2 `std::process::Command`：构建与执行](#22-stdprocesscommand构建与执行)
    - [2.3 进程生命周期与交互](#23-进程生命周期与交互)
    - [2.4 形式化视角：`Command` 的接口契约](#24-形式化视角command-的接口契约)
  - [3. 进程间通信 (IPC) 机制](#3-进程间通信-ipc-机制)
    - [3.1 标准流重定向 (Pipes)](#31-标准流重定向-pipes)
    - [3.2 网络套接字 (`std::net` 与异步变体)](#32-网络套接字-stdnet-与异步变体)
    - [3.3 共享内存 (Shared Memory)](#33-共享内存-shared-memory)
    - [3.4 消息队列 (Message Queues)](#34-消息队列-message-queues)
    - [3.5 信号 (Signals)](#35-信号-signals)
    - [3.6 文件系统作为 IPC](#36-文件系统作为-ipc)
    - [3.7 形式化定义：IPC 通道特性](#37-形式化定义ipc-通道特性)
    - [3.8 批判视角：标准库的局限与生态依赖](#38-批判视角标准库的局限与生态依赖)
  - [4. 同步机制：线程级与进程级](#4-同步机制线程级与进程级)
    - [4.1 区分：Intra-Process vs Inter-Process](#41-区分intra-process-vs-inter-process)
    - [4.2 线程同步原语（回顾）](#42-线程同步原语回顾)
    - [4.3 进程同步原语（Inter-Process Synchronization）](#43-进程同步原语inter-process-synchronization)
      - [4.3.1 命名信号量 (Named Semaphores)](#431-命名信号量-named-semaphores)
      - [4.3.2 系统互斥锁 (System Mutexes)](#432-系统互斥锁-system-mutexes)
      - [4.3.3 文件锁 (File Locks)](#433-文件锁-file-locks)
      - [4.3.4 共享内存中的同步原语](#434-共享内存中的同步原语)
    - [4.4 形式化定义：同步原语的保证](#44-形式化定义同步原语的保证)
    - [4.5 批判视角：安全边界的转移](#45-批判视角安全边界的转移)
  - [5. 与异步/并发模型的整合](#5-与异步并发模型的整合)
    - [5.1 阻塞操作的挑战](#51-阻塞操作的挑战)
    - [5.2 `spawn_blocking` 的作用](#52-spawn_blocking-的作用)
    - [5.3 异步原生支持](#53-异步原生支持)
  - [6. 结论：系统交互的 Rust 范式](#6-结论系统交互的-rust-范式)
  - [7. 思维导图](#7-思维导图)

---

## 1. 引言：超越线程的并发维度

之前的讨论深入分析了 Rust 在**线程级**并发（`std::thread`）和**任务级**并发（`async/await`, `Future`）方面的模型、安全保证（所有权、`Send`/`Sync`）以及相关的复杂性（`Pin`）。这些机制主要关注**单个进程内部**的并发执行和状态共享。

然而，现代系统常常需要**多个独立进程**协同工作。本篇将转换视角，梳理 Rust 如何处理进程创建、管理、进程间通信 (IPC) 以及跨进程的同步机制。我们将看到，与 Rust 对线程内存安全提供独特编译时保证不同，其在进程层面的能力更多地依赖于对底层操作系统原语的**封装和抽象**，安全责任也相应地从编译器部分转移到了开发者和操作系统。我们将结合形式化定义和批判性分析，审视这些机制的细节、保证和局限性。

## 2. Rust 中的进程管理

### 2.1 概念：进程作为隔离单元

**定义 (进程 Process)**：进程是操作系统进行资源分配和调度的基本单位，它拥有独立的内存地址空间、文件描述符、程序计数器和系统资源。进程间的隔离性是现代操作系统安全和稳定性的基石。

Rust 语言本身不重新定义进程概念，而是提供与操作系统交互以管理进程的接口。

### 2.2 `std::process::Command`：构建与执行

Rust 标准库通过 `std::process::Command` 结构体提供创建和配置新进程的能力。

**机制 (Process Builder Pattern)**：`Command` 采用构建器模式，允许链式调用配置方法：

```rust
use std::process::{Command, Stdio};
use std::io;

fn run_external_command() -> io::Result<()> {
    let mut cmd = Command::new("ls"); // 要执行的命令

    cmd.arg("-l") // 添加参数
       .arg("-a")
       .current_dir("/tmp") // 设置工作目录
       .env("MY_VAR", "value") // 设置环境变量
       .stdin(Stdio::null()) // 不提供标准输入
       .stdout(Stdio::piped()) // 捕获标准输出
       .stderr(Stdio::piped()); // 捕获标准错误

    // 启动进程
    let mut child = cmd.spawn()?; // 返回 Child 结构

    // ... 与子进程交互 ...

    Ok(())
}
```

### 2.3 进程生命周期与交互

`Command::spawn()` 成功后返回一个 `Child` 结构体，代表正在运行的子进程。

**机制 (Child Interaction)**：

- **获取句柄**：`child.stdin`, `child.stdout`, `child.stderr` 返回 `Option<ChildStdin>`, `Option<ChildStdout>`, `Option<ChildStderr>`，用于通过管道进行读写。
- **等待完成**：
  - `child.wait()`: 阻塞等待子进程结束，返回 `io::Result<ExitStatus>`。
  - `child.wait_with_output()`: 阻塞等待结束，并收集所有标准输出/错误，返回 `io::Result<Output>`。
  - `cmd.output()`: 启动进程、等待结束并收集输出的便捷方法。
  - `cmd.status()`: 启动进程、等待结束并只获取退出状态。
- **终止进程**：`child.kill()`: 发送 SIGKILL (Unix) 或 TerminateProcess (Windows) 尝试终止子进程。

**细节 (ExitStatus)**：`ExitStatus` 封装了进程的退出码或终止信号（Unix）。

### 2.4 形式化视角：`Command` 的接口契约

我们可以从接口契约的角度形式化 `Command` 的行为：

**定义 (Process Configuration `PConfig`)**: 一个包含可执行文件路径、参数列表、环境变量、工作目录、标准流配置等的记录。

**定义 (Process Handle `Child`)**: 一个代表操作系统子进程的句柄，可能包含 I/O 句柄（管道）。

**定义 (Exit Status `ExitStatus`)**: 包含进程退出码或终止原因的值。

**接口契约**:

1. **`Command::new(path) -> Command`**: 创建一个初始配置，目标为 `path`。
2. **`Command::arg/env/etc(self, ...) -> Command`**: 修改配置，返回更新后的配置。
3. **`Command::spawn(config: PConfig) -> io::Result<Child>`**:
    - **前提**: `config` 中的路径有效，当前用户有执行权限。
    - **保证**: 若成功 (`Ok`)，则操作系统已启动一个新进程，其状态由 `config` 指定，并返回一个 `Child` 句柄。若失败 (`Err`)，则没有新进程被创建。进程间的内存隔离由 OS 保证。
4. **`Child::wait(child: Child) -> io::Result<ExitStatus>`**:
    - **保证**: 调用线程将阻塞，直到 `child` 代表的 OS 进程终止。返回其最终状态。OS 保证进程资源会被回收。
5. **`Child::kill(child: Child) -> io::Result<()>`**:
    - **保证**: 尝试向 OS 请求终止 `child` 进程。成功不保证进程立即死亡，仅表示终止请求已发送。

**定理 (进程隔离)**：由 `spawn` 创建的两个不同 `Child` 进程 `c1` 和 `c2`，其内存地址空间是相互隔离的（由 OS 保证），除非显式使用 IPC 机制共享。Rust 的所有权和借用规则**不直接**管理这种跨进程隔离。

## 3. 进程间通信 (IPC) 机制

进程间通信是允许多个独立进程交换数据和协调工作的关键。Rust 对 IPC 的支持程度不一，部分在标准库，部分依赖生态 crate。

### 3.1 标准流重定向 (Pipes)

这是最基础、最常用的 IPC 形式，集成在 `std::process` 中。

**机制**: 通过 `Command::stdin/stdout/stderr(Stdio::piped())` 配置，`spawn()` 后通过 `Child::stdin/stdout/stderr` 获取管道句柄。

**形式化定义 (Pipe)**: 一个单向的、基于字节流的、由操作系统内核管理的通信通道。`Pipe ≈ Queue<byte>`。

**保证 (Pipe Semantics)**:

- 写入 `ChildStdin` 的数据会成为子进程的标准输入。
- 子进程写入标准输出/错误的数据可通过 `ChildStdout`/`ChildStderr` 读取。
- 顺序保证：字节按写入顺序读取。
- 阻塞行为：管道缓冲区满时写入阻塞，空时读取阻塞（除非配置为非阻塞）。

### 3.2 网络套接字 (`std::net` 与异步变体)

适用于本地或跨网络的进程通信。

**机制**:

- `std::net::TcpListener`, `std::net::TcpStream` (TCP)
- `std::net::UdpSocket` (UDP)
- `std::os::unix::net::UnixListener`, `std::os::unix::net::UnixStream` (Unix 域套接字，本地高效 IPC)

**形式化定义 (Socket)**: 网络通信的一个端点，由 IP 地址和端口号（或文件系统路径对 Unix 域套接字）标识。

**保证 (Socket Semantics)**:

- **TCP**: 面向连接、可靠、有序的字节流。
- **UDP**: 无连接、不可靠、无序的数据报。
- **Unix Domain**: 类 TCP 或类 UDP，但限于本地，通常更快，使用文件系统权限。

**异步集成**: `tokio::net`, `async-std::net` 提供了这些 API 的异步版本，与 `async/await` 良好集成。

### 3.3 共享内存 (Shared Memory)

最高效的 IPC 机制之一，但也是最危险的，因为它直接破坏了进程隔离。

**机制**:

- **标准库无直接支持**。
- 依赖 crate：`shared_memory`, `ipc-channel` (其内部可能使用共享内存), `memmap2` (内存映射文件，可用于共享)。
- 通常涉及：创建/打开命名内存区域 -> 映射到进程地址空间 -> 直接读写内存。

**形式化定义 (Shared Region `SR`)**: `SR = Map(name: String, size: usize) -> Result<MemoryRegion>`。`MemoryRegion` 是一块可由多个进程访问的原始内存。

**保证与风险**:

- **OS 保证**: 多个进程映射同一 `name` 的区域时，访问的是同一块物理内存。
- **Rust 安全保证失效**: Rust 的所有权、借用和 `Send/Sync` **不适用于**跨进程共享的原始内存。编译器无法防止数据竞争。
- **同步是关键**: **必须**使用外部的、跨进程的同步机制（如系统信号量、互斥锁）来协调对共享内存的访问，否则极易导致未定义行为。

### 3.4 消息队列 (Message Queues)

提供基于消息的、解耦的通信方式。

**机制**:

- **标准库无直接支持**。
- 依赖 crate：`posix-mq` (POSIX), 特定平台 crate (如 Windows)。
- 通常涉及：创建/打开命名队列 -> 发送消息 -> 接收消息。

**形式化定义 (Message Queue `MQ`)**: `MQ(name) -> Handle`。`Send(Handle, Msg) -> Result<()>`, `Receive(Handle) -> Result<Msg>`。

**保证 (Queue Semantics)**:

- 消息边界得以保留。
- 顺序性、持久性、阻塞行为等取决于具体实现（如 POSIX vs System V）。

### 3.5 信号 (Signals)

一种异步的、低带宽的通知机制，主要用于简单的进程控制。

**机制**:

- **标准库**：`Child::kill()` 发送信号。
- **处理信号**：标准库无直接支持，需要 `signal-hook`, `ctrlc` 等 crate，或直接使用 `libc`。
- 处理函数（Signal Handler）内可做的事情非常有限（必须是 async-signal-safe 的）。

**形式化定义 (Signal)**: `Signal(pid, sig_type)`. 一个发送给特定进程的异步事件。

**保证与风险**:

- **不可靠**: 信号可能丢失。
- **竞态条件**: 信号处理易引入竞态条件。
- **复杂性**: 安全地处理信号非常困难。

### 3.6 文件系统作为 IPC

利用文件进行数据交换或作为锁机制。

**机制**:

- 进程 A 写入文件，进程 B 读取文件。
- 使用文件锁（`flock`, `fcntl`）进行同步（见下文）。

**保证**: 依赖于文件系统的原子性和一致性保证。

### 3.7 形式化定义：IPC 通道特性

可以根据几个维度形式化描述不同的 IPC 机制：

| 特性             | Pipes      | TCP Sockets | UDP Sockets | Unix Domain | Shared Memory | Msg Queues | Files      |
| :--------------- | :--------- | :---------- | :---------- | :---------- | :------------ | :--------- | :--------- |
| **边界保留**     | 否 (流式)  | 否 (流式)   | 是 (数据报) | 否/是       | 否 (内存)     | 是 (消息)  | 否 (字节)  |
| **可靠性**       | 高         | 高          | 低          | 高          | N/A           | OS 依赖    | FS 依赖    |
| **顺序性**       | 是         | 是          | 否          | 是          | N/A           | OS 依赖    | 是         |
| **连接性**       | N/A        | 面向连接    | 无连接      | 面向连接    | N/A           | 无连接     | N/A        |
| **效率**         | 中         | 中-低       | 中          | 高          | **极高**      | 中-高      | 低         |
| **同步需求**     | 隐式/无    | 隐式/无     | 无          | 隐式/无     | **显式/高**   | 隐式/低    | 显式/中    |
| **std 支持**     | 部分       | 是          | 是          | Unix        | **否**        | **否**     | 是         |

### 3.8 批判视角：标准库的局限与生态依赖

Rust 标准库在 IPC 方面的支持相对基础，主要覆盖了管道和网络套接字。对于共享内存、消息队列等高效或特定场景的 IPC 机制，则完全依赖于第三方 crate。

- **优点**: 保持了标准库的精简和跨平台性。
- **缺点**:
  - 增加了开发者寻找、评估和集成第三方库的负担。
  - 缺乏标准接口可能导致生态碎片化（不同 crate 提供功能类似但 API 不兼容的 IPC）。
  - 对于需要高性能 IPC 的场景，开发者必须跳出标准库。

这种设计哲学与运行时分离类似，体现了 Rust 倾向于让社区探索和标准化复杂系统交互模式的策略。

## 4. 同步机制：线程级与进程级

### 4.1 区分：Intra-Process vs Inter-Process

必须严格区分两种同步：

1. **线程同步 (Intra-Process)**: 同一进程内的多个线程访问共享数据（内存）。由 Rust 的所有权、`Send/Sync` 和 `std::sync` 原语（Mutex, RwLock, Condvar, Barrier, channel）提供强大的编译时安全保证。
2. **进程同步 (Inter-Process)**: 不同进程（拥有独立内存）之间协调操作或访问共享资源（如文件、共享内存段、系统资源）。安全保证**主要依赖操作系统**和开发者的正确使用，Rust 编译器在此作用有限。

### 4.2 线程同步原语（回顾）

`std::sync::{Mutex, RwLock, Condvar, Barrier}` 和 `std::sync::mpsc::channel` 以及 `std::sync::atomic` 类型，结合所有权和 `Send/Sync`，为线程安全提供了核心保障。其关键在于它们操作的是**进程内的共享内存**，并受到 Rust 类型系统的严格检查。

### 4.3 进程同步原语（Inter-Process Synchronization）

这些原语用于协调不同进程。它们通常是**命名**的（可通过名字在系统范围内访问）或基于**文件描述符/句柄**。Rust 标准库**几乎不直接提供**这些，需要依赖 crate 或 OS 特定 API。

#### 4.3.1 命名信号量 (Named Semaphores)

**概念**: 操作系统维护的、可通过名称访问的计数器，用于限制对共享资源的并发访问数量或进行进程间通知。

**机制**:

- 需要 crate 如 `ipc-semaphore` 或直接调用 `libc` 中的 `sem_open`, `sem_wait`, `sem_post`, `sem_close`。

**形式化定义 (Semaphore `Sem`)**: `Sem(name: String, initial_value: u32) -> Result<Handle>`。

- `Wait(Handle)`: 原子操作 `if counter > 0 { counter -= 1; return Ok(()) } else { block until counter > 0 }`。
- `Post(Handle)`: 原子操作 `counter += 1; signal_one_waiter()`。

**保证 (Semaphore Atomicity & Wait)**: OS 保证 `Wait` 和 `Post` 操作的原子性以及等待/唤醒机制的正确性。

#### 4.3.2 系统互斥锁 (System Mutexes)

**概念**: 操作系统提供的、可通过名称（或某些机制）访问的互斥锁，用于确保在任何时刻只有一个进程能进入临界区或访问某个系统级共享资源。

**机制**:

- 需要 crate 如 `interprocess`, `system-mutex` 或直接调用 OS API (`pthread_mutex_t` 配置为 PSHARED, Windows `CreateMutex`)。

**形式化定义 (System Mutex `SysMutex`)**: `SysMutex(name: String) -> Result<Handle>`。

- `Lock(Handle)`: `if mutex_is_free { mark_as_locked_by_me; return Ok(()) } else { block until free }`。
- `Unlock(Handle)`: `if locked_by_me { mark_as_free; signal_one_waiter(); return Ok(()) } else { return Err(...) }`。

**保证 (System-Wide Mutual Exclusion)**: OS 保证在正确使用下，同一时间只有一个进程能持有该命名的互斥锁。

#### 4.3.3 文件锁 (File Locks)

**概念**: 利用文件系统提供的锁机制来协调对文件或关联资源的访问。

**机制**:

- `std::fs::File` 本身功能有限。
- 常用 crate `fs2`, `fd-lock` 封装了 `fcntl` (POSIX) 或 `LockFileEx` (Windows)。
- 类型：共享锁（读锁） vs 排他锁（写锁）。
- 范围：整个文件 vs 文件区域。
- 模式：阻塞 vs 非阻塞。
- 性质：通常是**劝告性 (advisory)** 的，需要所有协作进程都遵守约定才能生效。

**形式化定义 (File Lock `FLock`)**: `FLock(file: FileHandle, type: LockType, mode: LockMode) -> Result<()>`。`FUnlock(file: FileHandle) -> Result<()>`。

**保证 (File Lock Semantics)**: 取决于 OS 和文件系统。劝告锁仅在所有进程合作时提供互斥。强制锁（较少见）由内核强制执行。

#### 4.3.4 共享内存中的同步原语

**概念**: 在共享内存区域内实现同步原语（如互斥锁、条件变量）。

**机制**:

- 极其复杂，**标准库无支持**。
- 需要 crate (`ipc-channel` 可能内部实现，`parking_lot` 可配置用于 no-std 但需要 OS futex 支持等) 或手动基于原子操作和 OS futex/wait-address 实现。
- **核心挑战**: 需要将同步状态（如锁是否被持有、等待队列）存放在共享内存中，并使用原子操作和 OS 提供的底层等待/唤醒机制（如 futex）来避免自旋等待。

**保证与风险**: 高度依赖实现的正确性。极易出错，性能调优困难。

### 4.4 形式化定义：同步原语的保证

进程同步原语的核心保证是**原子性 (Atomicity)** 和 **互斥性 (Mutual Exclusion)** 或 **条件等待 (Conditional Waiting)**，这些保证由**操作系统内核**提供。

**定理 (Inter-Process Mutual Exclusion)**：对于一个系统互斥锁 M，如果进程 P1 调用 `Lock(M)` 成功，则在 P1 调用 `Unlock(M)` 之前，任何其他进程 P2 调用 `Lock(M)` 都会阻塞或失败（取决于模式）。

**定理 (Semaphore Wait Condition)**：进程 P 调用 `Wait(S)` 将会阻塞，当且仅当信号量 S 的内部计数器为 0。

Rust 代码本身只是调用了这些 OS API，其正确性依赖于 OS 实现和开发者对这些原语的正确使用。

### 4.5 批判视角：安全边界的转移

与线程同步相比，进程同步的安全性有本质不同：

1. **编译器检查失效**: Rust 编译器无法静态检查跨进程同步的正确性。例如，忘记在使用共享内存时加锁，编译器无法发现。`Send`/`Sync` 不适用于跨进程场景。
2. **责任转移**: 确保数据一致性和避免竞态条件的责任从编译器（部分）转移给了开发者和操作系统。
3. **`unsafe` 的普遍性**: 实现或使用许多高级 IPC 和进程同步机制通常需要 `unsafe` 代码块（直接调用 C API 或操作原始内存）。
4. **平台依赖性**: 许多进程同步机制的行为和可用性是平台相关的。

> **批判观点**: Rust 在进程级交互方面更像一个传统的系统编程语言，提供了对 OS 功能的访问，但其独特的编译时安全保证在这里作用有限。开发者需要具备更深厚的操作系统知识和更强的纪律性来确保跨进程操作的正确性和安全性。

## 5. 与异步/并发模型的整合

进程管理、IPC 和进程同步操作通常是**阻塞**的系统调用。这与 Rust 的 `async/await` 模型存在潜在冲突。

### 5.1 阻塞操作的挑战

在 `async` 函数中直接调用阻塞的 OS API（如 `child.wait()`, `socket.read()`, `file.lock()`, 多数 crate 提供的进程同步原语的 `lock()`）会导致执行该 `async` 任务的**执行器线程被阻塞**。如果运行时（如 Tokio）使用少量工作线程，这可能导致其他 `async` 任务无法被轮询，造成性能下降甚至死锁（线程饥饿）。

### 5.2 `spawn_blocking` 的作用

异步运行时（如 Tokio, async-std）通常提供 `spawn_blocking` 函数来解决此问题。

**机制**: 将一个闭包（包含阻塞代码）提交给一个**独立的、专门用于运行阻塞任务的线程池**。`spawn_blocking` 本身返回一个 `Future`，可以在 `async` 上下文中 `.await`。当阻塞操作完成时，`Future` 会完成。

```rust
use std::process::Command;
use tokio::task;

async fn wait_for_child_async(mut child: std::process::Child) -> std::io::Result<std::process::ExitStatus> {
    // 将阻塞的 wait() 操作移到阻塞线程池
    task::spawn_blocking(move || child.wait())
        .await // 等待阻塞操作完成
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))? // 处理 JoinError
}
```

**意义**: 确保了异步执行器线程的非阻塞性，维持了异步系统的响应能力。

### 5.3 异步原生支持

对于常见的阻塞操作，生态系统通常会提供异步原生版本：

- **网络**: `tokio::net`, `async-std::net`。
- **进程管理**: `tokio::process::Command` 提供了异步的 `spawn`, `wait`, `output` 等。
- **文件 I/O**: `tokio::fs`, `async-std::fs`。
- **IPC/同步**: 一些 crate 可能提供异步接口（例如，某些基于 io_uring 的库），但这相对较少，尤其是对于跨进程同步原语。

使用异步原生 API 是首选，因为它们通常更高效（直接集成到运行时的事件循环中）且更符合 `async/await` 的编程模型。当没有异步 API 可用时，`spawn_blocking` 是必要的备选方案。

## 6. 结论：系统交互的 Rust 范式

Rust 在处理进程、IPC 和进程同步方面，展现了与处理线程并发不同的设计哲学：

1. **拥抱 OS 原语**: Rust 没有试图重新发明进程模型或大多数 IPC/同步机制，而是提供了对底层 OS 功能的封装。
2. **安全边界**: Rust 强大的编译时安全保证主要适用于进程内的内存和线程安全。对于跨进程交互，特别是涉及共享内存或需要复杂同步的场景，安全责任更多地落在开发者身上，需要依赖 OS 提供的保证和开发者自身的严谨性。
3. **标准库的保守性**: 标准库仅包含最基础、跨平台性最好的进程管理和 IPC 功能（管道、网络）。更高级或平台相关的机制依赖于社区生态。
4. **异步整合**: 通过 `spawn_blocking` 和生态系统提供的异步原生 API，Rust 的异步模型可以与阻塞的系统调用进行有效整合，尽管这增加了编程的复杂性。

总体而言，Rust 为系统级进程交互提供了必要的工具，但开发者需要认识到其安全模型的边界，并结合操作系统知识来构建可靠的多进程应用程序。生态系统在弥补标准库的不足方面扮演了至关重要的角色。

## 7. 思维导图

```text
Rust 进程、通信与同步机制
│
├── 1. 进程管理 (std::process)
│   ├── 概念：OS 隔离单元
│   ├── Command (构建器模式)
│   │   ├── 配置：args, env, cwd, stdio
│   │   └── 执行：spawn() -> Child
│   ├── Child (进程句柄)
│   │   ├── 交互：stdin, stdout, stderr (Pipes)
│   │   ├── 等待：wait(), wait_with_output()
│   │   └── 终止：kill()
│   └── 形式化：接口契约, 进程隔离定理
│
├── 2. 进程间通信 (IPC)
│   ├── Pipes (Stdio redirection)
│   │   ├── 机制：Stdio::piped()
│   │   └── 特性：字节流, 有序, 可靠, std 支持
│   ├── Sockets (std::net, async variants)
│   │   ├── 类型：TCP, UDP, Unix Domain
│   │   └── 特性：网络/本地, 可靠/不可靠, std 支持
│   ├── Shared Memory (Crates: shared_memory, ipc-channel)
│   │   ├── 机制：命名区域, 内存映射
│   │   ├── 特性：**极高效**, **无边界**, **同步关键**
│   │   └── **Rust 安全保证失效**, **std 不支持**
│   ├── Message Queues (Crates: posix-mq)
│   │   ├── 机制：命名队列, 发送/接收
│   │   └── 特性：消息边界保留, 解耦, **std 不支持**
│   ├── Signals (Crates: signal-hook)
│   │   ├── 机制：异步通知
│   │   └── 特性：低带宽, **不可靠**, 处理复杂, **std 不支持**
│   ├── Filesystem
│   │   ├── 机制：文件读写, 文件锁
│   │   └── 特性：简单, 依赖 FS 保证
│   └── 批判视角：std 功能有限, 依赖生态
│
├── 3. 同步机制
│   ├── 区分：Intra-process (线程) vs Inter-process (进程)
│   ├── 线程同步 (回顾 std::sync)
│   │   ├── Mutex, RwLock, Condvar, Barrier, Atomics, Channels
│   │   └── **Rust 强安全保证** (所有权, Send/Sync)
│   ├── 进程同步 (Inter-Process, **主要靠 Crates/OS**)
│   │   ├── Named Semaphores (ipc-semaphore, libc)
│   │   │   └── 概念：系统级计数器
│   │   ├── System Mutexes (interprocess, system-mutex)
│   │   │   └── 概念：系统级互斥锁
│   │   ├── File Locks (fs2, fd-lock)
│   │   │   └── 概念：基于文件的锁 (常为劝告性)
│   │   └── Shared Memory Sync Primitives (复杂, Crates/Custom)
│   │       └── 概念：在共享内存中实现锁/条件变量 (需原子+futex)
│   ├── 形式化：原子性、互斥性、条件等待 (由 OS 保证)
│   └── 批判视角：**安全责任转移给开发者/OS**, **编译器检查失效**
│
├── 4. 与异步/并发模型整合
│   ├── 挑战：阻塞 OS 调用 vs Async 执行器
│   ├── 解决方案：`spawn_blocking`
│   │   └── 机制：移交阻塞任务给独立线程池
│   └── 异步原生 API
│       ├── 网络, 文件, 部分进程操作 (e.g., tokio::process)
│       └── 优选方案 (若可用)
│
└── 5. 结论
    ├── Rust 角色：OS 原语的安全封装者
    ├── 安全边界：线程内强保证，进程间依赖 OS 和开发者
    ├── 标准库策略：保守，核心功能，依赖生态扩展
    └── 范式：系统编程务实性，需结合 OS 知识
```
