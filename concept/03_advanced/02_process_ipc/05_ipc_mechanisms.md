> **EN**: Inter-Process Communication Mechanisms in Rust
> **Summary**: IPC patterns in Rust: anonymous pipes, named pipes, Unix sockets, TCP/UDP sockets, shared memory, message queues, and signal handling.
> **Rust Version**: 1.96.1+
> **受众**: [专家]
> **内容分级**: [专家级]
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **S+A** — Structure + Application
> **双维定位**: S×App — 应用 IPC 机制选型
> **前置依赖**: [Process Model and Lifecycle](01_process_model_and_lifecycle.md) · [Smart Pointers](../../02_intermediate/02_memory_management/12_smart_pointers.md) · [Error Handling](../../02_intermediate/03_error_handling/04_error_handling.md)
> **后置概念**: [Process Monitoring](06_process_monitoring_and_diagnostics.md) · [Process Security](07_process_security_and_sandboxing.md) · [Process Performance Engineering](08_process_performance_engineering.md)
> **定理链**: IPC Mechanism ⟹ Latency/Throughput Trade-off ⟹ Safety

# Rust 进程间通信机制（IPC）

> **权威页地位**：本页为 Rust IPC 概念的 canonical 解释来源。
> **对应 crate 示例**：`crates/c07_process/docs/tier_02_guides/02_ipc_communication_practice.md` 现为摘要页，指向此处。

---

## 1. IPC 机制概览

| 机制 | 性能 | 跨网络 | 复杂度 | 适用场景 |
| :--- | :--- | :--- | :--- | :--- |
| 管道（Pipe） | 中 | ❌ | 低 | 父子进程 |
| 命名管道（FIFO） | 中 | ❌ | 低 | 本地无亲缘进程 |
| Unix 域套接字 | 高 | ❌ | 中 | 本地复杂通信 |
| TCP/UDP 套接字 | 中 | ✅ | 中 | 跨网络通信 |
| 共享内存 | 最高 | ❌ | 高 | 大数据高性能 |
| 消息队列 | 中 | ❌ | 中 | 异步（Async）消息传递 |
| 信号（Signal） | 低 | ❌ | 低 | 事件通知 |

## 2. 匿名管道

通过 `std::process::Command` 的 I/O 重定向实现父子进程间单向通信：

```rust
use std::process::{Command, Stdio};
use std::io::Write;

fn basic_pipe() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;

    if let Some(mut stdin) = child.stdin.take() {
        stdin.write_all(b"Hello Pipe!\n")?;
        // stdin 在这里 drop，子进程读取到 EOF 后退出
    }

    let output = child.wait_with_output()?;
    println!("{}", String::from_utf8_lossy(&output.stdout));
    Ok(())
}
```

**关键点**：

- 必须调用 `take()` 获取管道所有权（Ownership）。
- 写入后关闭 stdin（或 drop），否则子进程会一直等待。
- 使用 `wait_with_output()` 同时等待进程结束并收集输出。

## 3. 命名管道（FIFO）

命名管道允许无亲缘关系的本地进程通信。Unix 上通过 `nix::unistd::mkfifo` 创建，Windows 上通过 `tokio::net::windows::named_pipe` 或 `windows-named-pipe` crate 实现。

## 4. Unix 域套接字

Unix 域套接字提供本地双向流式通信，性能通常高于 TCP 回环：

```rust
use std::os::unix::net::{UnixListener, UnixStream};
use std::io::{Read, Write};

fn server() -> Result<(), Box<dyn std::error::Error>> {
    let listener = UnixListener::bind("/tmp/rust_ipc.sock")?;

    if let Ok((mut stream, _)) = listener.accept() {
        let mut buf = [0u8; 1024];
        let n = stream.read(&mut buf)?;
        stream.write_all(&buf[..n])?;
    }

    Ok(())
}
```

## 5. TCP/UDP 套接字

`std::net` 提供跨平台 TCP/UDP 通信，适合本地或网络场景：

```rust
use std::net::{TcpListener, TcpStream};

fn tcp_server() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:8080")?;
    for stream in listener.incoming() {
        let _stream: TcpStream = stream?;
        // 处理连接
    }
    Ok(())
}
```

## 6. 共享内存

共享内存通过多个进程映射同一物理内存区域实现高速数据交换，但需要额外同步机制（如信号量、互斥锁、原子操作（Atomic Operations））防止数据竞争：

```rust
// 示意：使用 memmap2 创建共享内存映射
use memmap2::MmapOptions;
use std::fs::OpenOptions;

fn shared_memory() -> Result<(), Box<dyn std::error::Error>> {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .open("/tmp/shm")?;

    let mmap = unsafe { MmapOptions::new().map_mut(&file)? };
    // 通过 mmap 读写共享数据，需配合同步原语
    Ok(())
}
```

## 7. 消息队列

用户空间消息队列 crate（如 `crossbeam-channel`、`ipc-channel`）提供比内核消息队列更易用的抽象，适合同一机器内进程或线程间通信。

## 8. 信号处理

Unix 信号用于通知进程异步事件。Rust 中常用 `signal-hook` 或 `tokio::signal`：

```rust
use signal_hook::iterator::Signals;

fn handle_signals() -> Result<(), Box<dyn std::error::Error>> {
    let mut signals = Signals::new(&[signal_hook::consts::SIGTERM, signal_hook::consts::SIGINT])?;

    for sig in signals.forever() {
        println!("收到信号: {}", sig);
        // 执行清理并退出
    }

    Ok(())
}
```

## 9. 选型建议

- 父子进程简单通信：匿名管道。
- 本地无亲缘进程：命名管道或 Unix 域套接字。
- 高性能大数据：共享内存 + 同步原语。
- 跨网络通信：TCP/UDP 套接字。
- 异步事件通知：信号。
- 同一主机进程/线程间消息传递：`crossbeam-channel`。

> **L2 向下引用（Reference）**: IPC 安全抽象建立在 [Trait 系统](../../02_intermediate/00_traits/01_traits.md) 与 [错误处理（Error Handling）](../../02_intermediate/03_error_handling/04_error_handling.md) 之上。

## 补充视角：IPC 机制工程选型速查

> 本节选编自 `crates/c07_process/docs/02_ipc_mechanisms.md`，
> 作为 canonical IPC 概念页的工程实践补充。

### 机制对比

| 机制 | 适用场景 | 跨平台 | 性能 | 复杂度 |
| :--- | :--- | :--- | :--- | :--- |
| 管道 | 父子进程简单通信 | 是 | 中 | 低 |
| 命名管道 | 无亲缘进程通信 | 否 | 中 | 中 |
| 套接字 | 网络/本地通用 | 是 | 中高 | 中 |
| 共享内存 | 大数据量高速交换 | 否 | 高 | 高 |
| 信号 | 异步事件通知 | 否 | 低 | 低 |
| 消息队列 | 异步/多生产多消费 | 否 | 中 | 中 |

### 选型原则

- 优先选用标准库和成熟 crate。
- 跨平台场景优先考虑管道与套接字。
- 高性能场景可用共享内存，但必须配合同步原语防止数据竞争。

---

## 相关概念

- [进程模型与生命周期（Lifetimes）](01_process_model_and_lifecycle.md)
- [并发模型](../00_concurrency/01_concurrency.md)
- [原子操作与内存序](../00_concurrency/11_atomics_and_memory_ordering.md)
- [Rust 网络编程](../06_low_level_patterns/18_network_programming.md)

---

> **权威来源**: [Rust Standard Library — std::process](https://doc.rust-lang.org/std/process/) · [Rust Standard Library — std::net](https://doc.rust-lang.org/std/net/) · [signal-hook crate](https://docs.rs/signal-hook/) · [memmap2 crate](https://docs.rs/memmap2/)

---

## 10. IPC 选型决策流程（Mermaid）

```mermaid
flowchart TD
    Start["选择 IPC 机制"] --> Q1{"通信双方是否有亲缘关系?"}
    Q1 -->|是| Pipe["匿名管道<br/>std::process Stdio"]
    Q1 -->|否| Q2{"是否在同一主机?"}
    Q2 -->|否| Socket["TCP/UDP Socket"]
    Q2 -->|是| Q3{"是否需要最高性能?"}
    Q3 -->|是| SHM["共享内存 + 原子/信号量"]
    Q3 -->|否| Q4{"是否需要双向流?"}
    Q4 -->|是| UDS["Unix Domain Socket"]
    Q4 -->|否| FIFO["命名管道 / 消息队列"]
```

---

## 11. 可运行示例：父子匿名管道

```rust,editable
use std::io::Write;
use std::process::{Command, Stdio};

fn main() -> std::io::Result<()> {
    let mut child = Command::new("cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;

    if let Some(mut stdin) = child.stdin.take() {
        writeln!(stdin, "hello pipe")?;
    }

    let output = child.wait_with_output()?;
    println!("{}", String::from_utf8_lossy(&output.stdout));
    Ok(())
}
```

## 认知路径

1. **问题识别**: 识别不同 IPC 机制在延迟、吞吐、复杂度与跨网络能力上的权衡。
2. **概念建立**: 掌握匿名管道、命名管道、Unix 域套接字、TCP/UDP、共享内存与信号的使用场景。
3. **机制推理**: 通过机制特性 ⟹ 选型 ⟹ 安全边界的定理链进行工程决策。
4. **边界辨析**: 辨析“共享内存总是最快”等反命题，理解同步开销与数据一致性（Coherence）问题。
5. **迁移应用**: 将 IPC 与监控、安全、性能工程主题链接。

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| 管道简单 ⟹ 低开销但仅限亲缘进程 | 匿名管道基于文件描述符 | 适合父子进程单向流 |
| Unix 域套接字 ⟹ 高吞吐本地通信 | 绕过网络协议栈 | 适合同机复杂双向通信 |
| 共享内存 ⟹ 零拷贝但需同步 | 多个进程映射同一段物理内存 | 必须配合 Mutex/Semaphore 避免数据竞争 |

## 反命题

> **反命题 1**: "共享内存总是最快的 IPC" ⟹ 不成立。若同步开销过高或数据量小，其优势可能被抵消。
>
> **反命题 2**: "管道可以双向通信" ⟹ 不成立。匿名管道通常是单向的，双向通信需创建两个管道或改用套接字。
>
> **反命题 3**: "IPC 数据不需要序列化" ⟹ 不成立。进程地址空间独立，必须通过协议或序列化传递结构化数据。
>
## 反向推理

> **反向推理 1**: 观察到 IPC 延迟随消息大小剧增 ⟸ 说明应评估共享内存或零拷贝方案。
>
> **反向推理 2**: 发现消息乱序或丢失 ⟸ 说明未在不可靠通道上实现序列号或确认机制。
>
## 过渡段

> **过渡**: 从 IPC 机制概览过渡到具体实现，可以理解每种机制都是延迟、复杂度与可移植性的权衡。
>
> **过渡**: 从管道与套接字过渡到共享内存，可以建立“数据量小的时候用拷贝，数据量大的时候用映射”的选型直觉。
>
> **过渡**: 从共享内存过渡到安全与同步，可以理解 IPC 性能优势必须与同步原语配套使用。
>
