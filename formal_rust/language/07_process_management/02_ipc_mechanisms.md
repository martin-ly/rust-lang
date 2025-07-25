# C07-02. 进程间通信机制（IPC Mechanisms）

本章系统梳理 Rust 在进程间通信（IPC）方面的理论基础与工程实现，涵盖管道、命名管道、套接字、共享内存、信号、消息队列等主流机制。

## 1. 管道与命名管道

- **管道（Pipe）**：单向通信通道，由读取端和写入端组成，数据以字节流形式传递。
- **Rust 实现**：通过 `std::process::Command` 的 I/O 重定向实现父子进程间管道。

```rust
use std::process::{Command, Stdio};
let mut child = Command::new("wc")
    .stdin(Stdio::piped())
    .spawn()?;
```

- **命名管道（FIFO）**：具名、可在无亲缘关系进程间通信，需依赖平台 API（如 Unix 的 `mkfifo`）。

## 2. 套接字通信

- **套接字（Socket）**：支持本地或网络进程间的全双工通信。
- **Rust 实现**：`std::net::{TcpListener, TcpStream, UdpSocket}` 提供跨平台 TCP/UDP 通信。

```rust
use std::net::{TcpListener, TcpStream};
let listener = TcpListener::bind("127.0.0.1:8080")?;
for stream in listener.incoming() {
    let mut stream = stream?;
    // 处理 stream
}
```

- **Unix 域套接字**：`std::os::unix::net::UnixStream` 支持本地进程间高效通信。

## 3. 共享内存

- **共享内存**：多个进程映射同一物理内存区域，实现高速数据交换。
- **Rust 实现**：需依赖第三方 crate（如 `memmap2`、`shmem`），或 FFI 调用平台 API。

```rust
// 伪代码示例
let mmap = memmap2::MmapOptions::new().map(&file)?;
```

- **同步问题**：共享内存需配合锁、信号量等同步原语，防止数据竞争。

## 4. 信号机制

- **信号（Signal）**：操作系统用于通知进程异步事件的机制。
- **Rust 实现**：`signal-hook`、`nix::sys::signal` 等 crate 提供信号注册与处理。

```rust
use signal_hook::iterator::Signals;
let mut signals = Signals::new(&[signal_hook::consts::SIGTERM])?;
for sig in signals.forever() {
    // 处理信号
}
```

## 5. 消息队列

- **消息队列**：内核或用户空间的 FIFO 队列，实现进程间异步消息传递。
- **Rust 实现**：`crossbeam-channel`、`ipc-channel` 等 crate 提供高层抽象。

```rust
use crossbeam_channel::unbounded;
let (tx, rx) = unbounded();
tx.send("hello")?;
let msg = rx.recv()?;
```

- **平台 API**：可通过 FFI 调用 POSIX 消息队列（`mq_open` 等）。

## 6. 机制对比与选型建议

| 机制         | 适用场景           | 跨平台 | 性能   | 复杂度 |
|--------------|--------------------|--------|--------|--------|
| 管道         | 父子进程简单通信   | 是     | 中     | 低     |
| 命名管道     | 无亲缘进程通信     | 否     | 中     | 中     |
| 套接字       | 网络/本地通用      | 是     | 中高   | 中     |
| 共享内存     | 大数据量高速交换   | 否     | 高     | 高     |
| 信号         | 异步事件通知       | 否     | 低     | 低     |
| 消息队列     | 异步/多生产多消费  | 否     | 中     | 中     |

- **选型建议**：优先选用标准库和成熟 crate，跨平台优先考虑管道和套接字；高性能场景可用共享内存但需注意同步。

## 7. 小结

Rust 提供了丰富的 IPC 机制抽象，结合类型系统和所有权模型，既保证了安全性，又兼顾了性能和可移植性。实际工程中应根据通信模式、性能需求和平台兼容性合理选型。
