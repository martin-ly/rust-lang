# io_uring 高性能 I/O 指南

## 概述

io_uring 是 Linux 内核 5.1+ 引入的异步 I/O 接口，通过共享的提交队列（Submission Queue, SQ）和完成队列（Completion Queue, CQ）实现用户态与内核态的高效通信。

## 核心概念

### 队列对（Queue Pair）

- **SQ (Submission Queue)**: 用户态提交 I/O 请求到内核
- **CQ (Completion Queue)**: 内核返回 I/O 完成结果到用户态
- **SQE (Submission Queue Entry)**: 单个提交项，描述一个 I/O 操作
- **CQE (Completion Queue Entry)**: 单个完成项，包含操作结果

### 优势

| 特性 | 传统 epoll | io_uring |
|------|-----------|----------|
| 通知模型 | 就绪通知（readable/writable） | 完成通知（operation done） |
| 系统调用 | 每次 wait 需要 syscall | 批量提交可绕过 syscall（polling 模式） |
| 文件 I/O | 同步 fallback（aio 限制多） | 真正的异步文件 I/O |
| 缓冲区 | 用户态管理 | 支持 registered buffers（减少拷贝） |

## Rust 生态

### 主要 crate

- `io-uring`: 底层接口，直接映射内核 API
- `tokio-uring`: 基于 io-uring 的异步运行时，与 tokio 兼容

### 条件编译

由于 io_uring 仅 Linux 支持，代码必须使用条件编译：

```rust
#[cfg(all(target_os = "linux", feature = "io-uring"))]
pub mod linux_impl {
    // 真实 io_uring 代码
}

#[cfg(not(all(target_os = "linux", feature = "io-uring")))]
pub mod stub_impl {
    // 占位实现
}
```

## 代码示例

### 文件读取（io-uring crate）

```rust
use io_uring::{IoUring, opcode, types};
use std::os::unix::io::AsRawFd;

fn read_file(path: &str, buf: &mut [u8]) -> std::io::Result<usize> {
    let fd = std::fs::File::open(path)?;
    let mut ring = IoUring::new(8)?;

    let read_e = opcode::Read::new(
        types::Fd(fd.as_raw_fd()),
        buf.as_mut_ptr(),
        buf.len() as u32,
    ).build();

    unsafe {
        ring.submission().push(&read_e)?;
    }

    ring.submit_and_wait(1)?;

    let cqe = ring.completion().next()
        .ok_or_else(|| std::io::Error::other("no cqe"))?;
    Ok(cqe.result() as usize)
}
```

### Echo Server（tokio-uring）

```rust
use tokio_uring::net::TcpListener;

async fn echo_server(addr: &str) -> std::io::Result<()> {
    let listener = TcpListener::bind(addr.parse().unwrap())?;
    loop {
        let (stream, peer) = listener.accept().await?;
        tokio_uring::spawn(async move {
            let mut buf = vec![0u8; 1024];
            let (res, b) = stream.read(buf).await;
            // 处理...
        });
    }
}
```

## 编译与运行

```bash
# Linux 环境下启用 io_uring feature
cargo check -p c10_networks --features io-uring

# 运行示例（Linux only）
cargo run -p c10_networks --example io_uring_demo --features io-uring
```

## 参考

- [Lord of the io_uring](https://unixism.net/loti/)
- [Linux Kernel io_uring 文档](https://kernel.dk/io_uring.pdf)
- [tokio-uring GitHub](https://github.com/tokio-rs/tokio-uring)
