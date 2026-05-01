//! Linux io_uring 高性能 I/O 实战示例
//!
//! 本示例展示 Linux io_uring 接口在 Rust 中的应用，
//! 包括批量读写、零拷贝网络 I/O 和异步文件操作。
//!
//! **平台限制**: 仅 Linux 5.1+ 支持 io_uring。
//!
//! **依赖**: `tokio-uring` 或 `io-uring` crate。
//!
//! 权威来源:
//! - [Cloudflare: io_uring 实践](https://blog.cloudflare.com/io_uring-the-future-of-async/)
//! - [Linux kernel io_uring 文档](https://kernel.dk/io_uring.pdf)
//!
//! 运行方式:
//! ```bash
//! # Linux only
//! cargo run --example io_uring_demo -p c10_networks
//! ```

use std::io;

// ==================== 示例 1: io_uring 基础概念（纯说明） ====================

/// io_uring 核心概念速览
///
/// io_uring 是 Linux 5.1+ 引入的异步 I/O 接口，通过共享内存环形队列
/// 实现用户态与内核态的高效通信，避免传统 epoll + read/write 的系统调用开销。
///
/// ## 核心组件
/// - **Submission Queue (SQ)**: 用户态提交 I/O 请求
/// - **Completion Queue (CQ)**: 内核态返回 I/O 结果
/// - **Ring Buffer**: 共享内存映射，零拷贝传递请求
///
/// ## 与 epoll 的对比
/// | 特性 | epoll | io_uring |
/// |------|-------|----------|
/// | 系统调用次数 | 每次 I/O 需 syscall | batch 后仅需 1 次 syscall |
/// | 数据拷贝 | 内核 ↔ 用户态拷贝 | 支持 registered buffers（零拷贝） |
/// | 异步文件 I/O | 需线程池模拟 | 原生支持（Linux AIO 替代） |
/// | 性能 | 高 | 更高（批处理 + 轮询模式） |
fn io_uring_concepts() {
    println!("--- io_uring 核心概念 ---");
    println!("  io_uring 通过一对共享内存环形队列连接用户态和内核态:");
    println!("  - Submission Queue (SQ): 应用程序提交 I/O 操作");
    println!("  - Completion Queue (CQ): 内核返回操作结果");
    println!("  - 支持批量提交 (batching) 和内核轮询 (IOPOLL/SQPOLL)");
}

// ==================== 示例 2: 使用 `io-uring` crate 的底层 API ====================

#[cfg(target_os = "linux")]
fn demo_io_uring_file_read() -> io::Result<()> {
    use io_uring::{opcode, types, IoUring};
    use std::os::unix::io::AsRawFd;
    use std::fs::File;

    println!("\n--- 示例: io_uring 异步文件读取 ---");

    // 创建 io_uring 实例（默认 32 个队列条目）
    let mut ring = IoUring::new(32)?;

    // 打开文件
    let file = File::open("Cargo.toml")?;
    let fd = types::Fd(file.as_raw_fd());

    // 准备读取缓冲区
    let mut buf = vec![0u8; 1024];

    // 构建 read 操作：从 fd 的偏移量 0 读取到 buf
    let read_op = opcode::Read::new(fd, buf.as_mut_ptr(), buf.len() as u32)
        .offset(0)
        .build();

    // 提交到 SQ
    unsafe {
        let mut sq = ring.submission();
        sq.push(&read_op).expect("submission queue full");
    }

    // 提交并等待至少 1 个完成事件
    ring.submit_and_wait(1)?;

    // 读取 CQ 结果
    let cqe = ring.completion().next().expect("completion queue empty");
    let bytes_read = cqe.result();

    if bytes_read >= 0 {
        let bytes_read = bytes_read as usize;
        println!("  读取 {} bytes", bytes_read);
        println!("  内容预览: {}", String::from_utf8_lossy(&buf[..bytes_read.min(80)]));
    } else {
        println!("  读取失败: errno {}", -bytes_read);
    }

    Ok(())
}

#[cfg(not(target_os = "linux"))]
fn demo_io_uring_file_read() -> io::Result<()> {
    println!("\n--- 示例: io_uring 异步文件读取 ---");
    println!("  [跳过] io_uring 仅在 Linux 上可用");
    Ok(())
}

// ==================== 示例 3: 使用 `tokio-uring` 的高级 API ====================

#[cfg(target_os = "linux")]
fn demo_tokio_uring() -> io::Result<()> {
    use tokio_uring::fs::File;

    println!("\n--- 示例: tokio-uring 异步文件操作 ---");

    tokio_uring::start(async {
        // 异步打开文件
        let file = File::open("Cargo.toml").await?;

        // 异步读取
        let buf = vec![0u8; 1024];
        let (result, buf) = file.read_at(buf, 0).await;
        let bytes_read = result?;

        println!("  tokio-uring 读取 {} bytes", bytes_read);
        println!("  内容预览: {}", String::from_utf8_lossy(&buf[..bytes_read.min(80)]));

        // 异步写入（写入临时文件）
        let temp_path = "/tmp/io_uring_demo_test.txt";
        let write_file = File::create(temp_path).await?;
        let write_buf = b"Hello from io_uring!".to_vec();
        let (result, _) = write_file.write_at(write_buf, 0).await;
        result?;
        println!("  异步写入完成: {}", temp_path);

        // 清理
        let _ = std::fs::remove_file(temp_path);

        Ok(())
    })
}

#[cfg(not(target_os = "linux"))]
fn demo_tokio_uring() -> io::Result<()> {
    println!("\n--- 示例: tokio-uring 异步文件操作 ---");
    println!("  [跳过] tokio-uring 仅在 Linux 上可用");
    Ok(())
}

// ==================== 示例 4: 批量 I/O 提交（Batching） ====================

#[cfg(target_os = "linux")]
fn demo_batch_submission() -> io::Result<()> {
    use io_uring::{opcode, types, IoUring};
    use std::os::unix::io::AsRawFd;
    use std::fs::File;

    println!("\n--- 示例: 批量 I/O 提交 ---");

    let mut ring = IoUring::new(128)?;
    let file = File::open("Cargo.toml")?;
    let fd = types::Fd(file.as_raw_fd());

    // 准备多个缓冲区，执行分散读取 (readv)
    let mut buf1 = vec![0u8; 256];
    let mut buf2 = vec![0u8; 256];
    let mut buf3 = vec![0u8; 256];

    let iovecs = [
        libc::iovec {
            iov_base: buf1.as_mut_ptr() as *mut _,
            iov_len: buf1.len(),
        },
        libc::iovec {
            iov_base: buf2.as_mut_ptr() as *mut _,
            iov_len: buf2.len(),
        },
        libc::iovec {
            iov_base: buf3.as_mut_ptr() as *mut _,
            iov_len: buf3.len(),
        },
    ];

    // 构建 readv 操作
    let readv_op = opcode::Readv::new(fd, iovecs.as_ptr(), iovecs.len() as u32)
        .offset(0)
        .build();

    unsafe {
        let mut sq = ring.submission();
        sq.push(&readv_op).unwrap();
    }

    ring.submit_and_wait(1)?;

    let cqe = ring.completion().next().unwrap();
    let total = cqe.result();

    if total >= 0 {
        println!("  批量读取总字节数: {}", total);
        println!("  缓冲区 1 预览: {:?}", String::from_utf8_lossy(&buf1[..80.min(buf1.len())]));
    }

    Ok(())
}

#[cfg(not(target_os = "linux"))]
fn demo_batch_submission() -> io::Result<()> {
    println!("\n--- 示例: 批量 I/O 提交 ---");
    println!("  [跳过] 仅在 Linux 上可用");
    Ok(())
}

// ==================== 示例 5: 性能优化技巧 ====================

fn io_uring_performance_tips() {
    println!("\n--- io_uring 性能优化技巧 ---");

    println!("  1. 批量提交 (Batching):");
    println!("     尽量将多个 I/O 操作一次性提交到 SQ，减少系统调用次数");

    println!("  2. 注册文件描述符 (Registered FDs):");
    println!("     使用 IORING_REGISTER_FILES 避免每次操作都进行 fd 查找");

    println!("  3. 注册缓冲区 (Registered Buffers):");
    println!("     使用 IORING_REGISTER_BUFFERS 实现内核态零拷贝");

    println!("  4. 内核轮询模式 (SQPOLL):");
    println!("     让内核线程轮询 SQ，完全消除提交时的系统调用");

    println!("  5. 忙等待完成 (IOPOLL):");
    println!("     对块设备 I/O 使用忙等待，绕过中断");

    println!("  6. 链接操作 (Linked Operations):");
    println!("     使用 IOSQE_IO_LINK 将多个操作链接为原子序列");

    println!("  7. 多路复用完成事件:");
    println!("     使用 IORING_OP_POLL_ADD 将 epoll 行为整合到 io_uring");
}

// ==================== 示例 6: io_uring vs epoll 代码对比 ====================

/// 传统的 epoll + read 伪代码
fn _traditional_epoll_pseudo_code() {
    println!("\n--- 传统 epoll 伪代码 ---");
    println!("  loop {{");
    println!("      epoll_wait(epfd, events, ...);  // syscall 1");
    println!("      for event in events {{");
    println!("          read(fd, buf, ...);          // syscall 2 per event");
    println!("          process(buf);");
    println!("      }}");
    println!("  }}");
}

/// io_uring 批处理伪代码
fn _io_uring_pseudo_code() {
    println!("\n--- io_uring 批处理伪代码 ---");
    println!("  loop {{");
    println!("      for fd in interested_fds {{");
    println!("          sq.push(Read {{ fd, buf }});   // 用户态操作，无 syscall");
    println!("      }}");
    println!("      io_uring_enter();                 // syscall 1 (批量提交)");
    println!("      for cqe in cq {{");
    println!("          process(cqe.buf);");
    println!("      }}");
    println!("  }}");
}

// ==================== 主演示函数 ====================

fn main() -> io::Result<()> {
    println!("🐧 Linux io_uring 高性能 I/O 实战演示\n");

    io_uring_concepts();
    _traditional_epoll_pseudo_code();
    _io_uring_pseudo_code();

    demo_io_uring_file_read()?;
    demo_tokio_uring()?;
    demo_batch_submission()?;
    io_uring_performance_tips();

    println!("\n✅ io_uring 演示完成！");
    println!("   关键要点:");
    println!("   - io_uring 是 Linux 下最高效的异步 I/O 接口");
    println!("   - 批处理 + 共享内存环形队列 = 极低的系统调用开销");
    println!("   - tokio-uring 提供了安全的 Rust 抽象层");
    println!("   - 生产环境推荐结合 SQPOLL + registered buffers");

    Ok(())
}
