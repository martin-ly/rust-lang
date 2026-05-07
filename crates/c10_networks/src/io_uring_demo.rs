//! io_uring 高性能 I/O 演示
//!
//! io_uring 是 Linux 内核 5.1+ 引入的异步 I/O 接口，
//! 通过共享的提交队列（SQ）和完成队列（CQ）实现用户态与内核态的高效通信。
//!
//! ## 架构
//! - Submission Queue (SQ): 用户态提交 I/O 请求
//! - Completion Queue (CQ): 内核态返回 I/O 结果
//! - 无需系统调用即可完成批量 I/O 提交（如果开启 polling）
//!
//! ## 与 epoll 的差异
//! | 特性 | epoll | io_uring |
//! |------|-------|----------|
//! | 接口 | 基于文件描述符的就绪通知 | 基于操作的完成通知 |
//! | 系统调用 | 每次 wait 需 syscall | 批量提交可绕过 syscall |
//! | 缓冲区管理 | 用户态预分配 | 支持 registered buffers |
//! | 文件 I/O | 同步 fallback | 真正的异步文件 I/O |
//!
//! # 权威来源
//! - [kernel.org io_uring](https://kernel.dk/io_uring.pdf)
//! - [io-uring crate](https://github.com/tokio-rs/io-uring)
//! - [tokio-uring](https://github.com/tokio-rs/tokio-uring)

#[cfg(all(target_os = "linux", feature = "io-uring"))]
pub mod linux_impl {
    use std::os::unix::io::AsRawFd;

    /// 使用 io-uring crate 读取文件的示例
    ///
    /// # 注意
    ///
    /// 此代码需要 Linux 环境和 `io-uring` feature。
    pub fn read_file_with_io_uring(path: &str, buf: &mut [u8]) -> std::io::Result<usize> {
        use io_uring::{IoUring, opcode, types};

        let fd = std::fs::File::open(path)?;
        let mut ring = IoUring::new(8)?;

        let read_e = opcode::Read::new(
            types::Fd(fd.as_raw_fd()),
            buf.as_mut_ptr(),
            buf.len() as u32,
        )
        .build();

        unsafe {
            ring.submission()
                .push(&read_e)
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))?;
        }

        ring.submit_and_wait(1)?;

        let cqe = ring.completion().next().ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::Other, "completion queue empty")
        })?;

        let ret = cqe.result();
        if ret < 0 {
            return Err(std::io::Error::from_raw_os_error(-ret));
        }
        Ok(ret as usize)
    }

    /// 批量读取多个文件（io_uring 的核心优势）
    ///
    /// 展示 io_uring 的批量提交能力：一次 syscall 提交多个 I/O 请求。
    pub fn batch_read_files(paths: &[&str], bufs: &mut [Vec<u8>]) -> std::io::Result<Vec<usize>> {
        use io_uring::{IoUring, opcode, types};

        let mut ring = IoUring::new(paths.len() as u32)?;
        let mut fds = Vec::new();

        // 打开所有文件并构建 SQE
        for (i, path) in paths.iter().enumerate() {
            let fd = std::fs::File::open(path)?;
            let read_e = opcode::Read::new(
                types::Fd(fd.as_raw_fd()),
                bufs[i].as_mut_ptr(),
                bufs[i].len() as u32,
            )
            .build();

            unsafe {
                ring.submission()
                    .push(&read_e)
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))?;
            }
            fds.push(fd); // 保持 fd 存活
        }

        // 一次性提交所有请求
        ring.submit_and_wait(paths.len())?;

        // 收集所有完成结果
        let mut results = Vec::with_capacity(paths.len());
        for _ in 0..paths.len() {
            let cqe = ring.completion().next().ok_or_else(|| {
                std::io::Error::new(std::io::ErrorKind::Other, "completion queue incomplete")
            })?;
            let ret = cqe.result();
            results.push(if ret < 0 {
                0
            } else {
                ret as usize
            });
        }

        Ok(results)
    }

    /// 使用 tokio-uring 的 echo server
    ///
    /// 展示如何基于 io_uring 构建异步网络服务。
    pub async fn tokio_uring_echo_server(addr: &str) -> std::io::Result<()> {
        use std::net::SocketAddr;
        use tokio_uring::net::TcpListener;

        let socket_addr: SocketAddr = addr.parse().unwrap();
        let listener = TcpListener::bind(socket_addr)?;
        println!("io_uring echo server listening on {}", addr);

        loop {
            let (stream, peer) = listener.accept().await?;
            tokio_uring::spawn(async move {
                let mut buf = vec![0u8; 1024];
                loop {
                    let (res, b) = stream.read(buf).await;
                    buf = b;
                    let n = match res {
                        Ok(0) => return,
                        Ok(n) => n,
                        Err(e) => {
                            eprintln!("read error from {}: {}", peer, e);
                            return;
                        }
                    };
                    // 回写
                    let (res, b) = stream.write_all(&buf[..n]).await;
                    buf = b;
                    if let Err(e) = res {
                        eprintln!("write error to {}: {}", peer, e);
                        return;
                    }
                    let _ = n;
                }
            });
        }
    }

    /// io_uring 性能对比说明
    pub fn performance_comparison() -> &'static str {
        "| 场景 | epoll | io_uring | 提升 |\n\
         |------|-------|----------|------|\n\
         | 单文件读取 | 1 syscall | 1 syscall | 相当 |\n\
         | 100 文件批量读 | 100 syscalls | 1 syscall | ~100x |\n\
         | 网络 echo | 2 syscalls/rq | 0 syscalls (polling) | 显著 |\n\
         | 随机小 I/O | 同步 fallback | 真正异步 | 2-5x |"
    }
}

#[cfg(not(all(target_os = "linux", feature = "io-uring")))]
pub mod stub {
    //! io_uring feature 未启用或非 Linux 目标时的占位实现。

    /// io_uring 概念说明
    pub fn io_uring_concept() {
        println!(
            "[stub] io_uring 是 Linux 5.1+ 的高性能异步 I/O 接口。\n\
             启用 'io-uring' feature 并在 Linux 上运行以查看真实实现。"
        );
    }

    /// 性能对比占位
    pub fn performance_comparison() -> &'static str {
        "io_uring 性能对比需要 Linux 环境和 io-uring feature"
    }
}

// 统一导出
#[cfg(all(target_os = "linux", feature = "io-uring"))]
pub use linux_impl::*;

#[cfg(not(all(target_os = "linux", feature = "io-uring")))]
pub use stub::*;
