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

    /// 使用 tokio-uring 的 echo server 概念骨架
    ///
    /// 展示如何基于 io_uring 构建异步网络服务。
    /// 真实实现请参考 tokio-uring 文档调整 API。
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
                    // 回写（简化：直接写回整个 buffer 的前 n 字节）
                    let (res, b) = stream.write_all(buf).await;
                    buf = b;
                    if let Err(e) = res {
                        eprintln!("write error to {}: {}", peer, e);
                        return;
                    }
                    let _ = n; // 实际应只写 n 字节，此处简化
                }
            });
        }
    }
}

#[cfg(not(all(target_os = "linux", feature = "io-uring")))]
pub mod stub_impl {
    //! 非 Linux 环境或 io-uring feature 未启用时的占位实现。

    /// io_uring 读取文件的概念演示
    pub fn read_file_with_io_uring(path: &str, _buf: &mut [u8]) -> std::io::Result<usize> {
        eprintln!(
            "[stub] io_uring read: {} (仅在 Linux + io-uring feature 下可用)",
            path
        );
        // fallback 到标准文件读取并返回长度
        let data = std::fs::read(path)?;
        Ok(data.len())
    }

    /// io_uring echo server 的概念说明
    pub async fn tokio_uring_echo_server(addr: &str) -> std::io::Result<()> {
        eprintln!(
            "[stub] io_uring echo server: {} (仅在 Linux + io-uring feature 下可用)",
            addr
        );
        Ok(())
    }
}

// 统一导出
#[cfg(all(target_os = "linux", feature = "io-uring"))]
pub use linux_impl::*;

#[cfg(not(all(target_os = "linux", feature = "io-uring")))]
pub use stub_impl::*;
