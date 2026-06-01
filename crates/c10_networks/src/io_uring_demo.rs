//! io_uring 高性能 I/O 演示
//! io_uring high performance I/O demonstration
//! io_uring performance I/O demonstration
//! io_uring 高performance I/O Demonstration of
//! 通过共享的提交队列（SQ）和完成队列（CQ）实现用户态与内核态的高效通信。
//! queue （SQ）and complete queue （CQ）and kernel efficient 。
//! （SQ）and （CQ）and kernel efficient 。
//! ## 架构
//! ## architecture
//! - Submission Queue (SQ): 用户态提交 I/O 请求
//! - Completion Queue (CQ): 内核态返回 I/O 结果
//! - 无需系统调用即可完成批量 I/O 提交（如果开启 polling）
//! - system complete I/O （if polling）
//! - system I/O （if polling）
//! ## and epoll 差异
//! | 特性 | epoll | io_uring |
//! | 接口 | 基于文件描述符的就绪通知 | 基于操作的完成通知 |
//! | | file descriptor notify | operation complete notify |
//! | | file descriptor | |
//! | 系统调用 | 每次 wait 需 syscall | 批量提交可绕过 syscall |
//! | system | wait syscall | syscall |
//! | 缓冲区管理 | 用户态预分配 | 支持 registered buffers |
//! | buffering | | registered buffers |
//! # 权威来源
//! # Source
//! # 权威source
//! - [tokio-uring](https://github.com/tokio-rs/tokio-uring)

#[cfg(all(target_os = "linux", feature = "io-uring"))]
pub mod linux_impl {
    use std::os::unix::io::AsRawFd;

    /// # 注意
    /// #
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
            results.push(if ret < 0 { 0 } else { ret as usize });
        }

        Ok(results)
    }

    /// 展示如何基于 io_uring 构建异步网络服务。
    /// io_uring async network 。
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

    /// 使用 Registered Buffers（固定缓冲区）
    /// 这对高频小 I/O 场景（如数据库、缓存）有显著性能提升。
    /// to high I/O scenario （database 、cache ）significant performance 。
    /// to I/O scenario （database 、）significant performance 。
    pub fn registered_buffers_concept() -> &'static str {
        r#"
// 1. 注册缓冲区池
let mut buf_pool = vec![vec![0u8; 4096]; 128];
let mut iovecs: Vec<_> = buf_pool.iter_mut()
    .map(|b| libc::iovec { iov_base: b.as_mut_ptr() as _, iov_len: b.len() })
    .collect();

// 2. 向内核注册（只需一次）
ring.submitter()
    .register_buffers(&iovecs)
    .expect("register buffers failed");

// 3. 使用 REGISTERED_BUFFER 标志提交 I/O
let read_e = opcode::Read::new(fd, buf_ptr, buf_len)
    .buf_index(buf_index) // 使用已注册缓冲区的索引
    .build();
"#
    }

    /// 操作链（Linked Operations）
    /// 前一个操作完成后自动触发下一个，无需用户态干预。
    /// before operation complete after under ，。
    /// before after under ，。
    pub fn linked_operations_concept() -> &'static str {
        r#"
// 链式操作：先打开文件，然后读取，最后关闭
// 所有操作按顺序自动执行

let open_e = opcode::OpenAt::new(dir_fd, path.as_ptr())
    .flags(libc::O_RDONLY)
    .build()
    .user_data(1);

let read_e = opcode::Read::new(types::Fd(0), buf.as_mut_ptr(), buf.len() as _)
    .build()
    .flags(squeue::Flags::IO_LINK) // 链接到前一个操作
    .user_data(2);

let close_e = opcode::Close::new(types::Fd(0))
    .build()
    .flags(squeue::Flags::IO_LINK)
    .user_data(3);
"#
    }

    /// io_uring and epoll 决策tree
    pub fn when_to_use_io_uring() -> &'static str {
        r#"
何时使用 io_uring？

1. 你的应用是 I/O 密集型的？
   ├── 否 → 使用 epoll 或同步 I/O 即可
   └── 是 → 继续 2

2. 主要 I/O 类型？
   ├── 网络 I/O（大量连接）→ io_uring (polling mode) 或 epoll
   ├── 文件 I/O（批量读写）→ io_uring (核心优势)
   └── 混合 I/O → io_uring (统一接口)

3. 目标平台？
   ├── Linux 5.19+（支持 multi-shot accept/recv）→ io_uring 首选
   ├── Linux 5.10+（基础功能完整）→ io_uring 可用
   ├── Linux 5.1+（基础支持）→ io_uring 有限功能
   └── 非 Linux → 不可用（使用 epoll/kqueue/IOCP）

4. 是否需要可移植性？
   ├── 是 → 使用 Tokio（底层自动选择 epoll/io_uring/kqueue/IOCP）
   └── 否（仅 Linux）→ 直接使用 io-uring crate
"#
    }
    /// io_uring 性能对比说明
    /// io_uring performance to explain
    pub fn performance_comparison() -> &'static str {
        "| 场景 | epoll | io_uring | 提升 |\n|------|-------|----------|------|\n| 单文件读取 | 1 \
         syscall | 1 syscall | 相当 |\n| 100 文件批量读 | 100 syscalls | 1 syscall | ~100x |\n| \
         网络 echo | 2 syscalls/rq | 0 syscalls (polling) | 显著 |\n| 随机小 I/O | 同步 fallback | \
         真正异步 | 2-5x |"
    }
}

#[cfg(not(all(target_os = "linux", feature = "io-uring")))]
pub mod stub {

    /// io_uring 概念说明
    /// io_uring concept explain
    pub fn io_uring_concept() {
        println!(
            "[stub] io_uring 是 Linux 5.1+ 的高性能异步 I/O 接口。\n启用 'io-uring' feature 并在 \
             Linux 上运行以查看真实实现。"
        );
    }

    /// 性能对比占位
    /// performance to
    pub fn performance_comparison() -> &'static str {
        "io_uring 性能对比需要 Linux 环境和 io-uring feature"
    }
}

// 统一导出
#[cfg(all(target_os = "linux", feature = "io-uring"))]
pub use linux_impl::*;

#[cfg(not(all(target_os = "linux", feature = "io-uring")))]
pub use stub::*;
