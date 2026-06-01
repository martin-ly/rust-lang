//! io_uring 深度实践 —— Linux 高性能异步 I/O
//! io_uring —— Linux performance async I/O
//! io_uring 深度实践 —— Linux 高performanceasync I/O
//! # 概述
//! #
//! # 核心概念
//! # core concept
//! ## 队列对（Queue Pair）
//! ## 队列to（Queue Pair）
//! - **Submission Queue (SQ)**: 用户态提交 I/O 请求，内核消费
//! - **Submission Queue (SQ)**: I/O ，kernel
//! - **Completion Queue (CQ)**: 内核返回 I/O 结果，用户态消费
//! - **Completion Queue (CQ)**: kernel I/O result ，
//! ## 优势对比
//! ## strength to
//! | 特性 | epoll | io_uring |
//! | 接口语义 | 就绪通知（readiness） | 完成通知（completion） |
//! | | （readiness） | （completion） |
//! | 接口语义 | 就绪Notify（readiness） | 完成Notify（completion） |
//! | 系统调用 | epoll_ctl + epoll_wait | io_uring_enter（可批量） |
//! | 文件 I/O | 同步 fallback（阻塞） | 真正异步 |
//! | I/O | synchronous fallback（） | async |
//! | 文件 I/O | synchronous fallback（Block） | 真正async |
//! | 批处理 | 逐个处理 | 批量提交/收割 |
//! | | | / |
//! | 零拷贝 | 不支持 | 支持（registered buffers） |
//! | 零拷贝 | 不Supports | Supports（registered buffers） |
//! |  polling 模式 | 不支持 | 支持（绕过 syscall） |
//! | polling | | （ syscall） |
//! | polling 模式 | 不Supports | Supports（绕过 syscall） |
//! # 前置条件
//! # before condition
//! - Linux 内核 5.1+（建议 5.10+ 以获得完整特性）
//! - Linux kernel 5.1+（ 5.10+ complete feature ）
//! - Linux kernel 5.1+（建议 5.10+ 以获得completefeature）
//! - 启用 `io-uring` feature: `cargo build -p c10_networks --features io-uring`
//! # 参考
//! # reference
//! - [io_uring PDF](https://kernel.dk/io_uring.pdf) — Jens Axboe 原始论文

#[cfg(all(target_os = "linux", feature = "io-uring"))]
pub mod linux_impl {
    use io_uring::{CompletionQueue, IoUring, SubmissionQueue, opcode, types};
    use std::os::unix::io::AsRawFd;

    // =========================================================================
    // 1. 基础文件 I/O
    // =========================================================================

    /// 异步读取整个文件到 `Vec<u8>`
    /// async to `Vec<u8>`
    /// 1. 打开文件
    /// 1.
    /// 2. 构建 Read SQE (Submission Queue Entry)
    /// 3. 提交并等待完成
    /// 3. and etc.
    /// 4. 处理 CQE (Completion Queue Entry)
    pub fn read_file_full(path: &str) -> std::io::Result<Vec<u8>> {
        let file = std::fs::File::open(path)?;
        let file_size = file.metadata()?.len() as usize;
        let mut buf = vec![0u8; file_size];

        let mut ring = IoUring::new(8)?;

        let read_op = opcode::Read::new(
            types::Fd(file.as_raw_fd()),
            buf.as_mut_ptr(),
            buf.len() as u32,
        )
        .build();

        unsafe {
            ring.submission()
                .push(&read_op)
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))?;
        }

        // 提交并等待至少 1 个完成
        ring.submit_and_wait(1)?;

        let cqe = ring.completion().next().ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::UnexpectedEof, "no completion")
        })?;

        let ret = cqe.result();
        if ret < 0 {
            return Err(std::io::Error::from_raw_os_error(-ret));
        }

        buf.truncate(ret as usize);
        Ok(buf)
    }

    /// 异步写入文件
    /// async
    pub fn write_file_full(path: &str, data: &[u8]) -> std::io::Result<usize> {
        use std::fs::OpenOptions;

        let file = OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(path)?;
        let mut ring = IoUring::new(8)?;

        let write_op = opcode::Write::new(
            types::Fd(file.as_raw_fd()),
            data.as_ptr(),
            data.len() as u32,
        )
        .build();

        unsafe {
            ring.submission()
                .push(&write_op)
                .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))?;
        }

        ring.submit_and_wait(1)?;

        let cqe = ring
            .completion()
            .next()
            .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::Other, "no completion"))?;

        let ret = cqe.result();
        if ret < 0 {
            return Err(std::io::Error::from_raw_os_error(-ret));
        }
        Ok(ret as usize)
    }

    // =========================================================================
    // 2. 批量 I/O（批处理模式）
    // =========================================================================

    /// 批量读取多个文件
    /// io_uring corestrength：一次 `submit()` 提交多个操作，
    /// 减少用户态/内核态上下文切换。
    /// /kernel on under switching 。
    pub fn read_multiple_files(paths: &[&str]) -> Vec<std::io::Result<Vec<u8>>> {
        let mut ring = IoUring::new(paths.len() as u32 * 2).expect("create ring");
        let mut files = Vec::new();
        let mut buffers = Vec::new();

        // 阶段 1：构建所有 SQE
        unsafe {
            let mut sq = ring.submission();
            for path in paths {
                match std::fs::File::open(path) {
                    Ok(file) => {
                        let size = file.metadata().map(|m| m.len() as usize).unwrap_or(4096);
                        let mut buf = vec![0u8; size];
                        let op = opcode::Read::new(
                            types::Fd(file.as_raw_fd()),
                            buf.as_mut_ptr(),
                            buf.len() as u32,
                        )
                        .build();

                        if sq.push(&op).is_ok() {
                            files.push(Some(file)); // 保持文件存活
                            buffers.push(buf);
                        } else {
                            files.push(None);
                            buffers.push(Vec::new());
                        }
                    }
                    Err(e) => {
                        files.push(None);
                        buffers.push(Vec::new());
                    }
                }
            }
        }

        // 阶段 2：单次提交所有操作
        if let Err(e) = ring.submit() {
            return vec![Err(e); paths.len()];
        }

        // 阶段 3：收割所有完成
        let mut results = Vec::new();
        for buf in buffers {
            if buf.is_empty() {
                results.push(Err(std::io::Error::new(
                    std::io::ErrorKind::Other,
                    "skipped",
                )));
                continue;
            }

            match ring.completion().next() {
                Some(cqe) => {
                    let ret = cqe.result();
                    if ret < 0 {
                        results.push(Err(std::io::Error::from_raw_os_error(-ret)));
                    } else {
                        let mut b = buf;
                        b.truncate(ret as usize);
                        results.push(Ok(b));
                    }
                }
                None => {
                    results.push(Err(std::io::Error::new(
                        std::io::ErrorKind::UnexpectedEof,
                        "missing completion",
                    )));
                }
            }
        }

        results
    }

    // =========================================================================
    // 3. Registered Buffers（零拷贝优化）
    // =========================================================================

    /// 使用注册缓冲区减少内存拷贝
    /// buffering memory
    pub struct RegisteredBufferPool {
        ring: IoUring,
        buffers: Vec<Vec<u8>>,
    }

    impl RegisteredBufferPool {
        pub fn new(buffer_count: usize, buffer_size: usize) -> std::io::Result<Self> {
            let ring = IoUring::new(buffer_count as u32 * 2)?;
            let buffers: Vec<Vec<u8>> = (0..buffer_count).map(|_| vec![0u8; buffer_size]).collect();

            // 注册缓冲区到内核
            let slice_refs: Vec<&[u8]> = buffers.iter().map(|b| b.as_slice()).collect();
            unsafe {
                ring.submitter()
                    .register_buffers(&slice_refs)
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))?;
            }

            Ok(Self { ring, buffers })
        }

        pub fn read_with_registered_buf(
            &mut self,
            fd: std::fs::File,
            buf_index: usize,
        ) -> std::io::Result<usize> {
            if buf_index >= self.buffers.len() {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    "buffer index out of range",
                ));
            }

            let op = opcode::ReadFixed::new(
                types::Fd(fd.as_raw_fd()),
                self.buffers[buf_index].as_mut_ptr(),
                self.buffers[buf_index].len() as u32,
                buf_index as u16,
            )
            .build();

            unsafe {
                self.ring
                    .submission()
                    .push(&op)
                    .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))?;
            }

            self.ring.submit_and_wait(1)?;

            let cqe = self.ring.completion().next().ok_or_else(|| {
                std::io::Error::new(std::io::ErrorKind::UnexpectedEof, "no completion")
            })?;

            let ret = cqe.result();
            if ret < 0 {
                Err(std::io::Error::from_raw_os_error(-ret))
            } else {
                Ok(ret as usize)
            }
        }

        pub fn buffer(&self, index: usize) -> Option<&[u8]> {
            self.buffers.get(index).map(|b| b.as_slice())
        }
    }

    // =========================================================================
    // 4. 性能基准对比框架
    // =========================================================================

    /// io_uring vs 同步 I/O 性能对比（概念框架）
    /// io_uring vs synchronous I/O performance to （concept framework ）
    /// 实际基准测试应使用 `criterion` crate。
    /// actual benchmark `criterion` crate。
    pub struct IoUringBenchmark;

    impl IoUringBenchmark {
        /// 同步顺序读取
        /// synchronous order
        pub fn sync_sequential_read(path: &str, chunk_size: usize) -> std::io::Result<usize> {
            use std::io::Read;
            let mut file = std::fs::File::open(path)?;
            let mut buf = vec![0u8; chunk_size];
            let mut total = 0;
            loop {
                let n = file.read(&mut buf)?;
                if n == 0 {
                    break;
                }
                total += n;
            }
            Ok(total)
        }

        /// io_uring 并发读取（概念）
        /// io_uring concurrency （concept ）
        /// 通过链接 SQE（Linked SQE）实现流水线化 I/O。
        /// SQE（Linked SQE）pipeline I/O。
        pub fn io_uring_linked_reads(path: &str) -> std::io::Result<usize> {
            // 链接操作概念：Read → Process → Write 链
            // 实际实现需根据具体业务调整
            let data = read_file_full(path)?;
            Ok(data.len())
        }
    }
}

// =========================================================================
// 非 Linux 平台的占位实现
// =========================================================================

#[cfg(not(all(target_os = "linux", feature = "io-uring")))]
pub mod linux_impl {
    use std::io;

    pub fn read_file_full(_path: &str) -> io::Result<Vec<u8>> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "io_uring requires Linux with 'io-uring' feature enabled",
        ))
    }

    pub fn write_file_full(_path: &str, _data: &[u8]) -> io::Result<usize> {
        Err(io::Error::new(
            io::ErrorKind::Unsupported,
            "io_uring requires Linux with 'io-uring' feature enabled",
        ))
    }

    pub fn read_multiple_files(_paths: &[&str]) -> Vec<io::Result<Vec<u8>>> {
        vec![]
    }

    pub struct RegisteredBufferPool;

    impl RegisteredBufferPool {
        pub fn new(_count: usize, _size: usize) -> io::Result<Self> {
            Err(io::Error::new(
                io::ErrorKind::Unsupported,
                "io_uring requires Linux with 'io-uring' feature enabled",
            ))
        }
    }
}

// 统一导出
pub use linux_impl::*;
