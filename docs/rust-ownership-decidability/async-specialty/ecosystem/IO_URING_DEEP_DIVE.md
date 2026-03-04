# io_uring 深度解析 - Linux异步IO的未来

> 从原理到实战：全面掌握io_uring生态

---

## 1. io_uring 原理

### 1.1 传统IO的问题

```text
传统epoll模式:
┌──────────┐     ┌──────────┐     ┌──────────┐
│ 用户空间  │     │ 系统调用  │     │ 内核空间  │
│          │     │          │     │          │
│ read()   │────→│ syscall  │────→│ 文件系统  │
│          │     │          │     │          │
│ ◄────────│     │ ◄────────│     │ 磁盘IO   │
│ 数据拷贝  │     │ 上下文切换│     │          │
└──────────┘     └──────────┘     └──────────┘

问题:
1. 每次IO都需要syscall (开销~1-2μs)
2. 数据需要从内核拷贝到用户空间
3. 上下文切换开销
```

### 1.2 io_uring 架构

```text
io_uring 架构:
┌─────────────────────────────────────────────────────────┐
│                     用户空间                              │
│  ┌──────────────┐    ┌──────────────┐    ┌───────────┐ │
│  │   Producer   │    │   Consumer   │    │  Shared   │ │
│  │   (应用线程)  │    │   (应用线程)  │    │  Memory   │ │
│  └───────┬──────┘    └───────┬──────┘    └─────┬─────┘ │
│          │                   │                 │        │
│          ▼                   ▼                 ▼        │
│  ┌──────────────────────────────────────────────────┐  │
│  │  Submission Queue (SQ)  │  Completion Queue (CQ) │  │
│  │  ┌─────────────────┐   │  ┌─────────────────┐    │  │
│  │  │ sqe[0]          │   │  │ cqe[0]          │    │  │
│  │  │ sqe[1]          │   │  │ cqe[1]          │    │  │
│  │  │ ...             │   │  │ ...             │    │  │
│  │  │ sqe[MASK]       │   │  │ cqe[MASK]       │    │  │
│  │  └─────────────────┘   │  └─────────────────┘    │  │
│  │         ▲              │         │               │  │
│  │         │              │         ▼               │  │
│  │  Tail (写入位置)        │  Head (读取位置)         │  │
│  └─────────┼──────────────┴─────────┼───────────────┘  │
└───────────┼────────────────────────┼──────────────────┘
            │                        │
            │ io_uring_enter()       │ 完成事件
            │ (批量提交)              │ (通过CQ)
            ▼                        ▼
┌─────────────────────────────────────────────────────────┐
│                     内核空间                              │
│  ┌──────────────────────────────────────────────────┐   │
│  │              io_uring 子系统                        │   │
│  │  ┌─────────────┐    ┌─────────────┐              │   │
│  │  │  工作队列    │    │  完成处理    │              │   │
│  │  │  (批量IO)   │    │  (回调/唤醒) │              │   │
│  │  └──────┬──────┘    └──────┬──────┘              │   │
│  │         │                  │                      │   │
│  │         ▼                  ▼                      │   │
│  │  ┌───────────────────────────────────────────┐   │   │
│  │  │        块层 / 网络层 / 文件系统            │   │   │
│  │  └───────────────────────────────────────────┘   │   │
│  └──────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────┘

优势:
1. 批量提交 (减少syscall次数)
2. 共享内存 (mmap, 零拷贝)
3. 轮询模式 (完全无syscall)
4. 统一接口 (文件+网络+...)
```

### 1.3 核心数据结构

```rust
// io_uring Submission Queue Entry
#[repr(C)]
pub struct io_uring_sqe {
    pub opcode: u8,        // 操作码 (READ, WRITE, ACCEPT, ...)
    pub flags: u8,         // 标志位
    pub ioprio: u16,       // IO优先级
    pub fd: i32,           // 文件描述符
    pub off: u64,          // 偏移量
    pub addr: u64,         // 用户缓冲区地址
    pub len: u32,          // 长度
    pub rw_flags: u32,     // 读写标志
    pub user_data: u64,    // 用户数据 (标识请求)
    pub buf_index: u16,    // 缓冲区索引 (高级特性)
    pub personality: u16,  // 用户标识
    pub splice_fd_in: i32, // splice用
    pub __pad: [u64; 2],   // 对齐填充
}

// io_uring Completion Queue Entry
#[repr(C)]
pub struct io_uring_cqe {
    pub user_data: u64,    // 对应sqe的user_data
    pub res: i32,          // 结果 (>=0成功, <0错误码)
    pub flags: u32,        // 标志位
}

// 操作码枚举
pub const IORING_OP_NOP: u8 = 0;
pub const IORING_OP_READV: u8 = 1;
pub const IORING_OP_WRITEV: u8 = 2;
pub const IORING_OP_FSYNC: u8 = 3;
pub const IORING_OP_READ_FIXED: u8 = 4;
pub const IORING_OP_WRITE_FIXED: u8 = 5;
pub const IORING_OP_POLL_ADD: u8 = 6;
pub const IORING_OP_POLL_REMOVE: u8 = 7;
pub const IORING_OP_SYNC_FILE_RANGE: u8 = 8;
pub const IORING_OP_SENDMSG: u8 = 9;
pub const IORING_OP_RECVMSG: u8 = 10;
pub const IORING_OP_TIMEOUT: u8 = 11;
pub const IORING_OP_TIMEOUT_REMOVE: u8 = 12;
pub const IORING_OP_ACCEPT: u8 = 13;
pub const IORING_OP_ASYNC_CANCEL: u8 = 14;
pub const IORING_OP_LINK_TIMEOUT: u8 = 15;
pub const IORING_OP_CONNECT: u8 = 16;
pub const IORING_OP_FALLOCATE: u8 = 17;
pub const IORING_OP_OPENAT: u8 = 18;
pub const IORING_OP_CLOSE: u8 = 19;
// ... 更多操作码
```

---

## 2. 原生io_uring使用

### 2.1 基本API

```rust
use libc::*;
use std::os::unix::io::RawFd;
use std::ptr::{null, null_mut};

// io_uring 设置
pub struct IoUring {
    fd: RawFd,
    sq: SubmissionQueue,
    cq: CompletionQueue,
    sqes: *mut io_uring_sqe,
}

impl IoUring {
    /// 创建io_uring实例
    pub fn new(entries: u32, flags: u32) -> io::Result<Self> {
        unsafe {
            let fd = io_uring_setup(entries, &mut params)?;

            // mmap共享内存区域
            let sq_ptr = mmap(
                null_mut(),
                sq_len,
                PROT_READ | PROT_WRITE,
                MAP_SHARED | MAP_POPULATE,
                fd,
                IORING_OFF_SQ_RING as off_t,
            );

            let cq_ptr = mmap(
                null_mut(),
                cq_len,
                PROT_READ | PROT_WRITE,
                MAP_SHARED | MAP_POPULATE,
                fd,
                IORING_OFF_CQ_RING as off_t,
            );

            let sqes = mmap(
                null_mut(),
                sqe_len,
                PROT_READ | PROT_WRITE,
                MAP_SHARED | MAP_POPULATE,
                fd,
                IORING_OFF_SQES as off_t,
            ) as *mut io_uring_sqe;

            Ok(IoUring { fd, sq, cq, sqes })
        }
    }

    /// 获取SQE (Submission Queue Entry)
    pub fn get_sqe(&mut self) -> Option<&mut io_uring_sqe> {
        let next = self.sq.tail.wrapping_add(1);
        let head = self.sq.head.load(atomic::Ordering::Acquire);

        if next - head > self.sq.ring_entries {
            return None; // SQ已满
        }

        let idx = self.sq.tail & self.sq.ring_mask;
        let sqe = unsafe { &mut *self.sqes.add(idx as usize) };

        self.sq.tail = next;
        Some(sqe)
    }

    /// 提交SQE到内核
    pub fn submit(&self) -> io::Result<usize> {
        unsafe {
            let ret = io_uring_enter(
                self.fd,
                to_submit,      // 提交数量
                min_complete,   // 等待完成数量
                flags,          // 标志
                sigset,         // 信号集
            );

            if ret < 0 {
                return Err(io::Error::last_os_error());
            }
            Ok(ret as usize)
        }
    }

    /// 获取CQE (Completion Queue Entry)
    pub fn peek_cqe(&self) -> Option<&io_uring_cqe> {
        let head = self.cq.head.load(atomic::Ordering::Acquire);
        let tail = self.cq.tail.load(atomic::Ordering::Acquire);

        if head == tail {
            return None; // CQ为空
        }

        let idx = head & self.cq.ring_mask;
        let cqe = unsafe { &*self.cq.cqes.add(idx as usize) };

        Some(cqe)
    }

    /// 标记CQE已消费
    pub fn cqe_seen(&self) {
        self.cq.head.fetch_add(1, atomic::Ordering::Release);
    }
}
```

### 2.2 文件IO示例

```rust
use std::fs::OpenOptions;
use std::os::unix::io::AsRawFd;

fn io_uring_file_read() -> io::Result<()> {
    let mut ring = IoUring::new(32, 0)?;

    // 打开文件
    let file = OpenOptions::new().read(true).open("data.txt")?;
    let fd = file.as_raw_fd();

    // 准备缓冲区
    let mut buf = vec![0u8; 4096];

    // 获取SQE并设置读取操作
    let sqe = ring.get_sqe().ok_or(io::Error::new(
        io::ErrorKind::Other,
        "submission queue full"
    ))?;

    unsafe {
        // 清零SQE
        std::ptr::write_bytes(sqe, 0, 1);

        sqe.opcode = IORING_OP_READ;
        sqe.fd = fd;
        sqe.addr = buf.as_mut_ptr() as u64;
        sqe.len = buf.len() as u32;
        sqe.off = 0; // 从文件开头读取
        sqe.user_data = 0x1234; // 用户标识
    }

    // 提交到内核
    ring.submit()?;

    // 等待完成
    loop {
        ring.submit_and_wait(1)?;

        if let Some(cqe) = ring.peek_cqe() {
            if cqe.user_data == 0x1234 {
                if cqe.res < 0 {
                    return Err(io::Error::from_raw_os_error(-cqe.res));
                }
                println!("Read {} bytes", cqe.res);
                ring.cqe_seen();
                break;
            }
        }
    }

    Ok(())
}
```

### 2.3 网络IO示例

```rust
/// io_uring TCP服务器
fn io_uring_tcp_server() -> io::Result<()> {
    let mut ring = IoUring::new(256, IORING_SETUP_SQPOLL)?; // 启用内核轮询

    // 创建监听socket
    let listener = TcpListener::bind("0.0.0.0:8080")?;
    listener.set_nonblocking(true)?;
    let listen_fd = listener.as_raw_fd();

    // 提交accept操作
    let mut client_addr: sockaddr_in = unsafe { std::mem::zeroed() };
    let mut addr_len = std::mem::size_of::<sockaddr_in>() as u32;

    let sqe = ring.get_sqe().unwrap();
    unsafe {
        std::ptr::write_bytes(sqe, 0, 1);
        sqe.opcode = IORING_OP_ACCEPT;
        sqe.fd = listen_fd;
        sqe.addr = &mut client_addr as *mut _ as u64;
        sqe.off = &mut addr_len as *mut _ as u64;
        sqe.user_data = 1; // accept标识
    }
    ring.submit()?;

    // 事件循环
    loop {
        ring.submit_and_wait(1)?;

        while let Some(cqe) = ring.peek_cqe() {
            match cqe.user_data {
                1 => {
                    // Accept完成
                    let client_fd = cqe.res;
                    if client_fd < 0 {
                        eprintln!("Accept error: {}", -client_fd);
                    } else {
                        println!("New connection: {}", client_fd);
                        // 提交recv操作...
                    }
                    ring.cqe_seen();

                    // 提交新的accept
                    let sqe = ring.get_sqe().unwrap();
                    // ...
                }
                2 => {
                    // Recv完成
                    // ...
                }
                3 => {
                    // Send完成
                    // ...
                }
                _ => {}
            }
        }
    }
}
```

---

## 3. 高级特性

### 3.1 轮询模式 (SQPOLL)

```rust
/// 内核轮询模式 - 完全绕过syscall
fn sqpoll_mode() -> io::Result<()> {
    // IORING_SETUP_SQPOLL: 内核线程轮询SQ
    // IORING_SETUP_SQ_AFF: 绑定SQ线程到特定CPU
    let flags = IORING_SETUP_SQPOLL | IORING_SETUP_SQ_AFF;

    let mut ring = IoUring::new(4096, flags)?;

    // 设置SQ线程空闲超时 (ms)
    // 0 = 永不睡眠
    ring.params.sq_thread_idle = 1000;

    // 现在提交只需要内存操作，无需syscall!
    loop {
        // 填充SQE...

        // 只需更新tail指针，内核自动检测
        ring.sq.tail.store(new_tail, Release);

        // 无需io_uring_enter!
    }
}
```

### 3.2 注册缓冲区 (Registered Buffers)

```rust
/// 预注册缓冲区 - 避免每次IO的内存注册开销
fn registered_buffers() -> io::Result<()> {
    let mut ring = IoUring::new(256, 0)?;

    // 预分配缓冲区池
    let mut buffers: Vec<Vec<u8>> = (0..16)
        .map(|_| vec![0u8; 4096])
        .collect();

    // 注册到内核
    let iovecs: Vec<iovec> = buffers
        .iter_mut()
        .map(|buf| iovec {
            iov_base: buf.as_mut_ptr() as *mut c_void,
            iov_len: buf.len(),
        })
        .collect();

    unsafe {
        io_uring_register_buffers(
            ring.fd,
            iovecs.as_ptr(),
            iovecs.len() as u32,
        )?;
    }

    // 现在可以使用READ_FIXED/WRITE_FIXED
    let sqe = ring.get_sqe().unwrap();
    unsafe {
        sqe.opcode = IORING_OP_READ_FIXED;
        sqe.fd = file_fd;
        sqe.addr = 0; // 不使用，使用buf_index
        sqe.len = 4096;
        sqe.buf_index = 0; // 使用第0个注册缓冲区
    }

    Ok(())
}
```

### 3.3 IO链路与超时

```rust
/// 链接多个IO操作
fn linked_operations() -> io::Result<()> {
    let mut ring = IoUring::new(32, 0)?;

    // 操作1: 打开文件
    let sqe1 = ring.get_sqe().unwrap();
    unsafe {
        sqe1.opcode = IORING_OP_OPENAT;
        sqe1.addr = "file.txt".as_ptr() as u64;
        sqe1.len = 7;
        sqe1.flags = IOSQE_IO_LINK; // 链接到下一个操作
        sqe1.user_data = 1;
    }

    // 操作2: 读取 (依赖操作1的文件描述符)
    let sqe2 = ring.get_sqe().unwrap();
    unsafe {
        sqe2.opcode = IORING_OP_READ;
        sqe2.fd = 0; // 将由CQE返回
        sqe2.addr = buf.as_mut_ptr() as u64;
        sqe2.len = 4096;
        sqe2.flags = IOSQE_IO_LINK;
        sqe2.user_data = 2;
    }

    // 操作3: 超时 (整个链路的超时)
    let sqe3 = ring.get_sqe().unwrap();
    unsafe {
        sqe3.opcode = IORING_OP_LINK_TIMEOUT;
        sqe3.addr = &timespec { tv_sec: 5, tv_nsec: 0 } as *const _ as u64;
        sqe3.user_data = 3;
    }

    ring.submit()?;

    // 如果任一操作失败，整个链路中止
    Ok(())
}
```

---

## 4. 性能对比

### 4.1 基准测试结果

```text
文件IO性能 (4KB随机读取, IOPS):
┌─────────────────┬────────────┬────────────┬────────────┐
│     模式        │  sync      │  aio       │ io_uring   │
├─────────────────┼────────────┼────────────┼────────────┤
│ 单线程          │ 50K        │ 80K        │ 150K       │
│ 多线程          │ 200K       │ 300K       │ 1M+        │
│ SQPOLL轮询      │ -          │ -          │ 2M+        │
└─────────────────┴────────────┴────────────┴────────────┘

网络IO性能 (HTTP请求/秒):
┌─────────────────┬────────────┬────────────┬────────────┐
│     运行时      │  epoll     │ io_uring   │ SQPOLL     │
├─────────────────┼────────────┼────────────┼────────────┤
│ tokio (epoll)   │ 200K       │ -          │ -          │
│ tokio-uring     │ -          │ 350K       │ 500K       │
│ monoio          │ -          │ 400K       │ 600K       │
│ glommio         │ -          │ 450K       │ 700K       │
└─────────────────┴────────────┴────────────┴────────────┘

延迟 (P99, μs):
┌─────────────────┬────────────┬────────────┬────────────┐
│     模式        │  epoll     │ io_uring   │ SQPOLL     │
├─────────────────┼────────────┼────────────┼────────────┤
│ 延迟            │ 50         │ 20         │ 5          │
└─────────────────┴────────────┴────────────┴────────────┘
```

### 4.2 内核版本要求

| 特性 | 内核版本 | 说明 |
|:-----|:--------:|:-----|
| 基础io_uring | 5.1 | 初始版本 |
| SQPOLL | 5.11 | 稳定可用 |
| 多shot accept | 5.19 | 高效accept |
| 注册缓冲区环 | 6.0 | 零拷贝优化 |
| IO流支持 | 6.1 | 更好的网络支持 |

---

## 5. Rust io_uring库

### 5.1 io-uring (底层绑定)

```rust
use io_uring::{IoUring, opcode, types, squeue, cqueue};

fn main() -> std::io::Result<()> {
    let mut ring = IoUring::new(256)?;

    let fd = std::fs::File::open("file.txt")?;
    let mut buf = vec![0; 4096];

    let read_e = opcode::Read::new(
        types::Fd(fd.as_raw_fd()),
        buf.as_mut_ptr(),
        buf.len() as u32,
    )
    .offset(0)
    .build()
    .user_data(0x42);

    unsafe {
        ring.submission()
            .push(&read_e)
            .expect("submission queue is full");
    }

    ring.submit_and_wait(1)?;

    let cqe = ring.completion().next().expect("completion queue is empty");
    assert_eq!(cqe.user_data(), 0x42);
    assert!(cqe.result() >= 0, "read error: {}", cqe.result());

    Ok(())
}
```

### 5.2 生态对比

| 库 | 层次 | 易用性 | 性能 | 维护状态 |
|:---|:-----|:------:|:----:|:--------:|
| **io-uring** | 底层 | ⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐ 活跃 |
| **tokio-uring** | 集成Tokio | ⭐⭐⭐⭐ | ⭐⭐⭐⭐ | ⭐ 活跃 |
| **glommio** | 独立运行时 | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐ 活跃 |
| **monoio** | 独立运行时 | ⭐⭐⭐ | ⭐⭐⭐⭐⭐ | ⭐ 活跃 |
| **compio** | 跨平台 | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐ 活跃 |

---

**参考**:

- [io_uring内核文档](https://kernel.dk/io_uring.pdf)
- [Efficient IO with io_uring](https://kernel.dk/io_uring.pdf)
- [Lord of the io_uring](https://unixism.net/loti/)

**维护者**: Rust Async Ecosystem Team
**更新日期**: 2026-03-05
