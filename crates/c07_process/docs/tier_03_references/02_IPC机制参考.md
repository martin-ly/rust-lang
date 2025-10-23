# Tier 3: IPC机制参考

> **文档类型**: 技术参考  
> **适用版本**: Rust 1.90+  
> **前置知识**: [IPC通信实践](../tier_02_guides/02_IPC通信实践.md)

---

## 目录

- [Tier 3: IPC机制参考](#tier-3-ipc机制参考)
  - [目录](#目录)
  - [1. IPC机制概述](#1-ipc机制概述)
    - [1.1 IPC的定义与分类](#11-ipc的定义与分类)
    - [1.2 IPC选择决策树](#12-ipc选择决策树)
  - [2. 管道机制深度解析](#2-管道机制深度解析)
    - [2.1 匿名管道原理](#21-匿名管道原理)
    - [2.2 命名管道(FIFO)](#22-命名管道fifo)
    - [2.3 管道缓冲区管理](#23-管道缓冲区管理)
    - [2.4 管道性能优化](#24-管道性能优化)
  - [3. Unix域套接字](#3-unix域套接字)
    - [3.1 Unix Socket vs TCP Socket](#31-unix-socket-vs-tcp-socket)
    - [3.2 抽象命名空间](#32-抽象命名空间)
    - [3.3 文件描述符传递](#33-文件描述符传递)
    - [3.4 凭证传递](#34-凭证传递)
  - [4. 网络套接字](#4-网络套接字)
    - [4.1 TCP套接字详解](#41-tcp套接字详解)
    - [4.2 UDP套接字](#42-udp套接字)
    - [4.3 套接字选项优化](#43-套接字选项优化)
  - [5. 共享内存](#5-共享内存)
    - [5.1 POSIX共享内存](#51-posix共享内存)
    - [5.2 内存映射文件](#52-内存映射文件)
    - [5.3 同步机制](#53-同步机制)
  - [6. 信号机制](#6-信号机制)
  - [7. 消息队列](#7-消息队列)
  - [8. 性能基准测试](#8-性能基准测试)
  - [9. 安全性考虑](#9-安全性考虑)
  - [10. 跨平台实现](#10-跨平台实现)
  - [11. 总结与建议](#11-总结与建议)
    - [IPC机制选择矩阵](#ipc机制选择矩阵)
    - [最佳实践](#最佳实践)
    - [Rust优势](#rust优势)

---

## 1. IPC机制概述

### 1.1 IPC的定义与分类

**IPC (Inter-Process Communication)**: 进程间通信机制，允许独立进程之间交换数据和同步操作。

**分类维度1: 按通信方式**:

```text
IPC机制
├─ 数据传输类
│  ├─ 管道 (Pipe)
│  ├─ 命名管道 (FIFO)
│  ├─ Unix Socket
│  ├─ TCP/UDP Socket
│  └─ 消息队列
├─ 共享数据类
│  ├─ 共享内存 (SHM)
│  └─ 内存映射文件 (mmap)
└─ 同步信号类
   ├─ 信号 (Signal)
   └─ 信号量 (Semaphore)
```

**分类维度2: 按适用范围**:

| 机制 | 同主机 | 跨主机 | 说明 |
|------|--------|--------|------|
| **管道** | ✅ | ❌ | 仅父子进程/兄弟进程 |
| **命名管道** | ✅ | ❌ | 同主机任意进程 |
| **Unix Socket** | ✅ | ❌ | 同主机，性能最优 |
| **TCP Socket** | ✅ | ✅ | 跨主机，最通用 |
| **UDP Socket** | ✅ | ✅ | 跨主机，低延迟 |
| **共享内存** | ✅ | ❌ | 同主机，吞吐最高 |
| **信号** | ✅ | ❌ | 同主机，简单通知 |

**分类维度3: 按数据流向**:

- **单向通信**: 管道（默认）、命名管道
- **双向通信**: Socket、共享内存
- **广播/多播**: UDP、信号

---

### 1.2 IPC选择决策树

```text
需要跨主机通信？
├─ 是 → 使用 TCP/UDP Socket
└─ 否 → 
    ├─ 数据量大且频繁？
    │  ├─ 是 → 共享内存 (Shared Memory)
    │  └─ 否 →
    │      ├─ 仅父子进程？
    │      │  ├─ 是 → 管道 (Pipe)
    │      │  └─ 否 →
    │      │      ├─ 需要灵活性？
    │      │      │  ├─ 是 → Unix Socket
    │      │      │  └─ 否 → 命名管道 (FIFO)
    │      └─ 仅通知信号？
    │         └─ 是 → Signal
```

**性能排序** (同主机):

1. 🥇 共享内存 > 2. 🥈 Unix Socket > 3. 🥉 管道 > 4. TCP Socket

---

## 2. 管道机制深度解析

### 2.1 匿名管道原理

**内核实现**:

```text
父进程                      子进程
  │                          │
  ├─ 写端 (fd[1]) ─────────┐ │
  │                         │ │
  │         ┌───────────────┼─┤ 读端 (fd[0])
  │         │  内核缓冲区   │ │
  │         │  (4KB-64KB)   │ │
  │         └───────────────┘ │
```

**特点**:

- 单向通信（FIFO）
- 缓冲区大小固定（Linux: 65,536字节）
- 写满时阻塞，读空时阻塞
- 所有写端关闭后，读端返回EOF

**Rust实现**:

```rust
use std::process::{Command, Stdio};
use std::io::{Write, BufReader, BufRead};

fn pipe_communication() -> std::io::Result<()> {
    let mut child = Command::new("grep")
        .arg("error")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;
    
    // 写入数据
    if let Some(mut stdin) = child.stdin.take() {
        writeln!(stdin, "info: starting")?;
        writeln!(stdin, "error: failed")?;
        writeln!(stdin, "info: done")?;
    }
    
    // 读取输出
    if let Some(stdout) = child.stdout.take() {
        let reader = BufReader::new(stdout);
        for line in reader.lines() {
            println!("Filtered: {}", line?);
        }
    }
    
    child.wait()?;
    Ok(())
}
```

---

### 2.2 命名管道(FIFO)

**特点**:

- 文件系统中有路径
- 任意进程可通过路径访问
- 持久化（进程退出后仍存在）

**创建与使用**:

```rust
use std::fs;
use std::io::{Write, BufReader, BufRead};
use std::os::unix::fs::FileTypeExt;

// 创建命名管道
#[cfg(unix)]
fn create_fifo(path: &str) -> std::io::Result<()> {
    use nix::unistd::mkfifo;
    use nix::sys::stat::Mode;
    
    mkfifo(path, Mode::S_IRUSR | Mode::S_IWUSR)?;
    Ok(())
}

// 写入端
fn fifo_writer(path: &str) -> std::io::Result<()> {
    let mut file = fs::OpenOptions::new()
        .write(true)
        .open(path)?;
    
    writeln!(file, "Hello from writer")?;
    Ok(())
}

// 读取端
fn fifo_reader(path: &str) -> std::io::Result<()> {
    let file = fs::File::open(path)?;
    let reader = BufReader::new(file);
    
    for line in reader.lines() {
        println!("Received: {}", line?);
    }
    
    Ok(())
}
```

---

### 2.3 管道缓冲区管理

**Linux管道缓冲区大小**:

```rust
#[cfg(target_os = "linux")]
fn get_pipe_size(fd: i32) -> Result<usize, std::io::Error> {
    use nix::fcntl::{fcntl, FcntlArg};
    
    match fcntl(fd, FcntlArg::F_GETPIPE_SZ) {
        Ok(size) => Ok(size as usize),
        Err(e) => Err(std::io::Error::from(e)),
    }
}

#[cfg(target_os = "linux")]
fn set_pipe_size(fd: i32, size: usize) -> Result<(), std::io::Error> {
    use nix::fcntl::{fcntl, FcntlArg};
    
    fcntl(fd, FcntlArg::F_SETPIPE_SZ(size as i32))?;
    Ok(())
}
```

**缓冲区管理策略**:

1. **写满阻塞**: 写端会阻塞直到有空间
2. **读空阻塞**: 读端会阻塞直到有数据
3. **非阻塞模式**: 设置`O_NONBLOCK`

**原子性保证**:

- 小于`PIPE_BUF`(4096字节)的写入是原子的
- 大于`PIPE_BUF`的写入可能被分割

```rust
use std::os::unix::io::AsRawFd;

fn set_nonblocking(file: &std::fs::File) -> std::io::Result<()> {
    use nix::fcntl::{fcntl, FcntlArg, OFlag};
    
    let fd = file.as_raw_fd();
    let flags = fcntl(fd, FcntlArg::F_GETFL)?;
    let mut flags = OFlag::from_bits_truncate(flags);
    flags.insert(OFlag::O_NONBLOCK);
    fcntl(fd, FcntlArg::F_SETFL(flags))?;
    
    Ok(())
}
```

---

### 2.4 管道性能优化

**优化策略**:

**1. 使用缓冲I/O**:

```rust
use std::io::{BufWriter, BufReader, Write, Read};

// 写端
let mut writer = BufWriter::with_capacity(64 * 1024, stdin);
for data in large_dataset {
    writer.write_all(&data)?;
}
writer.flush()?;

// 读端
let mut reader = BufReader::with_capacity(64 * 1024, stdout);
let mut buffer = Vec::new();
reader.read_to_end(&mut buffer)?;
```

**2. 批量传输**:

```rust
// ❌ 低效：逐个字节
for byte in data {
    stdin.write(&[byte])?;
}

// ✅ 高效：批量写入
stdin.write_all(&data)?;
```

**3. 管道容量调整** (Linux):

```rust
#[cfg(target_os = "linux")]
fn optimize_pipe_size(fd: i32) -> Result<(), std::io::Error> {
    // 增加到1MB
    set_pipe_size(fd, 1024 * 1024)?;
    Ok(())
}
```

**性能基准** (Linux, 传输100MB):

| 方法 | 吞吐量 | 延迟 |
|------|--------|------|
| 默认管道(64KB) | ~500 MB/s | 中 |
| 大缓冲区(1MB) | ~800 MB/s | 中 |
| BufReader/Writer | ~1 GB/s | 低 |

---

## 3. Unix域套接字

### 3.1 Unix Socket vs TCP Socket

**对比分析**:

| 特性 | Unix Socket | TCP Socket |
|------|-------------|------------|
| **适用范围** | 同主机 | 跨主机 |
| **性能** | 极高 (无协议栈) | 较低 |
| **延迟** | ~1-2μs | ~50-100μs |
| **吞吐量** | ~10 GB/s | ~1 GB/s (千兆网) |
| **安全性** | 文件权限 | 网络防火墙 |
| **可靠性** | 100% | 需要TCP保证 |

**Rust实现对比**:

```rust
use std::os::unix::net::{UnixStream, UnixListener};
use std::net::{TcpStream, TcpListener};

// Unix Socket服务端
fn unix_socket_server() -> std::io::Result<()> {
    let listener = UnixListener::bind("/tmp/my.sock")?;
    
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                // 处理连接
            }
            Err(e) => eprintln!("Error: {}", e),
        }
    }
    
    Ok(())
}

// TCP Socket服务端
fn tcp_socket_server() -> std::io::Result<()> {
    let listener = TcpListener::bind("127.0.0.1:8080")?;
    
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                // 处理连接
            }
            Err(e) => eprintln!("Error: {}", e),
        }
    }
    
    Ok(())
}
```

---

### 3.2 抽象命名空间

**Linux特性**: 抽象Unix Socket（不创建文件系统条目）

```rust
#[cfg(target_os = "linux")]
fn abstract_unix_socket() -> std::io::Result<()> {
    use std::os::unix::net::UnixListener;
    
    // 以\0开头表示抽象命名空间
    let socket_path = "\0my_abstract_socket";
    let listener = UnixListener::bind(socket_path)?;
    
    println!("监听抽象套接字: {}", socket_path);
    
    Ok(())
}
```

**优点**:

- 无需清理文件系统
- 更快的创建/删除
- 自动清理

---

### 3.3 文件描述符传递

**高级特性**: Unix Socket可以在进程间传递文件描述符

```rust
#[cfg(unix)]
mod fd_passing {
    use std::os::unix::io::{AsRawFd, FromRawFd};
    use std::os::unix::net::UnixStream;
    use nix::sys::socket::{sendmsg, recvmsg, ControlMessage, MsgFlags};
    use nix::sys::uio::IoVec;
    
    pub fn send_fd(socket: &UnixStream, fd: i32) -> Result<(), nix::Error> {
        let cmsg = ControlMessage::ScmRights(&[fd]);
        let iov = [IoVec::from_slice(b"FD")];
        
        sendmsg(
            socket.as_raw_fd(),
            &iov,
            &[cmsg],
            MsgFlags::empty(),
            None,
        )?;
        
        Ok(())
    }
    
    pub fn recv_fd(socket: &UnixStream) -> Result<i32, nix::Error> {
        let mut cmsg_space = nix::cmsg_space!([i32; 1]);
        let mut buf = [0u8; 2];
        let iov = [IoVec::from_mut_slice(&mut buf)];
        
        let msg = recvmsg(
            socket.as_raw_fd(),
            &iov,
            Some(&mut cmsg_space),
            MsgFlags::empty(),
        )?;
        
        for cmsg in msg.cmsgs() {
            if let ControlMessage::ScmRights(fds) = cmsg {
                return Ok(fds[0]);
            }
        }
        
        Err(nix::Error::from_errno(nix::errno::Errno::EINVAL))
    }
}

// 使用示例
fn fd_passing_example() -> std::io::Result<()> {
    use std::fs::File;
    
    // 父进程打开文件
    let file = File::open("/etc/hosts")?;
    let fd = file.as_raw_fd();
    
    // 通过Unix Socket传递给子进程
    let socket = UnixStream::connect("/tmp/fd_passing.sock")?;
    fd_passing::send_fd(&socket, fd)?;
    
    Ok(())
}
```

**应用场景**:

- 特权分离（特权进程打开端口，传递给非特权进程）
- 热重载（新进程接收旧进程的监听Socket）
- 资源池管理

---

### 3.4 凭证传递

**安全特性**: 传递进程的UID/GID/PID

```rust
#[cfg(unix)]
fn get_peer_credentials(stream: &UnixStream) -> std::io::Result<(u32, u32, i32)> {
    use std::os::unix::net::UCred;
    
    let cred = stream.peer_cred()?;
    
    Ok((cred.uid, cred.gid, cred.pid))
}

// 使用示例
fn credential_based_auth() -> std::io::Result<()> {
    let listener = UnixListener::bind("/tmp/auth.sock")?;
    
    for stream in listener.incoming() {
        let stream = stream?;
        let (uid, gid, pid) = get_peer_credentials(&stream)?;
        
        println!("连接来自: UID={}, GID={}, PID={}", uid, gid, pid);
        
        // 基于UID进行授权
        if uid == 0 {
            println!("✅ Root用户，允许访问");
        } else {
            println!("❌ 非特权用户，拒绝访问");
        }
    }
    
    Ok(())
}
```

---

## 4. 网络套接字

### 4.1 TCP套接字详解

**TCP特性**:

- 面向连接
- 可靠传输（重传、确认）
- 顺序保证
- 流控制

**三次握手**:

```text
客户端                      服务端
  │                          │
  ├─ SYN ───────────────────→│
  │                          ├─ SYN+ACK
  │←───────────────────────  │
  ├─ ACK ───────────────────→│
  │                          │
  │     连接建立             │
```

**Rust TCP服务端**:

```rust
use std::net::{TcpListener, TcpStream};
use std::io::{Read, Write};
use std::thread;

pub fn tcp_echo_server(addr: &str) -> std::io::Result<()> {
    let listener = TcpListener::bind(addr)?;
    println!("✅ TCP服务器监听: {}", addr);
    
    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                thread::spawn(move || {
                    handle_client(stream).ok();
                });
            }
            Err(e) => eprintln!("连接错误: {}", e),
        }
    }
    
    Ok(())
}

fn handle_client(mut stream: TcpStream) -> std::io::Result<()> {
    let mut buffer = [0; 1024];
    
    loop {
        let n = stream.read(&mut buffer)?;
        if n == 0 {
            break;  // 连接关闭
        }
        
        stream.write_all(&buffer[..n])?;
    }
    
    Ok(())
}
```

---

### 4.2 UDP套接字

**UDP特性**:

- 无连接
- 不可靠（可能丢包、乱序）
- 低延迟
- 支持广播/多播

**Rust UDP实现**:

```rust
use std::net::UdpSocket;

// UDP服务端
fn udp_server(addr: &str) -> std::io::Result<()> {
    let socket = UdpSocket::bind(addr)?;
    println!("✅ UDP服务器监听: {}", addr);
    
    let mut buf = [0; 1024];
    
    loop {
        let (amt, src) = socket.recv_from(&mut buf)?;
        println!("收到 {} 字节，来自 {}", amt, src);
        
        // Echo back
        socket.send_to(&buf[..amt], src)?;
    }
}

// UDP客户端
fn udp_client(server: &str) -> std::io::Result<()> {
    let socket = UdpSocket::bind("0.0.0.0:0")?;
    
    socket.send_to(b"Hello", server)?;
    
    let mut buf = [0; 1024];
    let (amt, _) = socket.recv_from(&mut buf)?;
    
    println!("收到: {}", String::from_utf8_lossy(&buf[..amt]));
    
    Ok(())
}
```

---

### 4.3 套接字选项优化

**常用优化选项**:

```rust
use std::net::{TcpStream, TcpListener};
use std::time::Duration;

fn optimize_tcp_socket(stream: &TcpStream) -> std::io::Result<()> {
    // 1. TCP_NODELAY: 禁用Nagle算法，降低延迟
    stream.set_nodelay(true)?;
    
    // 2. 读超时
    stream.set_read_timeout(Some(Duration::from_secs(30)))?;
    
    // 3. 写超时
    stream.set_write_timeout(Some(Duration::from_secs(30)))?;
    
    // 4. 保持连接活跃
    #[cfg(unix)]
    {
        use std::os::unix::io::AsRawFd;
        use nix::sys::socket::{setsockopt, sockopt};
        
        let fd = stream.as_raw_fd();
        setsockopt(fd, sockopt::KeepAlive, &true)?;
    }
    
    Ok(())
}

fn optimize_tcp_listener(listener: &TcpListener) -> std::io::Result<()> {
    // SO_REUSEADDR: 允许地址重用
    #[cfg(unix)]
    {
        use std::os::unix::io::AsRawFd;
        use nix::sys::socket::{setsockopt, sockopt};
        
        let fd = listener.as_raw_fd();
        setsockopt(fd, sockopt::ReuseAddr, &true)?;
    }
    
    Ok(())
}
```

**性能对比** (localhost, 100MB传输):

| 配置 | 延迟 | 吞吐量 |
|------|------|--------|
| 默认TCP | ~50μs | ~1 GB/s |
| TCP_NODELAY | ~10μs | ~1.2 GB/s |
| 大缓冲区(256KB) | ~50μs | ~2 GB/s |
| Unix Socket | ~2μs | ~10 GB/s |

---

## 5. 共享内存

### 5.1 POSIX共享内存

**创建与使用**:

```rust
use shared_memory::*;

// 创建共享内存
fn create_shm() -> Result<Shmem, Box<dyn std::error::Error>> {
    let shmem = ShmemConf::new()
        .size(4096)
        .create()?;
    
    Ok(shmem)
}

// 写入数据
fn write_shm(shmem: &mut Shmem, data: &[u8]) {
    unsafe {
        let ptr = shmem.as_ptr() as *mut u8;
        std::ptr::copy_nonoverlapping(data.as_ptr(), ptr, data.len());
    }
}

// 读取数据
fn read_shm(shmem: &Shmem, len: usize) -> Vec<u8> {
    unsafe {
        let ptr = shmem.as_ptr();
        std::slice::from_raw_parts(ptr, len).to_vec()
    }
}
```

**性能**: 最高吞吐量（~20 GB/s），但需要同步机制。

---

### 5.2 内存映射文件

**Rust实现**:

```rust
use memmap2::MmapMut;
use std::fs::OpenOptions;

fn mmap_file(path: &str) -> Result<MmapMut, Box<dyn std::error::Error>> {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .open(path)?;
    
    file.set_len(4096)?;
    
    let mmap = unsafe { MmapMut::map_mut(&file)? };
    Ok(mmap)
}
```

---

### 5.3 同步机制

**使用原子操作**:

```rust
use std::sync::atomic::{AtomicU32, Ordering};

struct SharedCounter {
    counter: AtomicU32,
}

impl SharedCounter {
    pub fn increment(&self) -> u32 {
        self.counter.fetch_add(1, Ordering::SeqCst)
    }
}
```

---

## 6. 信号机制

**Unix信号通信**:

```rust
#[cfg(unix)]
fn signal_example() -> Result<(), Box<dyn std::error::Error>> {
    use signal_hook::{consts::SIGUSR1, iterator::Signals};
    
    let mut signals = Signals::new(&[SIGUSR1])?;
    
    std::thread::spawn(move || {
        for sig in signals.forever() {
            println!("收到信号: {}", sig);
        }
    });
    
    Ok(())
}
```

**适用场景**: 简单的进程间通知（不传递数据）。

---

## 7. 消息队列

**Rust消息传递**:

```rust
use crossbeam_channel::{bounded, Sender, Receiver};

// 创建bounded channel
let (tx, rx): (Sender<String>, Receiver<String>) = bounded(100);

// 发送
tx.send("Message".to_string())?;

// 接收
let msg = rx.recv()?;
```

**特点**: 异步、解耦、缓冲。

---

## 8. 性能基准测试

**延迟对比** (localhost, 1字节):

| 机制 | 平均延迟 |
|------|----------|
| 共享内存 | 0.1 μs |
| Unix Socket | 1-2 μs |
| 管道 | 5-10 μs |
| TCP Socket | 50-100 μs |

**吞吐量对比** (localhost, 100MB):

| 机制 | 吞吐量 |
|------|--------|
| 共享内存 | 20 GB/s |
| Unix Socket | 10 GB/s |
| 管道 | 1 GB/s |
| TCP Socket | 1 GB/s |

---

## 9. 安全性考虑

**权限控制**:

```rust
#[cfg(unix)]
fn set_socket_permissions(path: &str) -> std::io::Result<()> {
    use std::os::unix::fs::PermissionsExt;
    use std::fs;
    
    let permissions = fs::Permissions::from_mode(0o600);  // 仅所有者可读写
    fs::set_permissions(path, permissions)?;
    
    Ok(())
}
```

**输入验证**:

```rust
fn validate_message(msg: &[u8]) -> Result<(), &'static str> {
    if msg.len() > 1024 * 1024 {  // 1MB限制
        return Err("消息过大");
    }
    
    // 验证格式
    if msg.is_empty() {
        return Err("消息为空");
    }
    
    Ok(())
}
```

**防止注入攻击**: 不要直接将IPC数据用作命令执行。

---

## 10. 跨平台实现

**统一IPC接口**:

```rust
pub trait IpcChannel {
    fn send(&mut self, data: &[u8]) -> Result<(), Box<dyn std::error::Error>>;
    fn recv(&mut self) -> Result<Vec<u8>, Box<dyn std::error::Error>>;
}

#[cfg(unix)]
impl IpcChannel for UnixStream {
    fn send(&mut self, data: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
        use std::io::Write;
        self.write_all(data)?;
        Ok(())
    }
    
    fn recv(&mut self) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        use std::io::Read;
        let mut buf = vec![0; 1024];
        let n = self.read(&mut buf)?;
        buf.truncate(n);
        Ok(buf)
    }
}

impl IpcChannel for TcpStream {
    fn send(&mut self, data: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
        use std::io::Write;
        self.write_all(data)?;
        Ok(())
    }
    
    fn recv(&mut self) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
        use std::io::Read;
        let mut buf = vec![0; 1024];
        let n = self.read(&mut buf)?;
        buf.truncate(n);
        Ok(())
    }
}
```

**选择策略**:

```rust
pub fn create_ipc_channel(local_only: bool) -> Box<dyn IpcChannel> {
    #[cfg(unix)]
    if local_only {
        return Box::new(UnixStream::connect("/tmp/ipc.sock").unwrap());
    }
    
    Box::new(TcpStream::connect("127.0.0.1:8080").unwrap())
}
```

---

## 11. 总结与建议

### IPC机制选择矩阵

| 需求 | 推荐机制 | 原因 |
|------|----------|------|
| **父子进程通信** | 管道 | 简单、内置 |
| **同主机高性能** | Unix Socket / 共享内存 | 低延迟、高吞吐 |
| **跨主机通信** | TCP Socket | 标准、可靠 |
| **大数据传输** | 共享内存 | 最高吞吐量 |
| **实时通知** | 信号 | 低开销 |
| **异步消息** | 消息队列 | 解耦、缓冲 |

### 最佳实践

1. ✅ **选择合适的机制**: 根据需求选择（本地 vs 远程，吞吐 vs 延迟）
2. ✅ **错误处理**: 所有IPC调用都应检查错误
3. ✅ **超时机制**: 防止无限阻塞
4. ✅ **缓冲优化**: 使用BufReader/BufWriter
5. ✅ **安全验证**: 验证输入，控制权限
6. ✅ **资源清理**: 关闭连接，删除临时文件

### Rust优势

- **类型安全**: 编译时检查
- **零成本抽象**: 高性能
- **跨平台**: 统一接口
- **内存安全**: 无泄漏、无数据竞争

---

**下一步**: [03_Rust190特性参考](./03_Rust190特性参考.md)

---

**文档维护**: Documentation Team  
**创建日期**: 2025-10-22  
**最后更新**: 2025-10-23  
**适用版本**: Rust 1.90+
