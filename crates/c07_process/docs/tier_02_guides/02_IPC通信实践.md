# Tier 2: IPC通信实践

> **文档类型**: 实践指南
> **难度**: ⭐⭐⭐ 中级
> **预计时间**: 3小时
> **适用版本**: Rust 1.90+

---

## 目录

- [Tier 2: IPC通信实践](#tier-2-ipc通信实践)
  - [目录](#目录)
  - [学习目标](#学习目标)
  - [1. IPC机制概览](#1-ipc机制概览)
  - [2. 管道通信](#2-管道通信)
    - [2.1 匿名管道基础](#21-匿名管道基础)
    - [2.2 双向管道通信](#22-双向管道通信)
    - [2.3 管道链（Pipeline）](#23-管道链pipeline)
    - [2.4 命名管道（FIFO）](#24-命名管道fifo)
    - [2.5 管道容量和缓冲](#25-管道容量和缓冲)
    - [2.6 管道性能优化](#26-管道性能优化)
  - [3. Unix Socket](#3-unix-socket)
    - [3.1 基础Unix Socket服务端](#31-基础unix-socket服务端)
    - [3.2 Unix Socket客户端](#32-unix-socket客户端)
    - [3.3 带协议的Unix Socket通信](#33-带协议的unix-socket通信)
    - [3.4 异步Unix Socket (使用Tokio)](#34-异步unix-socket-使用tokio)
    - [3.5 Unix Socket权限和安全](#35-unix-socket权限和安全)
    - [3.6 Unix Socket性能优化](#36-unix-socket性能优化)
  - [4. TCP Socket](#4-tcp-socket)
    - [4.1 基础TCP服务端](#41-基础tcp服务端)
    - [4.2 TCP客户端](#42-tcp客户端)
    - [4.3 异步TCP (使用Tokio)](#43-异步tcp-使用tokio)
    - [4.4 TCP连接池](#44-tcp连接池)
    - [4.5 TCP性能优化](#45-tcp性能优化)
    - [4.6 处理TCP粘包](#46-处理tcp粘包)
  - [5. 共享内存](#5-共享内存)
    - [5.1 基础共享内存](#51-基础共享内存)
    - [5.2 结构化共享内存](#52-结构化共享内存)
    - [5.3 带同步的共享内存](#53-带同步的共享内存)
    - [5.4 环形缓冲区（Ring Buffer）](#54-环形缓冲区ring-buffer)
    - [5.5 共享内存性能测试](#55-共享内存性能测试)
  - [6. 选择合适的IPC机制](#6-选择合适的ipc机制)
  - [7. 实战案例](#7-实战案例)
    - [案例1: 统一的IPC抽象层](#案例1-统一的ipc抽象层)
    - [案例2: RPC (远程过程调用)](#案例2-rpc-远程过程调用)
  - [8. 常见问题解答](#8-常见问题解答)
    - [Q1: 如何选择合适的IPC机制？](#q1-如何选择合适的ipc机制)
    - [Q2: 如何处理IPC的背压（Backpressure）？](#q2-如何处理ipc的背压backpressure)
    - [Q3: 如何实现可靠的消息传递？](#q3-如何实现可靠的消息传递)
    - [Q4: 如何处理IPC超时？](#q4-如何处理ipc超时)
    - [Q5: 如何调试IPC问题？](#q5-如何调试ipc问题)
  - [9. 性能优化最佳实践](#9-性能优化最佳实践)
    - [9.1 批处理](#91-批处理)
    - [9.2 零拷贝](#92-零拷贝)
    - [9.3 连接复用](#93-连接复用)
  - [10. 安全注意事项](#10-安全注意事项)
    - [10.1 输入验证](#101-输入验证)
    - [10.2 权限控制](#102-权限控制)
  - [下一步](#下一步)

---

## 学习目标

- ✅ 理解不同IPC机制的特点
- ✅ 实现管道、Socket通信
- ✅ 选择合适的IPC方案
- ✅ 构建实用的IPC应用

---

## 1. IPC机制概览

**IPC对比**:

| IPC类型 | 性能 | 跨网络 | 复杂度 | 适用场景 |
|---------|------|--------|--------|---------|
| 管道 | 中 | 否 | 低 | 父子进程 |
| 命名管道 | 中 | 否 | 低 | 本地无亲缘进程 |
| Unix Socket | 高 | 否 | 中 | 本地复杂通信 |
| TCP Socket | 中 | 是 | 中 | 跨网络 |
| 共享内存 | 最高 | 否 | 高 | 大数据高性能 |

---

## 2. 管道通信

管道是最基本的IPC机制，允许一个进程的输出直接连接到另一个进程的输入。

### 2.1 匿名管道基础

**基础管道示例**:

```rust
use std::process::{Command, Stdio};
use std::io::Write;

fn basic_pipe_example() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()?;

    // 获取stdin并写入数据
    if let Some(mut stdin) = child.stdin.take() {
        stdin.write_all(b"Hello Pipe!\n")?;
        stdin.write_all(b"Line 2\n")?;
        // stdin自动关闭（Drop）
    }

    // 读取输出
    let output = child.wait_with_output()?;
    println!("Output: {}", String::from_utf8_lossy(&output.stdout));
    println!("Exit status: {}", output.status);

    Ok(())
}
```

**注意事项**:

- 必须调用 `take()` 获取所有权
- 写入后要关闭stdin（或drop），否则子进程会一直等待
- 使用 `wait_with_output()` 同时等待进程结束并收集输出

---

### 2.2 双向管道通信

同时读取stdout和stderr：

```rust
use std::process::{Command, Stdio};
use std::io::{Write, Read, BufReader, BufRead};
use std::thread;

fn bidirectional_pipe() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("sh")
        .arg("-c")
        .arg("echo stdout; echo stderr >&2")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    // 获取所有流
    let mut stdin = child.stdin.take().unwrap();
    let stdout = child.stdout.take().unwrap();
    let stderr = child.stderr.take().unwrap();

    // 在单独线程中读取stdout
    let stdout_thread = thread::spawn(move || {
        let reader = BufReader::new(stdout);
        for line in reader.lines() {
            println!("[stdout] {}", line.unwrap());
        }
    });

    // 在单独线程中读取stderr
    let stderr_thread = thread::spawn(move || {
        let reader = BufReader::new(stderr);
        for line in reader.lines() {
            eprintln!("[stderr] {}", line.unwrap());
        }
    });

    // 主线程写入数据
    stdin.write_all(b"input data\n")?;
    drop(stdin);  // 关闭stdin

    // 等待所有线程完成
    stdout_thread.join().unwrap();
    stderr_thread.join().unwrap();
    child.wait()?;

    Ok(())
}
```

**关键点**:

- 必须在单独线程读取，避免缓冲区满导致死锁
- 使用 `BufReader` 和 `lines()` 按行读取
- 主线程负责写入，子线程负责读取

---

### 2.3 管道链（Pipeline）

连接多个进程形成数据处理管道：

```rust
use std::process::{Command, Stdio};

/// 构建管道: ls -la | grep .rs | wc -l
fn pipeline_example() -> Result<String, Box<dyn std::error::Error>> {
    // 第一个进程: ls -la
    let ls = Command::new("ls")
        .arg("-la")
        .stdout(Stdio::piped())
        .spawn()?;

    // 第二个进程: grep .rs
    let grep = Command::new("grep")
        .arg(".rs")
        .stdin(ls.stdout.unwrap())
        .stdout(Stdio::piped())
        .spawn()?;

    // 第三个进程: wc -l
    let wc_output = Command::new("wc")
        .arg("-l")
        .stdin(grep.stdout.unwrap())
        .output()?;

    Ok(String::from_utf8_lossy(&wc_output.stdout).to_string())
}
```

**更通用的管道构建器**:

```rust
use std::process::{Command, Stdio, Child};

struct Pipeline {
    commands: Vec<(String, Vec<String>)>,
}

impl Pipeline {
    fn new() -> Self {
        Self {
            commands: Vec::new(),
        }
    }

    fn add(&mut self, program: &str, args: Vec<&str>) -> &mut Self {
        self.commands.push((
            program.to_string(),
            args.iter().map(|s| s.to_string()).collect()
        ));
        self
    }

    fn execute(&self) -> Result<String, Box<dyn std::error::Error>> {
        if self.commands.is_empty() {
            return Err("Pipeline is empty".into());
        }

        let mut children: Vec<Child> = Vec::new();
        let mut prev_stdout: Option<Stdio> = None;

        for (i, (program, args)) in self.commands.iter().enumerate() {
            let stdin = if i == 0 {
                Stdio::null()
            } else {
                prev_stdout.take().unwrap()
            };

            let stdout = if i == self.commands.len() - 1 {
                Stdio::piped()
            } else {
                Stdio::piped()
            };

            let mut cmd = Command::new(program);
            cmd.args(args)
                .stdin(stdin)
                .stdout(stdout);

            let child = cmd.spawn()?;

            if i < self.commands.len() - 1 {
                prev_stdout = child.stdout.map(Stdio::from);
            }

            children.push(child);
        }

        // 等待所有进程
        for child in &mut children[..children.len() - 1] {
            child.wait()?;
        }

        // 获取最后一个进程的输出
        let output = children.last_mut().unwrap().wait_with_output()?;
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let result = Pipeline::new()
        .add("cat", vec!["data.txt"])
        .add("grep", vec!["pattern"])
        .add("sort", vec![])
        .add("uniq", vec!["-c"])
        .execute()?;

    println!("Result:\n{}", result);
    Ok(())
}
```

---

### 2.4 命名管道（FIFO）

在Unix系统上创建命名管道：

```rust
#[cfg(unix)]
use std::os::unix::fs::OpenOptionsExt;
use std::fs::OpenOptions;
use std::io::{Write, Read};

#[cfg(unix)]
fn create_named_pipe() -> Result<(), Box<dyn std::error::Error>> {
    use nix::sys::stat;
    use nix::unistd;

    let fifo_path = "/tmp/my_fifo";

    // 创建命名管道
    unistd::mkfifo(
        fifo_path,
        stat::Mode::S_IRWXU
    )?;

    // 在另一个线程中写入
    let writer_thread = std::thread::spawn(|| {
        let mut file = OpenOptions::new()
            .write(true)
            .open("/tmp/my_fifo")
            .unwrap();

        file.write_all(b"Hello from writer!\n").unwrap();
    });

    // 主线程读取
    let mut file = OpenOptions::new()
        .read(true)
        .open(fifo_path)?;

    let mut buffer = String::new();
    file.read_to_string(&mut buffer)?;
    println!("Received: {}", buffer);

    writer_thread.join().unwrap();
    std::fs::remove_file(fifo_path)?;

    Ok(())
}
```

---

### 2.5 管道容量和缓冲

了解管道的容量限制：

```rust
use std::process::{Command, Stdio};
use std::io::Write;

fn pipe_capacity_test() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::null())  // 丢弃输出
        .spawn()?;

    if let Some(mut stdin) = child.stdin.take() {
        // 尝试写入大量数据
        let large_data = vec![b'x'; 1024 * 1024];  // 1MB

        match stdin.write_all(&large_data) {
            Ok(_) => println!("Successfully wrote all data"),
            Err(e) => println!("Write error: {}", e),
        }
    }

    child.wait()?;
    Ok(())
}
```

**管道容量**:

- Linux: 通常为 64KB (可通过 `fcntl` 修改)
- macOS: 16KB
- Windows: 命名管道可配置，默认4KB

**避免死锁**:

```rust
// ❌ 可能死锁
let mut child = Command::new("cat")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .spawn()?;

child.stdin.as_mut().unwrap().write_all(&huge_data)?;  // 可能阻塞
let output = child.wait_with_output()?;  // 永远不会到达

// ✅ 正确：使用线程
use std::thread;

let mut child = Command::new("cat")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .spawn()?;

let mut stdin = child.stdin.take().unwrap();
let write_thread = thread::spawn(move || {
    stdin.write_all(&huge_data).unwrap();
});

let output = child.wait_with_output()?;
write_thread.join().unwrap();
```

---

### 2.6 管道性能优化

```rust
use std::io::{BufWriter, Write};

fn optimized_pipe_write() -> Result<(), Box<dyn std::error::Error>> {
    let mut child = Command::new("cat")
        .stdin(Stdio::piped())
        .stdout(Stdio::null())
        .spawn()?;

    if let Some(stdin) = child.stdin.take() {
        // 使用BufferedWriter提升性能
        let mut writer = BufWriter::new(stdin);

        for i in 0..100000 {
            writeln!(writer, "Line {}", i)?;
        }

        // 确保flush
        writer.flush()?;
    }

    child.wait()?;
    Ok(())
}
```

**性能对比**:

| 方法 | 100k行写入时间 |
|------|---------------|
| 直接write | ~500ms |
| BufWriter | ~50ms (10x faster) |
| 批量write_all | ~100ms |

---

## 3. Unix Socket

Unix Domain Socket是高性能的本地IPC机制，适用于同一台机器上的进程通信。

### 3.1 基础Unix Socket服务端

完整的echo服务器实现：

```rust
#[cfg(unix)]
use std::os::unix::net::{UnixListener, UnixStream};
use std::io::{Read, Write};
use std::thread;

#[cfg(unix)]
fn unix_socket_server() -> Result<(), Box<dyn std::error::Error>> {
    let socket_path = "/tmp/my.sock";

    // 清理旧socket文件
    let _ = std::fs::remove_file(socket_path);

    let listener = UnixListener::bind(socket_path)?;
    println!("🚀 Server listening on {}", socket_path);

    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                thread::spawn(move || handle_client(stream));
            }
            Err(e) => {
                eprintln!("❌ Connection failed: {}", e);
            }
        }
    }

    Ok(())
}

#[cfg(unix)]
fn handle_client(mut stream: UnixStream) {
    let peer_addr = stream.peer_addr()
        .map(|addr| format!("{:?}", addr))
        .unwrap_or_else(|_| "unknown".to_string());

    println!("✅ New client: {}", peer_addr);

    let mut buf = [0; 1024];
    loop {
        match stream.read(&mut buf) {
            Ok(0) => {
                println!("🔌 Client disconnected: {}", peer_addr);
                break;
            }
            Ok(n) => {
                println!("📥 Received {} bytes from {}", n, peer_addr);

                // Echo back
                if let Err(e) = stream.write_all(&buf[..n]) {
                    eprintln!("❌ Write error: {}", e);
                    break;
                }
            }
            Err(e) => {
                eprintln!("❌ Read error: {}", e);
                break;
            }
        }
    }
}
```

---

### 3.2 Unix Socket客户端

```rust
#[cfg(unix)]
use std::os::unix::net::UnixStream;
use std::io::{Read, Write};

#[cfg(unix)]
fn unix_socket_client() -> Result<(), Box<dyn std::error::Error>> {
    let mut stream = UnixStream::connect("/tmp/my.sock")?;
    println!("✅ Connected to server");

    // 发送数据
    let message = b"Hello from client!";
    stream.write_all(message)?;
    println!("📤 Sent: {}", String::from_utf8_lossy(message));

    // 接收响应
    let mut buffer = vec![0; 1024];
    let n = stream.read(&mut buffer)?;
    println!("📥 Received: {}", String::from_utf8_lossy(&buffer[..n]));

    Ok(())
}
```

---

### 3.3 带协议的Unix Socket通信

定义消息协议：

```rust
#[cfg(unix)]
use serde::{Serialize, Deserialize};
use std::os::unix::net::{UnixListener, UnixStream};
use std::io::{Read, Write};

#[derive(Serialize, Deserialize, Debug)]
enum Message {
    Request { id: u32, data: String },
    Response { id: u32, result: String },
    Error { id: u32, message: String },
}

#[cfg(unix)]
struct ProtocolServer {
    listener: UnixListener,
}

#[cfg(unix)]
impl ProtocolServer {
    fn new(path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        let _ = std::fs::remove_file(path);
        Ok(Self {
            listener: UnixListener::bind(path)?,
        })
    }

    fn run(&self) -> Result<(), Box<dyn std::error::Error>> {
        for stream in self.listener.incoming() {
            let stream = stream?;
            std::thread::spawn(move || {
                if let Err(e) = Self::handle_connection(stream) {
                    eprintln!("Error handling connection: {}", e);
                }
            });
        }
        Ok(())
    }

    fn handle_connection(mut stream: UnixStream) -> Result<(), Box<dyn std::error::Error>> {
        let mut length_buf = [0u8; 4];

        loop {
            // 读取消息长度
            if stream.read_exact(&mut length_buf).is_err() {
                break;
            }
            let length = u32::from_be_bytes(length_buf) as usize;

            // 读取消息内容
            let mut msg_buf = vec![0u8; length];
            stream.read_exact(&mut msg_buf)?;

            // 解析消息
            let message: Message = bincode::deserialize(&msg_buf)?;
            println!("Received: {:?}", message);

            // 处理并响应
            let response = match message {
                Message::Request { id, data } => {
                    Message::Response {
                        id,
                        result: format!("Processed: {}", data),
                    }
                }
                _ => Message::Error {
                    id: 0,
                    message: "Invalid message type".to_string(),
                },
            };

            // 发送响应
            let response_data = bincode::serialize(&response)?;
            let response_length = (response_data.len() as u32).to_be_bytes();

            stream.write_all(&response_length)?;
            stream.write_all(&response_data)?;
        }

        Ok(())
    }
}

#[cfg(unix)]
struct ProtocolClient {
    stream: UnixStream,
}

#[cfg(unix)]
impl ProtocolClient {
    fn connect(path: &str) -> Result<Self, Box<dyn std::error::Error>> {
        Ok(Self {
            stream: UnixStream::connect(path)?,
        })
    }

    fn send_request(&mut self, id: u32, data: String) -> Result<Message, Box<dyn std::error::Error>> {
        // 构造请求
        let request = Message::Request { id, data };
        let request_data = bincode::serialize(&request)?;
        let request_length = (request_data.len() as u32).to_be_bytes();

        // 发送请求
        self.stream.write_all(&request_length)?;
        self.stream.write_all(&request_data)?;

        // 接收响应
        let mut length_buf = [0u8; 4];
        self.stream.read_exact(&mut length_buf)?;
        let length = u32::from_be_bytes(length_buf) as usize;

        let mut response_buf = vec![0u8; length];
        self.stream.read_exact(&mut response_buf)?;

        Ok(bincode::deserialize(&response_buf)?)
    }
}
```

---

### 3.4 异步Unix Socket (使用Tokio)

```rust
#[cfg(unix)]
use tokio::net::{UnixListener, UnixStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[cfg(unix)]
#[tokio::main]
async fn async_unix_server() -> Result<(), Box<dyn std::error::Error>> {
    let socket_path = "/tmp/async.sock";
    let _ = std::fs::remove_file(socket_path);

    let listener = UnixListener::bind(socket_path)?;
    println!("🚀 Async server listening");

    loop {
        let (stream, _) = listener.accept().await?;
        tokio::spawn(async move {
            if let Err(e) = handle_async_client(stream).await {
                eprintln!("Error: {}", e);
            }
        });
    }
}

#[cfg(unix)]
async fn handle_async_client(mut stream: UnixStream) -> Result<(), Box<dyn std::error::Error>> {
    let mut buf = vec![0; 1024];

    loop {
        let n = stream.read(&mut buf).await?;
        if n == 0 {
            break;
        }

        stream.write_all(&buf[..n]).await?;
    }

    Ok(())
}

#[cfg(unix)]
async fn async_unix_client() -> Result<(), Box<dyn std::error::Error>> {
    let mut stream = UnixStream::connect("/tmp/async.sock").await?;

    stream.write_all(b"Hello async!").await?;

    let mut buf = vec![0; 1024];
    let n = stream.read(&mut buf).await?;
    println!("Received: {}", String::from_utf8_lossy(&buf[..n]));

    Ok(())
}
```

---

### 3.5 Unix Socket权限和安全

设置socket文件权限：

```rust
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;
use std::fs;

#[cfg(unix)]
fn create_secure_socket() -> Result<(), Box<dyn std::error::Error>> {
    let socket_path = "/tmp/secure.sock";
    let _ = fs::remove_file(socket_path);

    let listener = UnixListener::bind(socket_path)?;

    // 设置权限为 0600 (仅所有者可读写)
    let metadata = fs::metadata(socket_path)?;
    let mut permissions = metadata.permissions();
    permissions.set_mode(0o600);
    fs::set_permissions(socket_path, permissions)?;

    println!("✅ Secure socket created with 0600 permissions");

    Ok(())
}
```

**凭证传递** (Unix Credential Passing):

```rust
#[cfg(target_os = "linux")]
use std::os::unix::net::UnixStream;

#[cfg(target_os = "linux")]
fn get_peer_credentials(stream: &UnixStream) -> Result<(u32, u32, u32), Box<dyn std::error::Error>> {
    use nix::sys::socket::{getsockopt, sockopt::PeerCredentials};
    use std::os::unix::io::AsRawFd;

    let creds = getsockopt(stream.as_raw_fd(), PeerCredentials)?;

    Ok((creds.pid() as u32, creds.uid(), creds.gid()))
}
```

---

### 3.6 Unix Socket性能优化

```rust
#[cfg(unix)]
use std::os::unix::net::UnixStream;
use std::io::{BufReader, BufWriter, Write};

#[cfg(unix)]
fn optimized_unix_socket() -> Result<(), Box<dyn std::error::Error>> {
    let stream = UnixStream::connect("/tmp/my.sock")?;

    // 使用缓冲提升性能
    let mut reader = BufReader::new(stream.try_clone()?);
    let mut writer = BufWriter::new(stream);

    // 批量写入
    for i in 0..1000 {
        writeln!(writer, "Message {}", i)?;
    }
    writer.flush()?;

    Ok(())
}
```

**性能对比** (同一台机器):

| IPC机制 | 延迟 | 吞吐量 |
|---------|------|--------|
| Unix Socket | ~2-5 μs | 5-10 GB/s |
| TCP Localhost | ~10-20 μs | 2-5 GB/s |
| 管道 | ~5-10 μs | 3-6 GB/s |
| 共享内存 | ~0.1-1 μs | 20+ GB/s |

---

## 4. TCP Socket

TCP Socket支持跨网络通信，是最通用的IPC机制。

### 4.1 基础TCP服务端

完整的多线程TCP echo服务器：

```rust
use std::net::{TcpListener, TcpStream};
use std::io::{Read, Write};
use std::thread;

fn tcp_server() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:8080")?;
    println!("🚀 TCP Server listening on 127.0.0.1:8080");

    for stream in listener.incoming() {
        match stream {
            Ok(stream) => {
                println!("✅ New connection from {:?}", stream.peer_addr());
                thread::spawn(move || {
                    if let Err(e) = handle_tcp_client(stream) {
                        eprintln!("❌ Error handling client: {}", e);
                    }
                });
            }
            Err(e) => {
                eprintln!("❌ Connection failed: {}", e);
            }
        }
    }

    Ok(())
}

fn handle_tcp_client(mut stream: TcpStream) -> Result<(), Box<dyn std::error::Error>> {
    let peer_addr = stream.peer_addr()?;
    println!("📥 Handling client: {}", peer_addr);

    let mut buf = [0; 1024];
    loop {
        match stream.read(&mut buf) {
            Ok(0) => {
                println!("🔌 Client disconnected: {}", peer_addr);
                break;
            }
            Ok(n) => {
                println!("📥 Received {} bytes from {}", n, peer_addr);
                stream.write_all(&buf[..n])?;
            }
            Err(e) => {
                eprintln!("❌ Read error: {}", e);
                break;
            }
        }
    }

    Ok(())
}
```

---

### 4.2 TCP客户端

```rust
use std::net::TcpStream;
use std::io::{Read, Write};
use std::time::Duration;

fn tcp_client() -> Result<(), Box<dyn std::error::Error>> {
    let mut stream = TcpStream::connect("127.0.0.1:8080")?;
    println!("✅ Connected to server");

    // 设置超时
    stream.set_read_timeout(Some(Duration::from_secs(5)))?;
    stream.set_write_timeout(Some(Duration::from_secs(5)))?;

    // 发送数据
    let message = b"Hello TCP Server!";
    stream.write_all(message)?;
    println!("📤 Sent: {}", String::from_utf8_lossy(message));

    // 接收响应
    let mut buffer = vec![0; 1024];
    let n = stream.read(&mut buffer)?;
    println!("📥 Received: {}", String::from_utf8_lossy(&buffer[..n]));

    Ok(())
}
```

---

### 4.3 异步TCP (使用Tokio)

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn async_tcp_server() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    println!("🚀 Async TCP Server listening");

    loop {
        let (socket, addr) = listener.accept().await?;
        println!("✅ New connection from {}", addr);

        tokio::spawn(async move {
            if let Err(e) = handle_async_tcp_client(socket).await {
                eprintln!("Error: {}", e);
            }
        });
    }
}

async fn handle_async_tcp_client(mut socket: TcpStream) -> Result<(), Box<dyn std::error::Error>> {
    let mut buf = vec![0; 1024];

    loop {
        let n = socket.read(&mut buf).await?;
        if n == 0 {
            return Ok(());
        }

        socket.write_all(&buf[..n]).await?;
    }
}
```

---

### 4.4 TCP连接池

```rust
use std::net::TcpStream;
use std::sync::{Arc, Mutex};
use std::collections::VecDeque;
use std::time::Duration;

struct TcpConnectionPool {
    connections: Arc<Mutex<VecDeque<TcpStream>>>,
    address: String,
    max_size: usize,
}

impl TcpConnectionPool {
    fn new(address: String, max_size: usize) -> Self {
        Self {
            connections: Arc::new(Mutex::new(VecDeque::new())),
            address,
            max_size,
        }
    }

    fn get_connection(&self) -> Result<TcpStream, Box<dyn std::error::Error>> {
        let mut pool = self.connections.lock().unwrap();

        // 尝试从池中获取
        if let Some(stream) = pool.pop_front() {
            // 验证连接是否仍然有效
            if stream.peer_addr().is_ok() {
                return Ok(stream);
            }
        }

        // 创建新连接
        let stream = TcpStream::connect(&self.address)?;
        stream.set_nodelay(true)?;
        Ok(stream)
    }

    fn return_connection(&self, stream: TcpStream) {
        let mut pool = self.connections.lock().unwrap();

        if pool.len() < self.max_size {
            pool.push_back(stream);
        }
        // 否则让连接自动关闭
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let pool = TcpConnectionPool::new("127.0.0.1:8080".to_string(), 10);

    // 使用连接
    let stream = pool.get_connection()?;
    // ... 使用stream ...
    pool.return_connection(stream);

    Ok(())
}
```

---

### 4.5 TCP性能优化

**启用TCP_NODELAY** (禁用Nagle算法):

```rust
use std::net::TcpStream;

fn optimize_tcp_stream(stream: &TcpStream) -> std::io::Result<()> {
    // 禁用Nagle算法，降低延迟
    stream.set_nodelay(true)?;

    // 设置发送/接收缓冲区大小
    #[cfg(unix)]
    {
        use std::os::unix::io::AsRawFd;
        use nix::sys::socket::{setsockopt, sockopt};

        let fd = stream.as_rawfd();
        setsockopt(fd, sockopt::SndBuf, &(256 * 1024))?;  // 256KB send buffer
        setsockopt(fd, sockopt::RcvBuf, &(256 * 1024))?;  // 256KB receive buffer
    }

    Ok(())
}
```

**使用BufReader/BufWriter**:

```rust
use std::io::{BufReader, BufWriter, Write};

fn buffered_tcp_communication(stream: TcpStream) -> Result<(), Box<dyn std::error::Error>> {
    let mut reader = BufReader::new(stream.try_clone()?);
    let mut writer = BufWriter::new(stream);

    // 批量写入
    for i in 0..1000 {
        writeln!(writer, "Message {}", i)?;
    }
    writer.flush()?;

    Ok(())
}
```

---

### 4.6 处理TCP粘包

定义消息边界协议：

```rust
use std::io::{Read, Write};
use std::net::TcpStream;

struct FramedMessage {
    stream: TcpStream,
}

impl FramedMessage {
    fn new(stream: TcpStream) -> Self {
        Self { stream }
    }

    fn send(&mut self, data: &[u8]) -> std::io::Result<()> {
        // 发送长度 (4字节大端)
        let length = (data.len() as u32).to_be_bytes();
        self.stream.write_all(&length)?;

        // 发送数据
        self.stream.write_all(data)?;

        Ok(())
    }

    fn receive(&mut self) -> std::io::Result<Vec<u8>> {
        // 读取长度
        let mut length_buf = [0u8; 4];
        self.stream.read_exact(&mut length_buf)?;
        let length = u32::from_be_bytes(length_buf) as usize;

        // 读取数据
        let mut data = vec![0u8; length];
        self.stream.read_exact(&mut data)?;

        Ok(data)
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let stream = TcpStream::connect("127.0.0.1:8080")?;
    let mut framed = FramedMessage::new(stream);

    // 发送
    framed.send(b"Message 1")?;
    framed.send(b"Message 2")?;

    // 接收
    let msg1 = framed.receive()?;
    let msg2 = framed.receive()?;

    Ok(())
}
```

---

## 5. 共享内存

共享内存是最快的IPC机制，但需要careful handling和同步机制。

### 5.1 基础共享内存

使用 `shared_memory` crate:

```rust
use shared_memory::*;

fn shared_memory_example() -> Result<(), Box<dyn std::error::Error>> {
    // 创建共享内存
    let shmem = ShmemConf::new()
        .size(4096)
        .flink("my_shmem")
        .create()?;

    println!("✅ Created shared memory: {} bytes", shmem.len());

    // 写入数据
    unsafe {
        let ptr = shmem.as_ptr() as *mut u8;
        for i in 0..10 {
            ptr.add(i).write(i as u8);
        }
    }

    println!("📤 Wrote data to shared memory");
    Ok(())
}

fn read_shared_memory() -> Result<(), Box<dyn std::error::Error>> {
    // 打开现有共享内存
    let shmem = ShmemConf::new()
        .flink("my_shmem")
        .open()?;

    println!("✅ Opened shared memory");

    // 读取数据
    unsafe {
        let ptr = shmem.as_ptr();
        for i in 0..10 {
            let value = ptr.add(i).read();
            println!("📥 Read[{}] = {}", i, value);
        }
    }

    Ok(())
}
```

---

### 5.2 结构化共享内存

共享复杂数据结构：

```rust
use shared_memory::*;
use std::mem;

#[repr(C)]
#[derive(Debug, Clone)]
struct SharedData {
    counter: u64,
    values: [i32; 10],
    flag: bool,
}

impl Default for SharedData {
    fn default() -> Self {
        Self {
            counter: 0,
            values: [0; 10],
            flag: false,
        }
    }
}

fn create_structured_shmem() -> Result<(), Box<dyn std::error::Error>> {
    let shmem = ShmemConf::new()
        .size(mem::size_of::<SharedData>())
        .flink("struct_shmem")
        .create()?;

    unsafe {
        let ptr = shmem.as_ptr() as *mut SharedData;

        // 初始化
        ptr.write(SharedData {
            counter: 100,
            values: [1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
            flag: true,
        });
    }

    println!("✅ Initialized structured shared memory");
    Ok(())
}

fn read_structured_shmem() -> Result<(), Box<dyn std::error::Error>> {
    let shmem = ShmemConf::new()
        .flink("struct_shmem")
        .open()?;

    unsafe {
        let ptr = shmem.as_ptr() as *const SharedData;
        let data = ptr.read();

        println!("📥 Read data: {:?}", data);
    }

    Ok(())
}
```

---

### 5.3 带同步的共享内存

使用互斥锁保护共享数据：

```rust
use shared_memory::*;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};

#[repr(C)]
struct SynchronizedSharedMemory {
    lock: AtomicU64,  // 简单的自旋锁
    data: [u8; 4000],
}

impl SynchronizedSharedMemory {
    fn lock(&self) {
        while self.lock.compare_exchange(
            0, 1,
            Ordering::Acquire,
            Ordering::Relaxed
        ).is_err() {
            std::hint::spin_loop();
        }
    }

    fn unlock(&self) {
        self.lock.store(0, Ordering::Release);
    }
}

fn synchronized_write() -> Result<(), Box<dyn std::error::Error>> {
    let shmem = ShmemConf::new()
        .size(std::mem::size_of::<SynchronizedSharedMemory>())
        .flink("sync_shmem")
        .create()?;

    unsafe {
        let ptr = shmem.as_ptr() as *mut SynchronizedSharedMemory;

        // 获取锁
        (*ptr).lock();

        // 写入数据
        for i in 0..10 {
            (*ptr).data[i] = i as u8;
        }

        // 释放锁
        (*ptr).unlock();
    }

    Ok(())
}
```

---

### 5.4 环形缓冲区（Ring Buffer）

使用共享内存实现高性能环形缓冲区：

```rust
use std::sync::atomic::{AtomicUsize, Ordering};

#[repr(C)]
struct RingBuffer {
    write_pos: AtomicUsize,
    read_pos: AtomicUsize,
    capacity: usize,
    data: [u8; 4096],
}

impl RingBuffer {
    fn new(capacity: usize) -> Self {
        Self {
            write_pos: AtomicUsize::new(0),
            read_pos: AtomicUsize::new(0),
            capacity,
            data: [0; 4096],
        }
    }

    fn write(&mut self, byte: u8) -> bool {
        let write = self.write_pos.load(Ordering::Acquire);
        let read = self.read_pos.load(Ordering::Acquire);

        let next_write = (write + 1) % self.capacity;
        if next_write == read {
            return false;  // Buffer full
        }

        self.data[write] = byte;
        self.write_pos.store(next_write, Ordering::Release);
        true
    }

    fn read(&mut self) -> Option<u8> {
        let write = self.write_pos.load(Ordering::Acquire);
        let read = self.read_pos.load(Ordering::Acquire);

        if read == write {
            return None;  // Buffer empty
        }

        let byte = self.data[read];
        let next_read = (read + 1) % self.capacity;
        self.read_pos.store(next_read, Ordering::Release);
        Some(byte)
    }
}
```

---

### 5.5 共享内存性能测试

```rust
use std::time::Instant;
use shared_memory::*;

fn benchmark_shared_memory() -> Result<(), Box<dyn std::error::Error>> {
    let size = 1024 * 1024;  // 1MB
    let shmem = ShmemConf::new()
        .size(size)
        .flink("bench_shmem")
        .create()?;

    let iterations = 1_000_000;
    let start = Instant::now();

    unsafe {
        let ptr = shmem.as_ptr() as *mut u8;
        for i in 0..iterations {
            ptr.add(i % size).write((i % 256) as u8);
        }
    }

    let duration = start.elapsed();
    let throughput = (iterations as f64 / duration.as_secs_f64()) / 1_000_000.0;

    println!("📊 Throughput: {:.2} million ops/sec", throughput);
    println!("📊 Latency: {:.2} ns/op",
        duration.as_nanos() as f64 / iterations as f64);

    Ok(())
}
```

**性能对比**:

| 操作 | 共享内存 | Unix Socket | TCP Localhost |
|------|---------|-------------|---------------|
| 1-byte write | ~50 ns | ~2 μs | ~10 μs |
| 1KB write | ~100 ns | ~5 μs | ~15 μs |
| 1MB write | ~500 μs | ~5 ms | ~10 ms |

---

## 6. 选择合适的IPC机制

**决策树**:

```text
需要跨网络？
├─ 是 → TCP/UDP Socket
└─ 否
   ├─ 高性能大数据？
   │  └─ 是 → 共享内存
   └─ 否
      ├─ 父子进程？
      │  └─ 是 → 管道
      └─ 否 → Unix Socket
```

---

## 7. 实战案例

### 案例1: 统一的IPC抽象层

```rust
#[cfg(unix)]
use std::os::unix::net::UnixStream;
use serde::{Serialize, Deserialize};

pub trait IpcTransport: Send {
    fn send(&mut self, data: &[u8]) -> std::io::Result<()>;
    fn recv(&mut self) -> std::io::Result<Vec<u8>>;
}

pub enum IpcMessage {
    Text(String),
    Binary(Vec<u8>),
    Command { cmd: String, args: Vec<String> },
}

pub struct IpcChannel<T: IpcTransport> {
    transport: T,
}

impl<T: IpcTransport> IpcChannel<T> {
    pub fn new(transport: T) -> Self {
        Self { transport }
    }

    pub fn send(&mut self, msg: &IpcMessage) -> Result<(), Box<dyn std::error::Error>> {
        let data = bincode::serialize(msg)?;
        let length = (data.len() as u32).to_be_bytes();

        self.transport.send(&length)?;
        self.transport.send(&data)?;
        Ok(())
    }

    pub fn recv(&mut self) -> Result<IpcMessage, Box<dyn std::error::Error>> {
        let mut length_buf = [0u8; 4];
        let length_data = self.transport.recv()?;
        length_buf.copy_from_slice(&length_data[..4]);
        let length = u32::from_be_bytes(length_buf) as usize;

        let data = self.transport.recv()?;
        Ok(bincode::deserialize(&data[..length])?)
    }
}
```

---

### 案例2: RPC (远程过程调用)

```rust
use serde::{Serialize, Deserialize};

#[derive(Serialize, Deserialize, Debug)]
pub enum RpcRequest {
    Add { a: i32, b: i32 },
    Multiply { a: i32, b: i32 },
    Echo { message: String },
}

#[derive(Serialize, Deserialize, Debug)]
pub enum RpcResponse {
    Result(i32),
    Message(String),
    Error(String),
}

pub struct RpcServer {
    // implementation
}

impl RpcServer {
    pub fn handle_request(&self, req: RpcRequest) -> RpcResponse {
        match req {
            RpcRequest::Add { a, b } => RpcResponse::Result(a + b),
            RpcRequest::Multiply { a, b } => RpcResponse::Result(a * b),
            RpcRequest::Echo { message } => RpcResponse::Message(message),
        }
    }
}
```

---

## 8. 常见问题解答

### Q1: 如何选择合适的IPC机制？

**A**: 根据以下因素决策：

1. **性能要求**: 共享内存 > Unix Socket > 管道 > TCP
2. **跨网络需求**: 需要 → TCP/UDP；不需要 → 本地IPC
3. **复杂度容忍**: 简单 → 管道；复杂 → Socket/共享内存
4. **数据量**: 大数据 → 共享内存；小消息 → Socket/管道

---

### Q2: 如何处理IPC的背压（Backpressure）？

**A**: 实现流控机制：

```rust
struct FlowControl {
    max_queue_size: usize,
    current_size: AtomicUsize,
}

impl FlowControl {
    fn can_send(&self) -> bool {
        self.current_size.load(Ordering::Relaxed) < self.max_queue_size
    }

    fn on_send(&self) {
        self.current_size.fetch_add(1, Ordering::Release);
    }

    fn on_receive(&self) {
        self.current_size.fetch_sub(1, Ordering::Release);
    }
}
```

---

### Q3: 如何实现可靠的消息传递？

**A**: 添加确认机制：

```rust
#[derive(Serialize, Deserialize)]
enum Message {
    Data { id: u64, payload: Vec<u8> },
    Ack { id: u64 },
}

struct ReliableChannel {
    pending: HashMap<u64, Vec<u8>>,
    next_id: u64,
}

impl ReliableChannel {
    fn send_reliable(&mut self, data: Vec<u8>) -> u64 {
        let id = self.next_id;
        self.next_id += 1;
        self.pending.insert(id, data.clone());
        id
    }

    fn on_ack(&mut self, id: u64) {
        self.pending.remove(&id);
    }
}
```

---

### Q4: 如何处理IPC超时？

**A**: 使用timeout机制：

```rust
use std::time::Duration;

fn send_with_timeout(
    stream: &mut TcpStream,
    data: &[u8],
    timeout: Duration
) -> std::io::Result<()> {
    stream.set_write_timeout(Some(timeout))?;
    stream.write_all(data)?;
    stream.set_write_timeout(None)?;
    Ok(())
}
```

---

### Q5: 如何调试IPC问题？

**A**: 常用调试技巧：

1. **日志记录**:

    ```rust
    fn send_logged(stream: &mut TcpStream, data: &[u8]) -> std::io::Result<()> {
        eprintln!("[IPC] Sending {} bytes", data.len());
        stream.write_all(data)?;
        eprintln!("[IPC] Sent successfully");
        Ok(())
    }
    ```

2. **使用tcpdump/Wireshark** (网络IPC):

    ```bash
    tcpdump -i lo port 8080 -X
    ```

3. **使用strace** (Unix):

    ```bash
    strace -f -e trace=network your_program
    ```

---

## 9. 性能优化最佳实践

### 9.1 批处理

```rust
fn batch_send(stream: &mut TcpStream, messages: &[Vec<u8>]) -> std::io::Result<()> {
    // 合并多个消息
    let total_size: usize = messages.iter().map(|m| m.len()).sum();
    let mut buffer = Vec::with_capacity(total_size);

    for msg in messages {
        buffer.extend_from_slice(msg);
    }

    stream.write_all(&buffer)?;
    Ok(())
}
```

---

### 9.2 零拷贝

```rust
#[cfg(unix)]
use std::os::unix::io::AsRawFd;

#[cfg(target_os = "linux")]
fn sendfile_zero_copy(
    out_fd: &TcpStream,
    in_fd: &std::fs::File,
    count: usize
) -> std::io::Result<()> {
    unsafe {
        libc::sendfile(
            out_fd.as_raw_fd(),
            in_fd.as_raw_fd(),
            std::ptr::null_mut(),
            count
        );
    }
    Ok(())
}
```

---

### 9.3 连接复用

```rust
struct ConnectionPool {
    connections: Vec<TcpStream>,
    available: VecDeque<usize>,
}

impl ConnectionPool {
    fn acquire(&mut self) -> Option<&mut TcpStream> {
        self.available.pop_front()
            .map(|idx| &mut self.connections[idx])
    }

    fn release(&mut self, idx: usize) {
        self.available.push_back(idx);
    }
}
```

---

## 10. 安全注意事项

### 10.1 输入验证

```rust
fn validate_message(data: &[u8]) -> Result<(), String> {
    // 检查长度
    if data.len() > 1024 * 1024 {
        return Err("Message too large".to_string());
    }

    // 检查格式
    if data.len() < 4 {
        return Err("Message too short".to_string());
    }

    Ok(())
}
```

---

### 10.2 权限控制

```rust
#[cfg(unix)]
fn check_peer_uid(stream: &UnixStream) -> Result<u32, Box<dyn std::error::Error>> {
    #[cfg(target_os = "linux")]
    {
        use nix::sys::socket::{getsockopt, sockopt::PeerCredentials};
        use std::os::unix::io::AsRawFd;

        let creds = getsockopt(stream.as_raw_fd(), PeerCredentials)?;
        Ok(creds.uid())
    }

    #[cfg(not(target_os = "linux"))]
    {
        Err("Unsupported platform".into())
    }
}
```

---

## 下一步

- [进程管理快速入门](./01_进程管理快速入门.md)
- [异步进程管理](./03_异步进程管理.md)
- [IPC机制参考](../tier_03_references/02_IPC机制参考.md)

---

**文档维护**: Documentation Team
**创建日期**: 2025-10-22
**适用版本**: Rust 1.90+
