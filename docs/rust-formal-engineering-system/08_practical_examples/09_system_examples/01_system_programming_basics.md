# 系统编程基础（System Programming Basics）

> **创建日期**: 2025-11-15
> **最后更新**: 2025-11-15
> **Rust 版本**: 1.91.1+ (Edition 2024) ✅
> **状态**: ✅ 已完善

---

## 📊 目录

- [系统编程基础（System Programming Basics）](#系统编程基础system-programming-basics)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [文件系统操作](#文件系统操作)
    - [文件读写](#文件读写)
    - [目录操作](#目录操作)
    - [文件元数据](#文件元数据)
  - [进程管理](#进程管理)
    - [创建子进程](#创建子进程)
    - [异步进程执行](#异步进程执行)
    - [进程间通信](#进程间通信)
  - [网络编程](#网络编程)
    - [TCP 服务器](#tcp-服务器)
    - [TCP 客户端](#tcp-客户端)
    - [UDP 通信](#udp-通信)
  - [实践示例](#实践示例)
    - [示例 1：文件监控](#示例-1文件监控)
    - [示例 2：日志轮转](#示例-2日志轮转)
    - [示例 3：系统资源监控](#示例-3系统资源监控)
  - [最佳实践](#最佳实践)
    - [1. 错误处理](#1-错误处理)
    - [2. 异步操作](#2-异步操作)
    - [3. 资源清理](#3-资源清理)
  - [参考资料](#参考资料)

---

## 概述

Rust 在系统编程领域具有显著优势，包括内存安全、零成本抽象和强大的并发支持。本示例展示 Rust 系统编程的基础知识。

## 文件系统操作

### 文件读写

```rust
use std::fs;
use std::io::{self, Read, Write};

fn read_file(path: &str) -> io::Result<String> {
    fs::read_to_string(path)
}

fn write_file(path: &str, content: &str) -> io::Result<()> {
    fs::write(path, content)
}

fn read_file_binary(path: &str) -> io::Result<Vec<u8>> {
    fs::read(path)
}

fn write_file_binary(path: &str, data: &[u8]) -> io::Result<()> {
    fs::write(path, data)
}
```

### 目录操作

```rust
use std::fs;
use std::path::Path;

fn create_directory(path: &str) -> io::Result<()> {
    fs::create_dir_all(path)
}

fn list_directory(path: &str) -> io::Result<Vec<String>> {
    let entries = fs::read_dir(path)?;
    let mut files = Vec::new();

    for entry in entries {
        let entry = entry?;
        let path = entry.path();
        if let Some(name) = path.file_name() {
            files.push(name.to_string_lossy().to_string());
        }
    }

    Ok(files)
}

fn remove_directory(path: &str) -> io::Result<()> {
    fs::remove_dir_all(path)
}
```

### 文件元数据

```rust
use std::fs;
use std::time::SystemTime;

fn get_file_metadata(path: &str) -> io::Result<()> {
    let metadata = fs::metadata(path)?;

    println!("文件大小: {} 字节", metadata.len());
    println!("是否为文件: {}", metadata.is_file());
    println!("是否为目录: {}", metadata.is_dir());

    if let Ok(modified) = metadata.modified() {
        println!("修改时间: {:?}", modified);
    }

    Ok(())
}
```

## 进程管理

### 创建子进程

```rust
use std::process::{Command, Stdio};

fn run_command() -> io::Result<()> {
    let output = Command::new("ls")
        .arg("-la")
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()?;

    println!("状态码: {}", output.status.code().unwrap_or(-1));
    println!("标准输出:\n{}", String::from_utf8_lossy(&output.stdout));

    if !output.stderr.is_empty() {
        eprintln!("标准错误:\n{}", String::from_utf8_lossy(&output.stderr));
    }

    Ok(())
}
```

### 异步进程执行

```rust
use tokio::process::Command;

async fn run_command_async() -> io::Result<()> {
    let mut child = Command::new("ls")
        .arg("-la")
        .stdout(Stdio::piped())
        .spawn()?;

    let output = child.wait_with_output().await?;
    println!("输出:\n{}", String::from_utf8_lossy(&output.stdout));

    Ok(())
}
```

### 进程间通信

```rust
use std::process::{Command, Stdio};
use std::io::Write;

fn pipe_commands() -> io::Result<()> {
    let mut echo = Command::new("echo")
        .arg("hello world")
        .stdout(Stdio::piped())
        .spawn()?;

    let echo_output = echo.stdout.take().ok_or_else(|| {
        io::Error::new(io::ErrorKind::Other, "无法获取标准输出")
    })?;

    let mut grep = Command::new("grep")
        .arg("hello")
        .stdin(echo_output)
        .stdout(Stdio::piped())
        .spawn()?;

    let output = grep.wait_with_output()?;
    println!("结果: {}", String::from_utf8_lossy(&output.stdout));

    Ok(())
}
```

## 网络编程

### TCP 服务器

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

async fn tcp_server() -> io::Result<()> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;
    println!("服务器监听在 127.0.0.1:8080");

    loop {
        let (mut socket, addr) = listener.accept().await?;
        println!("新连接: {}", addr);

        tokio::spawn(async move {
            let mut buf = [0; 1024];

            loop {
                match socket.read(&mut buf).await {
                    Ok(0) => break,
                    Ok(n) => {
                        if socket.write_all(&buf[..n]).await.is_err() {
                            break;
                        }
                    }
                    Err(_) => break,
                }
            }
        });
    }
}
```

### TCP 客户端

```rust
async fn tcp_client() -> io::Result<()> {
    let mut stream = TcpStream::connect("127.0.0.1:8080").await?;

    stream.write_all(b"Hello, server!").await?;

    let mut buf = [0; 1024];
    let n = stream.read(&mut buf).await?;
    println!("收到: {}", String::from_utf8_lossy(&buf[..n]));

    Ok(())
}
```

### UDP 通信

```rust
use tokio::net::UdpSocket;

async fn udp_server() -> io::Result<()> {
    let socket = UdpSocket::bind("127.0.0.1:8080").await?;
    let mut buf = [0; 1024];

    loop {
        let (len, addr) = socket.recv_from(&mut buf).await?;
        println!("收到来自 {} 的消息: {}", addr, String::from_utf8_lossy(&buf[..len]));

        socket.send_to(&buf[..len], addr).await?;
    }
}

async fn udp_client() -> io::Result<()> {
    let socket = UdpSocket::bind("127.0.0.1:0").await?;
    socket.connect("127.0.0.1:8080").await?;

    socket.send(b"Hello, UDP!").await?;

    let mut buf = [0; 1024];
    let len = socket.recv(&mut buf).await?;
    println!("收到: {}", String::from_utf8_lossy(&buf[..len]));

    Ok(())
}
```

## 实践示例

### 示例 1：文件监控

```rust
use std::path::Path;
use std::time::Duration;
use tokio::time::sleep;

async fn monitor_file(path: &str) -> io::Result<()> {
    let path = Path::new(path);
    let mut last_modified = None;

    loop {
        if let Ok(metadata) = fs::metadata(path) {
            if let Ok(modified) = metadata.modified() {
                if last_modified != Some(modified) {
                    println!("文件已修改: {:?}", modified);
                    last_modified = Some(modified);
                }
            }
        }

        sleep(Duration::from_secs(1)).await;
    }
}
```

### 示例 2：日志轮转

```rust
use std::fs::OpenOptions;
use std::io::Write;

pub struct LogRotator {
    log_file: String,
    max_size: u64,
}

impl LogRotator {
    pub fn new(log_file: String, max_size: u64) -> Self {
        LogRotator { log_file, max_size }
    }

    pub fn write_log(&self, message: &str) -> io::Result<()> {
        let metadata = fs::metadata(&self.log_file)?;

        if metadata.len() > self.max_size {
            self.rotate_log()?;
        }

        let mut file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&self.log_file)?;

        writeln!(file, "{}", message)?;
        Ok(())
    }

    fn rotate_log(&self) -> io::Result<()> {
        let backup = format!("{}.old", self.log_file);
        fs::rename(&self.log_file, &backup)?;
        Ok(())
    }
}
```

### 示例 3：系统资源监控

```rust
use std::process::Command;

pub struct SystemMonitor;

impl SystemMonitor {
    pub fn get_cpu_usage() -> io::Result<String> {
        let output = Command::new("top")
            .arg("-bn1")
            .arg("|")
            .arg("grep")
            .arg("Cpu(s)")
            .output()?;

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }

    pub fn get_memory_usage() -> io::Result<String> {
        let output = Command::new("free")
            .arg("-h")
            .output()?;

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }

    pub fn get_disk_usage() -> io::Result<String> {
        let output = Command::new("df")
            .arg("-h")
            .output()?;

        Ok(String::from_utf8_lossy(&output.stdout).to_string())
    }
}
```

## 最佳实践

### 1. 错误处理

```rust
use std::io;

fn handle_file_operation() -> io::Result<()> {
    match fs::read_to_string("file.txt") {
        Ok(content) => {
            println!("文件内容: {}", content);
            Ok(())
        }
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            eprintln!("文件不存在");
            Ok(())
        }
        Err(e) => Err(e),
    }
}
```

### 2. 异步操作

```rust
use tokio::fs;

async fn async_file_operations() -> io::Result<()> {
    let content = fs::read_to_string("file.txt").await?;
    fs::write("output.txt", content).await?;
    Ok(())
}
```

### 3. 资源清理

```rust
use std::fs::File;

fn with_file<F>(path: &str, f: F) -> io::Result<()>
where
    F: FnOnce(&mut File) -> io::Result<()>,
{
    let mut file = File::open(path)?;
    f(&mut file)?;
    // 文件自动关闭
    Ok(())
}
```

## 参考资料

- [系统示例索引](./00_index.md)
- [实践示例索引](../00_index.md)
- [Tokio 文档](https://docs.rs/tokio/)
- [标准库文档](https://doc.rust-lang.org/std/)

---

**导航**:

- 返回索引: [`00_index.md`](./00_index.md)
- 返回实践示例: [`../00_index.md`](../00_index.md)
