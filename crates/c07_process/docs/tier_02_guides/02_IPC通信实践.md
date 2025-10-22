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
  - [3. Unix Socket](#3-unix-socket)
  - [4. TCP Socket](#4-tcp-socket)
  - [5. 共享内存](#5-共享内存)
  - [6. 选择合适的IPC机制](#6-选择合适的ipc机制)
  - [7. 实战案例](#7-实战案例)

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

**基础管道**:

```rust
use std::process::{Command, Stdio};
use std::io::Write;

let mut child = Command::new("cat")
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .spawn()?;

// 写入
if let Some(mut stdin) = child.stdin.take() {
    stdin.write_all(b"Hello Pipe!")?;
}

// 读取
let output = child.wait_with_output()?;
println!("{}", String::from_utf8_lossy(&output.stdout));
```

**管道链**:

```rust
let ls = Command::new("ls")
    .stdout(Stdio::piped())
    .spawn()?;

let grep = Command::new("grep")
    .arg("txt")
    .stdin(ls.stdout.unwrap())
    .stdout(Stdio::piped())
    .spawn()?;

let output = grep.wait_with_output()?;
```

---

## 3. Unix Socket

**服务端**:

```rust
#[cfg(unix)]
use std::os::unix::net::{UnixListener, UnixStream};
use std::io::{Read, Write};

let listener = UnixListener::bind("/tmp/my.sock")?;

for stream in listener.incoming() {
    let mut stream = stream?;
    let mut buf = [0; 1024];
    let n = stream.read(&mut buf)?;
    stream.write_all(&buf[..n])?;  // echo
}
```

**客户端**:

```rust
let mut stream = UnixStream::connect("/tmp/my.sock")?;
stream.write_all(b"Hello")?;

let mut response = String::new();
stream.read_to_string(&mut response)?;
println!("{}", response);
```

---

## 4. TCP Socket

**服务端**:

```rust
use std::net::{TcpListener, TcpStream};
use std::io::{Read, Write};

let listener = TcpListener::bind("127.0.0.1:8080")?;

for stream in listener.incoming() {
    let mut stream = stream?;
    let mut buf = [0; 1024];
    let n = stream.read(&mut buf)?;
    stream.write_all(&buf[..n])?;
}
```

**客户端**:

```rust
let mut stream = TcpStream::connect("127.0.0.1:8080")?;
stream.write_all(b"Hello TCP")?;

let mut response = Vec::new();
stream.read_to_end(&mut response)?;
```

---

## 5. 共享内存

使用 `shared_memory` crate:

```rust
use shared_memory::*;

// 创建
let shmem = ShmemConf::new()
    .size(4096)
    .flink("my_shmem")
    .create()?;

// 写入
unsafe {
    let ptr = shmem.as_ptr() as *mut u8;
    *ptr = 42;
}

// 其他进程打开
let shmem = ShmemConf::new()
    .flink("my_shmem")
    .open()?;

// 读取
unsafe {
    let ptr = shmem.as_ptr();
    let value = *ptr;
}
```

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

**案例: 简单的IPC库**:

```rust
pub enum IpcMessage {
    Text(String),
    Binary(Vec<u8>),
}

pub struct IpcChannel {
    stream: UnixStream,
}

impl IpcChannel {
    pub fn connect(path: &str) -> Result<Self, std::io::Error> {
        Ok(Self {
            stream: UnixStream::connect(path)?,
        })
    }
    
    pub fn send(&mut self, msg: &IpcMessage) -> Result<(), Box<dyn std::error::Error>> {
        let data = bincode::serialize(msg)?;
        self.stream.write_all(&data)?;
        Ok(())
    }
    
    pub fn recv(&mut self) -> Result<IpcMessage, Box<dyn std::error::Error>> {
        let mut buf = Vec::new();
        self.stream.read_to_end(&mut buf)?;
        Ok(bincode::deserialize(&buf)?)
    }
}
```

---

**参考**: [IPC机制参考](../tier_03_references/02_IPC机制参考.md)

---

**文档维护**: Documentation Team  
**创建日期**: 2025-10-22  
**适用版本**: Rust 1.90+
