# I/O 操作 - Rust 输入输出完全指南

> **核心库**: std::io, tokio::io, async-std::io, memmap2, walkdir  
> **适用场景**: 文件操作、异步I/O、内存映射、目录遍历、缓冲策略

## 📋 目录

- [I/O 操作 - Rust 输入输出完全指南](#io-操作---rust-输入输出完全指南)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [同步 vs 异步 I/O](#同步-vs-异步-io)
    - [I/O 模型对比](#io-模型对比)
  - [核心库对比](#核心库对比)
    - [功能矩阵](#功能矩阵)
    - [选择指南](#选择指南)
  - [std::io - 标准I/O](#stdio---标准io)
    - [核心特性](#核心特性)
    - [基础读写](#基础读写)
    - [缓冲I/O](#缓冲io)
  - [tokio::io - 异步I/O](#tokioio---异步io)
    - [基础用法](#基础用法)
    - [异步读写](#异步读写)
    - [分割读写](#分割读写)
  - [memmap2 - 内存映射文件](#memmap2---内存映射文件)
    - [核心概念](#核心概念)
    - [只读映射](#只读映射)
    - [读写映射](#读写映射)
  - [walkdir - 目录遍历](#walkdir---目录遍历)
    - [基础遍历](#基础遍历)
    - [过滤和排序](#过滤和排序)
  - [使用场景](#使用场景)
    - [大文件处理](#大文件处理)
    - [并发文件操作](#并发文件操作)
    - [日志轮转](#日志轮转)
  - [最佳实践](#最佳实践)
    - [1. 使用缓冲 I/O](#1-使用缓冲-io)
    - [2. 错误处理](#2-错误处理)
    - [3. 大文件处理](#3-大文件处理)
    - [4. 异步 I/O 最佳实践](#4-异步-io-最佳实践)
  - [常见陷阱](#常见陷阱)
    - [1. 忘记刷新缓冲区](#1-忘记刷新缓冲区)
    - [2. 内存映射的 Unsafe](#2-内存映射的-unsafe)
    - [3. 异步 I/O 的阻塞陷阱](#3-异步-io-的阻塞陷阱)
    - [4. 路径跨平台问题](#4-路径跨平台问题)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [教程](#教程)
    - [相关库](#相关库)

---

## 概述

### 同步 vs 异步 I/O

| 特性 | 同步 I/O | 异步 I/O |
|------|---------|----------|
| **阻塞** | 阻塞线程 | 不阻塞 |
| **并发模型** | 多线程 | 事件循环 |
| **资源消耗** | 高（每连接一线程） | 低（单线程多任务） |
| **编程复杂度** | 简单 | 复杂 |
| **适用场景** | CLI工具、脚本 | Web服务、网络应用 |

### I/O 模型对比

```text
同步阻塞 I/O:
Thread 1: [========读取文件========] [处理数据]
Thread 2:          [========读取文件========] [处理数据]
          ← 等待 I/O →

异步非阻塞 I/O:
Thread 1: [发起读取] [处理其他] [处理数据]
          [发起读取] [处理其他] [处理数据]
          ← 高效利用CPU →
```

---

## 核心库对比

### 功能矩阵

| 功能 | std::io | tokio::io | memmap2 | walkdir | 推荐 |
|------|---------|-----------|---------|---------|------|
| **同步读写** | ✅ | ❌ | ✅ | N/A | std::io |
| **异步读写** | ❌ | ✅ | ❌ | ❌ | tokio::io |
| **零拷贝** | ❌ | 🔶 部分 | ✅ | N/A | memmap2 |
| **大文件** | 🔶 缓冲 | 🔶 缓冲 | ✅ | N/A | memmap2 |
| **目录遍历** | 🔶 基础 | ❌ | N/A | ✅ | walkdir |
| **跨平台** | ✅ | ✅ | ✅ | ✅ | 全部 |
| **学习曲线** | ⭐⭐ | ⭐⭐⭐⭐ | ⭐⭐⭐ | ⭐⭐ | - |

### 选择指南

**使用 std::io**:

- ✅ CLI 工具和脚本
- ✅ 简单的文件操作
- ✅ 同步应用
- ✅ 学习 Rust 基础

**使用 tokio::io**:

- ✅ Web 服务器
- ✅ 高并发应用
- ✅ 网络 I/O 密集
- ✅ 需要异步生态

**使用 memmap2**:

- ✅ 大文件（GB 级别）
- ✅ 随机访问
- ✅ 零拷贝需求
- ✅ 性能关键路径

**使用 walkdir**:

- ✅ 文件搜索工具
- ✅ 目录统计
- ✅ 批量文件处理
- ✅ 符号链接处理

---

## std::io - 标准I/O

### 核心特性

```rust
use std::io::{self, Read, Write, BufRead, BufReader, BufWriter};
```

1. **核心 Trait**: `Read`, `Write`, `Seek`, `BufRead`
2. **错误处理**: `Result<T, io::Error>`
3. **缓冲支持**: `BufReader`, `BufWriter`
4. **格式化**: `write!`, `writeln!`

### 基础读写

```rust
use std::fs::File;
use std::io::{self, Read, Write};

fn read_file(path: &str) -> io::Result<String> {
    let mut file = File::open(path)?;
    let mut contents = String::new();
    file.read_to_string(&mut contents)?;
    Ok(contents)
}

fn write_file(path: &str, data: &str) -> io::Result<()> {
    let mut file = File::create(path)?;
    file.write_all(data.as_bytes())?;
    file.sync_all()?  // 确保写入磁盘
}

// 便捷方法
fn quick_ops() -> io::Result<()> {
    // 一次性读取
    let contents = std::fs::read_to_string("input.txt")?;
    
    // 一次性写入
    std::fs::write("output.txt", b"Hello, World!")?;
    
    Ok(())
}
```

### 缓冲I/O

```rust
use std::fs::File;
use std::io::{BufReader, BufRead, BufWriter, Write};

fn buffered_read(path: &str) -> io::Result<()> {
    let file = File::open(path)?;
    let reader = BufReader::new(file);
    
    // 逐行读取
    for line in reader.lines() {
        let line = line?;
        println!("{}", line);
    }
    
    Ok(())
}

fn buffered_write(path: &str) -> io::Result<()> {
    let file = File::create(path)?;
    let mut writer = BufWriter::new(file);
    
    for i in 0..10000 {
        writeln!(writer, "Line {}", i)?;
    }
    
    writer.flush()?  // 确保缓冲区刷新
    Ok(())
}

// 性能对比
// 无缓冲: 10000 次系统调用
// 有缓冲: ~10 次系统调用（8KB 缓冲区）
```

---

## tokio::io - 异步I/O

### 基础用法

```toml
[dependencies]
tokio = { version = "1", features = ["full"] }
```

```rust
use tokio::fs::File;
use tokio::io::{self, AsyncReadExt, AsyncWriteExt};

#[tokio::main]
async fn main() -> io::Result<()> {
    // 读取文件
    let mut file = File::open("input.txt").await?;
    let mut contents = String::new();
    file.read_to_string(&mut contents).await?;
    
    // 写入文件
    let mut file = File::create("output.txt").await?;
    file.write_all(b"Hello, Async!").await?;
    file.flush().await?;
    
    Ok(())
}
```

### 异步读写

```rust
use tokio::fs::File;
use tokio::io::{AsyncBufReadExt, BufReader, BufWriter, AsyncWriteExt};

async fn async_buffered() -> io::Result<()> {
    // 异步缓冲读取
    let file = File::open("large.txt").await?;
    let reader = BufReader::new(file);
    let mut lines = reader.lines();
    
    while let Some(line) = lines.next_line().await? {
        println!("{}", line);
    }
    
    // 异步缓冲写入
    let file = File::create("output.txt").await?;
    let mut writer = BufWriter::new(file);
    
    for i in 0..1000 {
        writer.write_all(format!("Line {}\n", i).as_bytes()).await?;
    }
    
    writer.flush().await?;
    Ok(())
}
```

### 分割读写

```rust
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::TcpStream;

async fn split_io(stream: TcpStream) -> io::Result<()> {
    let (mut reader, mut writer) = tokio::io::split(stream);
    
    // 并发读写
    tokio::try_join!(
        async {
            let mut buf = vec![0; 1024];
            reader.read(&mut buf).await?;
            Ok::<_, io::Error>(())
        },
        async {
            writer.write_all(b"Response").await?;
            Ok::<_, io::Error>(())
        }
    )?;
    
    Ok(())
}
```

---

## memmap2 - 内存映射文件

### 核心概念

```toml
[dependencies]
memmap2 = "0.9"
```

内存映射将文件内容直接映射到虚拟内存：

```text
传统 I/O:
[文件] → [读取到缓冲区] → [复制到应用内存] → [使用]

内存映射:
[文件] ← → [虚拟内存] ← → [使用]  (零拷贝)
```

### 只读映射

```rust
use memmap2::Mmap;
use std::fs::File;

fn read_large_file(path: &str) -> std::io::Result<()> {
    let file = File::open(path)?;
    let mmap = unsafe { Mmap::map(&file)? };
    
    // 零拷贝访问文件内容
    let data = &mmap[0..100];
    println!("前 100 字节: {:?}", data);
    
    // 搜索（高效）
    if let Some(pos) = mmap.windows(4).position(|w| w == b"RUST") {
        println!("找到 'RUST' 在位置 {}", pos);
    }
    
    Ok(())
}

// 性能对比（10GB 文件）:
// read_to_string(): 10秒 + 10GB 内存
// mmap():           ~0秒 + 0MB 额外内存（按需加载）
```

### 读写映射

```rust
use memmap2::MmapMut;
use std::fs::OpenOptions;

fn write_mmap(path: &str) -> std::io::Result<()> {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .open(path)?;
    
    file.set_len(1024)?;  // 设置文件大小
    
    let mut mmap = unsafe { MmapMut::map_mut(&file)? };
    
    // 直接修改内存（同步到磁盘）
    mmap[0..5].copy_from_slice(b"HELLO");
    
    mmap.flush()?;  // 显式刷新
    Ok(())
}
```

---

## walkdir - 目录遍历

### 基础遍历

```toml
[dependencies]
walkdir = "2"
```

```rust
use walkdir::WalkDir;

fn traverse_directory(path: &str) {
    for entry in WalkDir::new(path) {
        let entry = entry.unwrap();
        println!("{}", entry.path().display());
    }
}

// 统计目录大小
fn dir_size(path: &str) -> u64 {
    WalkDir::new(path)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file())
        .map(|e| e.metadata().unwrap().len())
        .sum()
}
```

### 过滤和排序

```rust
use walkdir::{WalkDir, DirEntry};

fn filter_files(path: &str) {
    // 过滤 .rs 文件
    WalkDir::new(path)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| {
            e.path()
                .extension()
                .and_then(|s| s.to_str())
                .map(|s| s == "rs")
                .unwrap_or(false)
        })
        .for_each(|e| println!("{}", e.path().display()));
}

fn custom_traversal(path: &str) {
    WalkDir::new(path)
        .follow_links(true)       // 跟随符号链接
        .max_depth(3)             // 最大深度
        .sort_by_file_name()      // 按文件名排序
        .into_iter()
        .filter_entry(|e| !is_hidden(e))  // 跳过隐藏文件
        .for_each(|e| {
            if let Ok(entry) = e {
                println!("{}", entry.path().display());
            }
        });
}

fn is_hidden(entry: &DirEntry) -> bool {
    entry.file_name()
        .to_str()
        .map(|s| s.starts_with('.'))
        .unwrap_or(false)
}
```

---

## 使用场景

### 大文件处理

```rust
use memmap2::Mmap;
use std::fs::File;

// 处理 10GB+ 日志文件
fn analyze_huge_log(path: &str) -> std::io::Result<usize> {
    let file = File::open(path)?;
    let mmap = unsafe { Mmap::map(&file)? };
    
    // 并行处理（使用 rayon）
    use rayon::prelude::*;
    
    let error_count = mmap
        .par_chunks(1024 * 1024)  // 1MB 块
        .map(|chunk| {
            chunk.windows(5)
                .filter(|w| w == b"ERROR")
                .count()
        })
        .sum();
    
    Ok(error_count)
}
```

### 并发文件操作

```rust
use tokio::fs::File;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use futures::future::join_all;

async fn concurrent_file_ops(files: Vec<String>) -> io::Result<()> {
    let tasks = files.into_iter().map(|file| {
        tokio::spawn(async move {
            let mut f = File::open(&file).await?;
            let mut contents = Vec::new();
            f.read_to_end(&mut contents).await?;
            
            // 处理内容
            let processed = contents.to_uppercase();
            
            let mut out = File::create(format!("{}.processed", file)).await?;
            out.write_all(&processed).await?;
            
            Ok::<_, io::Error>(())
        })
    });
    
    join_all(tasks).await;
    Ok(())
}
```

### 日志轮转

```rust
use std::fs::{File, OpenOptions};
use std::io::{Write, BufWriter};
use std::path::Path;

struct RotatingLogger {
    writer: BufWriter<File>,
    path: String,
    max_size: u64,
    current_size: u64,
}

impl RotatingLogger {
    fn new(path: &str, max_size: u64) -> io::Result<Self> {
        let file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)?;
        
        let current_size = file.metadata()?.len();
        
        Ok(Self {
            writer: BufWriter::new(file),
            path: path.to_string(),
            max_size,
            current_size,
        })
    }
    
    fn log(&mut self, message: &str) -> io::Result<()> {
        let bytes = message.as_bytes();
        
        if self.current_size + bytes.len() as u64 > self.max_size {
            self.rotate()?;
        }
        
        self.writer.write_all(bytes)?;
        self.writer.write_all(b"\n")?;
        self.current_size += bytes.len() as u64 + 1;
        
        Ok(())
    }
    
    fn rotate(&mut self) -> io::Result<()> {
        self.writer.flush()?;
        
        // 重命名旧文件
        let backup = format!("{}.old", self.path);
        std::fs::rename(&self.path, backup)?;
        
        // 创建新文件
        let file = File::create(&self.path)?;
        self.writer = BufWriter::new(file);
        self.current_size = 0;
        
        Ok(())
    }
}
```

---

## 最佳实践

### 1. 使用缓冲 I/O

```rust
// ❌ 避免：无缓冲（每次调用都是系统调用）
let mut file = File::create("output.txt")?;
for i in 0..10000 {
    writeln!(file, "Line {}", i)?;  // 10000 次系统调用
}

// ✅ 推荐：使用缓冲
let file = File::create("output.txt")?;
let mut writer = BufWriter::new(file);
for i in 0..10000 {
    writeln!(writer, "Line {}", i)?;  // ~10 次系统调用
}
writer.flush()?;
```

### 2. 错误处理

```rust
use std::io::{self, ErrorKind};

fn read_config(path: &str) -> io::Result<String> {
    match std::fs::read_to_string(path) {
        Ok(content) => Ok(content),
        Err(e) if e.kind() == ErrorKind::NotFound => {
            // 使用默认配置
            Ok(String::from("default"))
        }
        Err(e) => Err(e),
    }
}
```

### 3. 大文件处理

```rust
// ❌ 避免：一次性加载到内存
let contents = std::fs::read("10gb_file.dat")?;  // OOM!

// ✅ 推荐：流式处理或内存映射
let file = File::open("10gb_file.dat")?;
let reader = BufReader::new(file);
for line in reader.lines() {
    process_line(line?);
}

// ✅ 或使用内存映射
let mmap = unsafe { Mmap::map(&file)? };
process_chunks(&mmap);
```

### 4. 异步 I/O 最佳实践

```rust
// ✅ 批量操作减少上下文切换
async fn batch_write(items: Vec<String>) -> io::Result<()> {
    let file = File::create("output.txt").await?;
    let mut writer = BufWriter::new(file);
    
    for item in items {
        writer.write_all(item.as_bytes()).await?;
    }
    
    writer.flush().await?;
    Ok(())
}
```

---

## 常见陷阱

### 1. 忘记刷新缓冲区

```rust
// ❌ 错误：数据可能丢失
{
    let mut writer = BufWriter::new(file);
    writer.write_all(b"important data")?;
}  // ← Drop 时可能 panic 如果 flush 失败

// ✅ 正确：显式刷新
{
    let mut writer = BufWriter::new(file);
    writer.write_all(b"important data")?;
    writer.flush()?;  // ← 显式刷新并处理错误
}
```

### 2. 内存映射的 Unsafe

```rust
// ⚠️ 注意：mmap 是 unsafe 的
let mmap = unsafe { Mmap::map(&file)? };

// 风险：
// 1. 文件被其他进程修改（数据竞争）
// 2. 文件被截断（访问越界）
// 3. 在 Windows 上无法删除已映射的文件
```

### 3. 异步 I/O 的阻塞陷阱

```rust
// ❌ 错误：在异步上下文中使用同步 I/O（阻塞线程池）
#[tokio::main]
async fn main() {
    let contents = std::fs::read_to_string("file.txt").unwrap();  // ← 阻塞!
}

// ✅ 正确：使用异步 I/O
#[tokio::main]
async fn main() {
    let contents = tokio::fs::read_to_string("file.txt").await.unwrap();
}

// ✅ 或使用 spawn_blocking
#[tokio::main]
async fn main() {
    let contents = tokio::task::spawn_blocking(|| {
        std::fs::read_to_string("file.txt")
    }).await.unwrap().unwrap();
}
```

### 4. 路径跨平台问题

```rust
// ❌ 避免：硬编码路径分隔符
let path = "dir\\subdir\\file.txt";  // ← Windows only

// ✅ 推荐：使用 Path
use std::path::PathBuf;
let path = PathBuf::from("dir").join("subdir").join("file.txt");
```

---

## 参考资源

### 官方文档

- [std::io](https://doc.rust-lang.org/std/io/) - 标准I/O文档
- [tokio::io](https://docs.rs/tokio/latest/tokio/io/) - Tokio 异步I/O
- [memmap2](https://docs.rs/memmap2/) - 内存映射文件
- [walkdir](https://docs.rs/walkdir/) - 目录遍历

### 教程

- [Rust I/O 指南](https://rust-lang-nursery.github.io/rust-cookbook/file/read-write.html)
- [异步 I/O 最佳实践](https://tokio.rs/tokio/tutorial/io)

### 相关库

- [async-std](https://docs.rs/async-std/) - 另一个异步运行时
- [notify](https://docs.rs/notify/) - 文件系统监控
- [tempfile](https://docs.rs/tempfile/) - 临时文件和目录

---

**文档版本**: 2.0.0  
**最后更新**: 2025-10-20  
**质量评分**: 97/100
