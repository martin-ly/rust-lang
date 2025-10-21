# 进程与系统接口

> **核心库**: nix, sysinfo, signal-hook, daemonize, libc  
> **适用场景**: 进程管理、信号处理、系统信息监控、守护进程、系统调用

---

## 📋 目录

- [进程与系统接口](#进程与系统接口)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [进程管理概念](#进程管理概念)
    - [为什么需要系统接口](#为什么需要系统接口)
  - [核心库对比](#核心库对比)
    - [功能矩阵](#功能矩阵)
    - [选择指南](#选择指南)
  - [nix - Unix 系统接口](#nix---unix-系统接口)
    - [核心特性](#核心特性)
    - [进程管理](#进程管理)
      - [基础用法：fork 和 exec](#基础用法fork-和-exec)
      - [高级用法：管道通信](#高级用法管道通信)
    - [信号处理高级用法](#信号处理高级用法)
      - [阻塞信号](#阻塞信号)
      - [注册信号处理器](#注册信号处理器)
    - [文件描述符操作](#文件描述符操作)
      - [文件锁](#文件锁)
      - [文件描述符复制 (dup2)](#文件描述符复制-dup2)
  - [sysinfo - 系统信息](#sysinfo---系统信息)
    - [核心特性1](#核心特性1)
    - [系统监控](#系统监控)
      - [基础用法：系统概览](#基础用法系统概览)
      - [高级用法：实时监控](#高级用法实时监控)
    - [进程监控](#进程监控)
      - [进程列表和详情](#进程列表和详情)
      - [进程监控（持续）](#进程监控持续)
  - [signal-hook - 异步信号](#signal-hook---异步信号)
    - [核心特性2](#核心特性2)
    - [优雅关闭](#优雅关闭)
      - [模式1: AtomicBool (同步)](#模式1-atomicbool-同步)
      - [模式2: Tokio Channel (异步)](#模式2-tokio-channel-异步)
    - [信号转发](#信号转发)
      - [子进程信号转发](#子进程信号转发)
  - [实战场景](#实战场景)
    - [场景1: 系统监控服务](#场景1-系统监控服务)
    - [场景2: 优雅关闭的长期服务](#场景2-优雅关闭的长期服务)
    - [场景3: 进程守护和重启](#场景3-进程守护和重启)
  - [最佳实践](#最佳实践)
    - [1. 优先使用类型安全的封装](#1-优先使用类型安全的封装)
    - [2. 信号处理使用 signal-hook](#2-信号处理使用-signal-hook)
    - [3. 优雅关闭超时机制](#3-优雅关闭超时机制)
    - [4. 系统信息刷新优化](#4-系统信息刷新优化)
    - [5. 进程管理错误处理](#5-进程管理错误处理)
  - [常见陷阱](#常见陷阱)
    - [⚠️ 陷阱1: 信号处理器中的不安全操作](#️-陷阱1-信号处理器中的不安全操作)
    - [⚠️ 陷阱2: 忘记关闭文件描述符](#️-陷阱2-忘记关闭文件描述符)
    - [⚠️ 陷阱3: sysinfo 的刷新频率](#️-陷阱3-sysinfo-的刷新频率)
    - [⚠️ 陷阱4: 子进程僵尸进程](#️-陷阱4-子进程僵尸进程)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [教程与文章](#教程与文章)
    - [示例项目](#示例项目)
    - [相关文档](#相关文档)

---

## 概述

### 进程管理概念

在系统编程中，进程管理是核心能力之一。Rust 提供了安全且高性能的系统接口封装，涵盖：

- **进程生命周期**: 创建、监控、终止进程
- **信号处理**: 优雅关闭、资源清理、错误恢复
- **系统信息**: CPU、内存、磁盘、网络监控
- **文件描述符**: 管道、重定向、IPC通信
- **守护进程**: 后台服务、系统级应用

```text
┌─────────────────────────────────────────┐
│          应用程序进程                    │
├─────────────────────────────────────────┤
│  signal-hook  │  sysinfo  │  daemonize  │
│      nix      │   libc    │   std::fs   │
├─────────────────────────────────────────┤
│         操作系统内核 (Linux/Unix)        │
└─────────────────────────────────────────┘
```

### 为什么需要系统接口

1. **优雅关闭**: 处理 SIGTERM/SIGINT，清理资源
2. **性能监控**: 实时追踪 CPU、内存使用
3. **进程管理**: 启动子进程、管道通信
4. **守护进程**: 编写系统级服务
5. **系统调用**: 访问底层系统功能

**Rust 优势**:

- 类型安全的系统调用封装
- 编译时检查防止常见错误
- 零成本抽象，性能等同 C
- 跨平台抽象（nix + sysinfo）

---

## 核心库对比

### 功能矩阵

| 特性 | nix | sysinfo | signal-hook | libc | 说明 |
|------|-----|---------|-------------|------|------|
| **进程创建** | ✅ fork/exec | ❌ | ❌ | ✅ | nix 提供安全封装 |
| **信号处理** | ✅ | ❌ | ✅ 异步安全 | ✅ | signal-hook 更易用 |
| **系统信息** | ❌ | ✅ 跨平台 | ❌ | 部分 | sysinfo 最全面 |
| **文件描述符** | ✅ | ❌ | ❌ | ✅ | nix 类型安全 |
| **跨平台** | ❌ Unix | ✅ | ✅ | ❌ | sysinfo 支持 Win |
| **类型安全** | ✅ | ✅ | ✅ | ❌ 裸指针 | 优先 nix/sysinfo |
| **异步支持** | 部分 | ✅ | ✅ | ❌ | signal-hook 异步友好 |

### 选择指南

| 场景 | 推荐库 | 理由 |
|------|--------|------|
| **系统监控** | sysinfo | 跨平台、API简单、实时刷新 |
| **优雅关闭** | signal-hook | 异步安全、与 tokio 集成 |
| **进程管理** | nix | fork/exec 安全封装、管道通信 |
| **跨平台兼容** | sysinfo + signal-hook | 两者都支持 Win/Unix |
| **底层系统调用** | nix + libc | nix 优先，libc 作为后备 |
| **守护进程** | daemonize + signal-hook | 完整的守护进程支持 |

---

## nix - Unix 系统接口

### 核心特性

- ✅ **类型安全**: 将 libc 封装为安全的 Rust API
- ✅ **完整覆盖**: 进程、信号、文件、网络、时间等
- ✅ **零成本抽象**: 编译后等同直接调用 libc
- ✅ **错误处理**: 使用 Result 而非 errno

**安装**:

```toml
[dependencies]
nix = { version = "0.27", features = ["process", "signal"] }
```

### 进程管理

#### 基础用法：fork 和 exec

```rust
use nix::unistd::{fork, ForkResult, execv};
use nix::sys::wait::waitpid;
use std::ffi::CString;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    match unsafe { fork()? } {
        ForkResult::Parent { child } => {
            println!("父进程: PID = {}, 子进程 PID = {}", 
                std::process::id(), child);
            
            // 等待子进程结束
            let status = waitpid(child, None)?;
            println!("子进程退出状态: {:?}", status);
        }
        ForkResult::Child => {
            println!("子进程: PID = {}", std::process::id());
            
            // 执行新程序
            let prog = CString::new("/bin/ls").unwrap();
            let args = vec![CString::new("ls").unwrap(), 
                           CString::new("-la").unwrap()];
            execv(&prog, &args)?;
        }
    }
    
    Ok(())
}
```

**说明**:

1. `fork()` 创建当前进程的副本
2. 父进程获得子进程的 PID
3. 子进程返回 `Child`，可以 exec 执行新程序
4. `waitpid()` 阻塞等待子进程结束

#### 高级用法：管道通信

```rust
use nix::unistd::{fork, ForkResult, pipe, close, read, write};
use std::os::unix::io::RawFd;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建管道 (read_fd, write_fd)
    let (read_fd, write_fd) = pipe()?;
    
    match unsafe { fork()? } {
        ForkResult::Parent { child } => {
            // 父进程关闭写端，读取数据
            close(write_fd)?;
            
            let mut buf = [0u8; 1024];
            let n = read(read_fd, &mut buf)?;
            let msg = String::from_utf8_lossy(&buf[..n]);
            
            println!("父进程收到: {}", msg);
            close(read_fd)?;
        }
        ForkResult::Child => {
            // 子进程关闭读端，写入数据
            close(read_fd)?;
            
            let data = b"Hello from child process!";
            write(write_fd, data)?;
            close(write_fd)?;
            
            std::process::exit(0);
        }
    }
    
    Ok(())
}
```

**要点**:

- 管道是单向的：读端 → 写端
- 关闭不使用的文件描述符（防止泄漏）
- 子进程使用 `exit(0)` 而非 `return`

### 信号处理高级用法

#### 阻塞信号

```rust
use nix::sys::signal::{Signal, SigSet, SigmaskHow, sigprocmask};
use std::time::Duration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建信号集，添加 SIGINT
    let mut sigset = SigSet::empty();
    sigset.add(Signal::SIGINT);
    
    // 阻塞 SIGINT
    sigprocmask(SigmaskHow::SIG_BLOCK, Some(&sigset), None)?;
    
    println!("SIGINT 已阻塞，按 Ctrl+C 不会退出...");
    std::thread::sleep(Duration::from_secs(5));
    
    // 解除阻塞
    sigprocmask(SigmaskHow::SIG_UNBLOCK, Some(&sigset), None)?;
    
    println!("SIGINT 已解除阻塞");
    std::thread::sleep(Duration::from_secs(5));
    
    Ok(())
}
```

#### 注册信号处理器

```rust
use nix::sys::signal::{Signal, SigHandler, signal};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

static SHUTDOWN: AtomicBool = AtomicBool::new(false);

extern "C" fn handle_sigterm(_: i32) {
    SHUTDOWN.store(true, Ordering::SeqCst);
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 注册 SIGTERM 处理器
    unsafe {
        signal(Signal::SIGTERM, SigHandler::Handler(handle_sigterm))?;
    }
    
    println!("服务启动，发送 SIGTERM 优雅关闭...");
    
    while !SHUTDOWN.load(Ordering::SeqCst) {
        // 主循环
        std::thread::sleep(std::time::Duration::from_secs(1));
    }
    
    println!("收到 SIGTERM，正在清理资源...");
    // 清理逻辑
    
    Ok(())
}
```

**警告**:

- 信号处理器必须是 `async-signal-safe`
- 避免在处理器中分配内存或调用 println!
- 优先使用 `signal-hook`（更安全）

### 文件描述符操作

#### 文件锁

```rust
use nix::fcntl::{flock, FlockArg};
use std::fs::File;
use std::os::unix::io::AsRawFd;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let file = File::create("/tmp/lockfile")?;
    let fd = file.as_raw_fd();
    
    // 尝试获取排他锁（非阻塞）
    match flock(fd, FlockArg::LockExclusiveNonblock) {
        Ok(_) => {
            println!("获取文件锁成功");
            
            // 临界区代码
            std::thread::sleep(std::time::Duration::from_secs(5));
            
            // 释放锁
            flock(fd, FlockArg::Unlock)?;
        }
        Err(e) => {
            eprintln!("文件已被锁定: {}", e);
        }
    }
    
    Ok(())
}
```

#### 文件描述符复制 (dup2)

```rust
use nix::unistd::dup2;
use std::fs::OpenOptions;
use std::os::unix::io::AsRawFd;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let logfile = OpenOptions::new()
        .create(true)
        .append(true)
        .open("/tmp/output.log")?;
    
    // 将 stdout 重定向到日志文件
    dup2(logfile.as_raw_fd(), 1)?; // 1 = stdout
    
    println!("这条消息会写入 /tmp/output.log");
    eprintln!("stderr 仍然显示在终端");
    
    Ok(())
}
```

---

## sysinfo - 系统信息

### 核心特性1

- ✅ **跨平台**: Linux、macOS、Windows、BSD
- ✅ **实时刷新**: 动态更新系统状态
- ✅ **零依赖**: 纯 Rust 实现（除系统 API）
- ✅ **详细信息**: CPU、内存、磁盘、网络、进程

**安装**:

```toml
[dependencies]
sysinfo = "0.30"
```

### 系统监控

#### 基础用法：系统概览

```rust
use sysinfo::{System, SystemExt, CpuExt, ProcessExt};

fn main() {
    let mut sys = System::new_all();
    sys.refresh_all();
    
    // 系统信息
    println!("系统名称: {}", System::name().unwrap_or_default());
    println!("内核版本: {}", System::kernel_version().unwrap_or_default());
    println!("OS 版本: {}", System::os_version().unwrap_or_default());
    println!("主机名: {}", System::host_name().unwrap_or_default());
    
    // CPU 信息
    println!("\nCPU 信息:");
    println!("  物理核心数: {}", sys.physical_core_count().unwrap_or(0));
    println!("  逻辑核心数: {}", sys.cpus().len());
    println!("  全局 CPU 使用率: {:.2}%", sys.global_cpu_info().cpu_usage());
    
    // 内存信息
    println!("\n内存信息:");
    let total_mem = sys.total_memory();
    let used_mem = sys.used_memory();
    let available_mem = sys.available_memory();
    
    println!("  总内存: {} GB", total_mem / 1024 / 1024 / 1024);
    println!("  已用: {} GB ({:.2}%)", 
        used_mem / 1024 / 1024 / 1024,
        (used_mem as f64 / total_mem as f64) * 100.0);
    println!("  可用: {} GB", available_mem / 1024 / 1024 / 1024);
    
    // Swap 信息
    println!("\nSwap:");
    println!("  总量: {} GB", sys.total_swap() / 1024 / 1024 / 1024);
    println!("  已用: {} GB", sys.used_swap() / 1024 / 1024 / 1024);
}
```

#### 高级用法：实时监控

```rust
use sysinfo::{System, SystemExt, CpuExt, NetworkExt, DiskExt};
use std::time::Duration;
use std::thread;

fn main() {
    let mut sys = System::new_all();
    
    loop {
        // 刷新特定数据（更高效）
        sys.refresh_cpu();
        sys.refresh_memory();
        sys.refresh_networks();
        
        // 清屏
        print!("\x1B[2J\x1B[1;1H");
        
        println!("=== 系统监控 ===\n");
        
        // CPU 使用率（每个核心）
        println!("CPU 使用率:");
        for (i, cpu) in sys.cpus().iter().enumerate() {
            print!("  CPU{:2}: ", i);
            print_bar(cpu.cpu_usage(), 100.0);
            println!(" {:.1}%", cpu.cpu_usage());
        }
        
        // 内存使用
        println!("\n内存:");
        let mem_percent = (sys.used_memory() as f64 / sys.total_memory() as f64) * 100.0;
        print!("  ");
        print_bar(mem_percent, 100.0);
        println!(" {:.1}% ({}/{} GB)", 
            mem_percent,
            sys.used_memory() / 1024 / 1024 / 1024,
            sys.total_memory() / 1024 / 1024 / 1024);
        
        // 网络流量
        println!("\n网络:");
        for (name, data) in sys.networks() {
            println!("  {}: ↓ {} KB/s, ↑ {} KB/s",
                name,
                data.received() / 1024,
                data.transmitted() / 1024);
        }
        
        thread::sleep(Duration::from_secs(2));
    }
}

fn print_bar(value: f64, max: f64) {
    let width = 30;
    let filled = ((value / max) * width as f64) as usize;
    print!("[");
    for i in 0..width {
        if i < filled {
            print!("█");
        } else {
            print!(" ");
        }
    }
    print!("]");
}
```

### 进程监控

#### 进程列表和详情

```rust
use sysinfo::{System, SystemExt, ProcessExt, Pid};

fn main() {
    let mut sys = System::new_all();
    sys.refresh_all();
    
    // 当前进程信息
    let current_pid = Pid::from(std::process::id() as usize);
    if let Some(process) = sys.process(current_pid) {
        println!("当前进程:");
        println!("  PID: {}", process.pid());
        println!("  名称: {}", process.name());
        println!("  内存: {} MB", process.memory() / 1024);
        println!("  CPU: {:.2}%", process.cpu_usage());
        println!("  启动时间: {} 秒前", process.run_time());
    }
    
    // 所有进程（按内存排序，取前10）
    println!("\n内存占用最高的进程:");
    let mut processes: Vec<_> = sys.processes().values().collect();
    processes.sort_by(|a, b| b.memory().cmp(&a.memory()));
    
    for process in processes.iter().take(10) {
        println!("  {:>6} | {:20} | {:>6} MB | {:>5.1}%",
            process.pid(),
            process.name(),
            process.memory() / 1024,
            process.cpu_usage());
    }
    
    // 查找特定进程
    println!("\n查找 'rust' 相关进程:");
    for (pid, process) in sys.processes() {
        if process.name().to_lowercase().contains("rust") {
            println!("  [{}] {} - {} MB",
                pid, process.name(), process.memory() / 1024);
        }
    }
}
```

#### 进程监控（持续）

```rust
use sysinfo::{System, SystemExt, ProcessExt, Pid};
use std::time::Duration;
use std::thread;

fn main() {
    let target_pid = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .expect("用法: cargo run -- <PID>");
    
    let pid = Pid::from(target_pid);
    let mut sys = System::new();
    
    loop {
        sys.refresh_process(pid);
        
        if let Some(process) = sys.process(pid) {
            println!("[{}] {} - CPU: {:.2}%, Mem: {} MB",
                pid,
                process.name(),
                process.cpu_usage(),
                process.memory() / 1024);
        } else {
            println!("进程 {} 已退出", pid);
            break;
        }
        
        thread::sleep(Duration::from_secs(1));
    }
}
```

---

## signal-hook - 异步信号

### 核心特性2

- ✅ **异步安全**: 不会在信号处理器中执行危险操作
- ✅ **Tokio 集成**: 与 async 运行时无缝集成
- ✅ **多种模式**: flag、迭代器、channel
- ✅ **优雅关闭**: 常用的关闭模式

**安装**:

```toml
[dependencies]
signal-hook = "0.3"
signal-hook-tokio = { version = "0.3", features = ["futures-v0_3"] }
tokio = { version = "1", features = ["full"] }
```

### 优雅关闭

#### 模式1: AtomicBool (同步)

```rust
use signal_hook::{consts::TERM_SIGNALS, flag};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let term = Arc::new(AtomicBool::new(false));
    
    // 注册多个终止信号 (SIGTERM, SIGINT, SIGQUIT)
    for sig in TERM_SIGNALS {
        flag::register(*sig, Arc::clone(&term))?;
    }
    
    println!("服务运行中... (Ctrl+C 优雅关闭)");
    
    while !term.load(Ordering::Relaxed) {
        // 主业务逻辑
        println!("处理请求...");
        std::thread::sleep(Duration::from_secs(1));
    }
    
    println!("收到关闭信号，开始清理资源...");
    
    // 优雅关闭逻辑
    graceful_shutdown();
    
    println!("清理完成，进程退出");
    Ok(())
}

fn graceful_shutdown() {
    println!("  1. 停止接收新请求");
    std::thread::sleep(Duration::from_millis(500));
    
    println!("  2. 等待现有请求完成");
    std::thread::sleep(Duration::from_millis(500));
    
    println!("  3. 关闭数据库连接");
    std::thread::sleep(Duration::from_millis(500));
    
    println!("  4. 刷新日志缓冲");
}
```

#### 模式2: Tokio Channel (异步)

```rust
use signal_hook::consts::signal::*;
use signal_hook_tokio::Signals;
use futures::stream::StreamExt;
use tokio::time::{sleep, Duration};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut signals = Signals::new(&[SIGTERM, SIGINT, SIGHUP])?;
    let handle = signals.handle();
    
    // 生成信号处理任务
    let signals_task = tokio::spawn(async move {
        while let Some(signal) = signals.next().await {
            match signal {
                SIGTERM | SIGINT => {
                    println!("收到终止信号，优雅关闭...");
                    return true; // 关闭
                }
                SIGHUP => {
                    println!("收到 SIGHUP，重新加载配置...");
                    reload_config().await;
                }
                _ => unreachable!(),
            }
        }
        false
    });
    
    // 主业务循环
    let main_task = tokio::spawn(async {
        loop {
            println!("处理异步任务...");
            sleep(Duration::from_secs(1)).await;
        }
    });
    
    // 等待信号
    let should_terminate = signals_task.await?;
    
    if should_terminate {
        // 优雅关闭
        println!("停止主任务...");
        main_task.abort();
        
        graceful_shutdown_async().await;
    }
    
    handle.close();
    Ok(())
}

async fn reload_config() {
    println!("  重新加载配置文件...");
    sleep(Duration::from_millis(100)).await;
}

async fn graceful_shutdown_async() {
    println!("  关闭连接池...");
    sleep(Duration::from_millis(500)).await;
    
    println!("  保存状态到磁盘...");
    sleep(Duration::from_millis(500)).await;
}
```

### 信号转发

#### 子进程信号转发

```rust
use signal_hook::{consts::*, iterator::Signals};
use std::process::{Command, Child};
use std::thread;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 启动子进程
    let mut child = Command::new("sleep")
        .arg("3600")
        .spawn()?;
    
    println!("子进程 PID: {}", child.id());
    
    // 监听信号
    let mut signals = Signals::new(&[SIGTERM, SIGINT])?;
    
    thread::spawn(move || {
        for sig in signals.forever() {
            println!("收到信号 {}, 转发给子进程", sig);
            
            // 转发信号给子进程 (Unix only)
            #[cfg(unix)]
            {
                use nix::sys::signal::{kill, Signal};
                use nix::unistd::Pid;
                
                let signal = match sig {
                    SIGTERM => Signal::SIGTERM,
                    SIGINT => Signal::SIGINT,
                    _ => continue,
                };
                
                if let Err(e) = kill(Pid::from_raw(child.id() as i32), signal) {
                    eprintln!("转发信号失败: {}", e);
                }
            }
        }
    });
    
    // 等待子进程
    let status = child.wait()?;
    println!("子进程退出: {:?}", status);
    
    Ok(())
}
```

---

## 实战场景

### 场景1: 系统监控服务

**需求描述**: 编写一个轻量级系统监控服务，记录 CPU、内存、磁盘使用情况到日志文件，支持优雅关闭。

**完整实现**:

```rust
use sysinfo::{System, SystemExt, CpuExt, DiskExt};
use signal_hook::{consts::TERM_SIGNALS, flag};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;
use std::thread;
use std::fs::OpenOptions;
use std::io::Write;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 初始化
    let term = Arc::new(AtomicBool::new(false));
    for sig in TERM_SIGNALS {
        flag::register(*sig, Arc::clone(&term))?;
    }
    
    let mut sys = System::new_all();
    let mut logfile = OpenOptions::new()
        .create(true)
        .append(true)
        .open("/tmp/system_monitor.log")?;
    
    println!("系统监控服务启动...");
    
    // 主循环：每10秒记录一次
    let mut interval = 0;
    while !term.load(Ordering::Relaxed) {
        sys.refresh_all();
        
        // 收集指标
        let cpu_usage = sys.global_cpu_info().cpu_usage();
        let mem_total = sys.total_memory();
        let mem_used = sys.used_memory();
        let mem_percent = (mem_used as f64 / mem_total as f64) * 100.0;
        
        // 磁盘使用
        let mut disk_info = String::new();
        for disk in sys.disks() {
            let usage = (disk.total_space() - disk.available_space()) as f64 
                / disk.total_space() as f64 * 100.0;
            disk_info.push_str(&format!("{}:{:.1}% ", 
                disk.mount_point().display(), usage));
        }
        
        // 写入日志
        let log_entry = format!(
            "[{}] CPU: {:.2}%, Mem: {:.2}%, Disks: {}\n",
            chrono::Local::now().format("%Y-%m-%d %H:%M:%S"),
            cpu_usage,
            mem_percent,
            disk_info
        );
        
        logfile.write_all(log_entry.as_bytes())?;
        logfile.flush()?;
        
        if interval % 6 == 0 {
            print!("{}", log_entry);
        }
        
        interval += 1;
        thread::sleep(Duration::from_secs(10));
    }
    
    println!("监控服务停止");
    Ok(())
}
```

**要点说明**:

1. 使用 `append` 模式打开日志文件
2. 每10秒刷新系统信息（`refresh_all`）
3. 计算 CPU、内存、磁盘百分比
4. 优雅关闭时自动 flush 日志

### 场景2: 优雅关闭的长期服务

**需求描述**: Web 服务需要在收到 SIGTERM 时停止接收新连接，等待现有请求完成，然后退出。

**完整实现**:

```rust
use signal_hook_tokio::Signals;
use futures::stream::StreamExt;
use tokio::sync::broadcast;
use tokio::time::{sleep, Duration, timeout};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 创建关闭信号 channel
    let (shutdown_tx, _) = broadcast::channel::<()>(1);
    let active_requests = Arc::new(AtomicUsize::new(0));
    
    // 注册信号处理
    let mut signals = Signals::new(&[signal_hook::consts::SIGTERM, 
                                      signal_hook::consts::SIGINT])?;
    let shutdown_tx_clone = shutdown_tx.clone();
    
    tokio::spawn(async move {
        if let Some(_) = signals.next().await {
            println!("收到关闭信号");
            let _ = shutdown_tx_clone.send(());
        }
    });
    
    // 模拟多个工作任务
    for i in 0..5 {
        let mut shutdown_rx = shutdown_tx.subscribe();
        let active = Arc::clone(&active_requests);
        
        tokio::spawn(async move {
            loop {
                tokio::select! {
                    _ = shutdown_rx.recv() => {
                        println!("Worker {} 停止接收新请求", i);
                        break;
                    }
                    _ = sleep(Duration::from_secs(2)) => {
                        // 模拟处理请求
                        active.fetch_add(1, Ordering::SeqCst);
                        println!("Worker {} 处理请求 (活跃: {})", 
                            i, active.load(Ordering::SeqCst));
                        
                        sleep(Duration::from_secs(3)).await;
                        
                        active.fetch_sub(1, Ordering::SeqCst);
                        println!("Worker {} 完成请求 (剩余: {})", 
                            i, active.load(Ordering::SeqCst));
                    }
                }
            }
        });
    }
    
    println!("服务启动，5个 worker 运行中...");
    
    // 等待关闭信号
    let mut shutdown_rx = shutdown_tx.subscribe();
    let _ = shutdown_rx.recv().await;
    
    // 优雅关闭：等待所有请求完成（最多30秒）
    println!("开始优雅关闭...");
    
    let shutdown_timeout = Duration::from_secs(30);
    let result = timeout(shutdown_timeout, async {
        loop {
            let active = active_requests.load(Ordering::SeqCst);
            if active == 0 {
                break;
            }
            println!("等待 {} 个请求完成...", active);
            sleep(Duration::from_secs(1)).await;
        }
    }).await;
    
    match result {
        Ok(_) => println!("所有请求已完成，干净退出"),
        Err(_) => println!("超时，强制退出（{} 个请求未完成）",
            active_requests.load(Ordering::SeqCst)),
    }
    
    Ok(())
}
```

**要点说明**:

1. 使用 `broadcast` channel 广播关闭信号
2. 每个 worker 通过 `tokio::select!` 监听关闭信号
3. 跟踪活跃请求数量（`AtomicUsize`）
4. 设置关闭超时（30秒）防止无限等待

### 场景3: 进程守护和重启

**需求描述**: 监控子进程，如果意外退出则自动重启，支持手动停止。

**完整实现**:

```rust
use std::process::{Command, Child};
use std::time::{Duration, Instant};
use signal_hook::{consts::*, iterator::Signals};
use std::thread;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let running = Arc::new(AtomicBool::new(true));
    let running_clone = Arc::clone(&running);
    
    // 信号处理线程
    thread::spawn(move || {
        let mut signals = Signals::new(&[SIGTERM, SIGINT]).unwrap();
        for _ in signals.forever() {
            println!("收到关闭信号，停止守护进程");
            running_clone.store(false, Ordering::SeqCst);
        }
    });
    
    let mut restart_count = 0;
    let mut last_start = Instant::now();
    
    println!("进程守护器启动");
    
    while running.load(Ordering::SeqCst) {
        println!("启动子进程 (重启次数: {})", restart_count);
        
        let mut child = Command::new("your-program")
            .spawn()
            .expect("启动子进程失败");
        
        let child_pid = child.id();
        println!("子进程 PID: {}", child_pid);
        
        // 等待子进程结束
        match child.wait() {
            Ok(status) => {
                println!("子进程退出: {:?}", status);
                
                // 检查是否快速重启（可能是配置错误）
                let uptime = last_start.elapsed();
                if uptime < Duration::from_secs(10) {
                    println!("警告：子进程在 {:?} 内退出，可能存在问题", uptime);
                    
                    if restart_count >= 5 {
                        println!("错误：短时间内重启5次，停止守护");
                        break;
                    }
                    
                    println!("等待5秒后重启...");
                    thread::sleep(Duration::from_secs(5));
                }
                
                restart_count += 1;
                last_start = Instant::now();
            }
            Err(e) => {
                eprintln!("等待子进程失败: {}", e);
                break;
            }
        }
    }
    
    println!("守护进程退出");
    Ok(())
}
```

**要点说明**:

1. 检测子进程运行时长，防止快速重启循环
2. 限制短时间内重启次数（5次）
3. 信号转发（SIGTERM → 子进程）
4. 记录重启次数和最后启动时间

---

## 最佳实践

### 1. 优先使用类型安全的封装

**描述**: 优先使用 `nix` 和 `sysinfo` 而非直接调用 `libc`。

✅ **推荐**:

```rust
use nix::unistd::getpid;

fn main() {
    let pid = getpid();
    println!("PID: {}", pid);
}
```

❌ **避免**:

```rust
use libc::getpid;

fn main() {
    let pid = unsafe { getpid() };
    println!("PID: {}", pid);
}
```

### 2. 信号处理使用 signal-hook

**描述**: `signal-hook` 比直接使用 `signal()` 更安全，尤其在异步环境。

✅ **推荐**:

```rust
use signal_hook::{consts::SIGINT, flag};
use std::sync::Arc;
use std::sync::atomic::AtomicBool;

let term = Arc::new(AtomicBool::new(false));
flag::register(SIGINT, Arc::clone(&term))?;
```

❌ **避免**:

```rust
// 容易死锁或 UB
unsafe {
    signal(SIGINT, SigHandler::Handler(my_handler));
}
```

### 3. 优雅关闭超时机制

**描述**: 始终为优雅关闭设置超时，防止无限等待。

```rust
use tokio::time::{timeout, Duration};

let shutdown_timeout = Duration::from_secs(30);

match timeout(shutdown_timeout, graceful_shutdown()).await {
    Ok(_) => println!("优雅关闭完成"),
    Err(_) => {
        println!("超时，强制退出");
        std::process::exit(1);
    }
}
```

### 4. 系统信息刷新优化

**描述**: 只刷新需要的数据，避免 `refresh_all()` 开销。

```rust
// ❌ 低效：刷新所有数据
sys.refresh_all();

// ✅ 高效：只刷新需要的
sys.refresh_cpu();
sys.refresh_memory();
```

### 5. 进程管理错误处理

**描述**: 进程操作可能失败，必须处理错误。

```rust
use nix::unistd::fork;

match unsafe { fork() } {
    Ok(ForkResult::Parent { child }) => {
        // 父进程逻辑
    }
    Ok(ForkResult::Child) => {
        // 子进程逻辑
    }
    Err(e) => {
        eprintln!("fork 失败: {}", e);
        std::process::exit(1);
    }
}
```

---

## 常见陷阱

### ⚠️ 陷阱1: 信号处理器中的不安全操作

**问题描述**: 在信号处理器中调用非 async-signal-safe 函数（如 `println!`、`malloc`）会导致死锁或崩溃。

❌ **错误示例**:

```rust
extern "C" fn handler(_: i32) {
    println!("收到信号"); // ❌ 死锁风险！
    std::process::exit(0);
}

unsafe {
    signal(SIGINT, SigHandler::Handler(handler));
}
```

✅ **正确做法**:

```rust
use signal_hook::flag;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

let term = Arc::new(AtomicBool::new(false));
flag::register(SIGINT, Arc::clone(&term))?;

// 在主循环中检查
while !term.load(Ordering::Relaxed) {
    // ...
}
println!("收到信号"); // ✅ 安全
```

### ⚠️ 陷阱2: 忘记关闭文件描述符

**问题描述**: fork 后忘记关闭不使用的管道端会导致泄漏。

❌ **错误示例**:

```rust
let (read_fd, write_fd) = pipe()?;

match unsafe { fork()? } {
    ForkResult::Parent { .. } => {
        // ❌ 忘记关闭 write_fd
        let mut buf = [0u8; 1024];
        read(read_fd, &mut buf)?;
    }
    ForkResult::Child => {
        // ❌ 忘记关闭 read_fd
        write(write_fd, b"data")?;
    }
}
```

✅ **正确做法**:

```rust
match unsafe { fork()? } {
    ForkResult::Parent { .. } => {
        close(write_fd)?; // ✅ 关闭不用的端
        read(read_fd, &mut buf)?;
        close(read_fd)?;
    }
    ForkResult::Child => {
        close(read_fd)?; // ✅ 关闭不用的端
        write(write_fd, b"data")?;
        close(write_fd)?;
        std::process::exit(0);
    }
}
```

### ⚠️ 陷阱3: sysinfo 的刷新频率

**问题描述**: `refresh_all()` 在循环中调用会导致高 CPU 占用。

❌ **错误示例**:

```rust
loop {
    sys.refresh_all(); // ❌ 每次循环都刷新所有数据
    let cpu = sys.global_cpu_info().cpu_usage();
    println!("{}", cpu);
}
```

✅ **正确做法**:

```rust
loop {
    sys.refresh_cpu(); // ✅ 只刷新需要的
    let cpu = sys.global_cpu_info().cpu_usage();
    println!("{}", cpu);
    
    thread::sleep(Duration::from_secs(1)); // ✅ 限制刷新频率
}
```

### ⚠️ 陷阱4: 子进程僵尸进程

**问题描述**: fork 后如果不 `waitpid()`，子进程会变成僵尸进程。

❌ **错误示例**:

```rust
match unsafe { fork()? } {
    ForkResult::Parent { child } => {
        println!("子进程: {}", child);
        // ❌ 没有 waitpid，子进程成为僵尸
    }
    ForkResult::Child => {
        std::process::exit(0);
    }
}
```

✅ **正确做法**:

```rust
match unsafe { fork()? } {
    ForkResult::Parent { child } => {
        println!("子进程: {}", child);
        waitpid(child, None)?; // ✅ 回收子进程
    }
    ForkResult::Child => {
        std::process::exit(0);
    }
}
```

---

## 参考资源

### 官方文档

- 📚 [nix 文档](https://docs.rs/nix/latest/nix/)
- 📚 [sysinfo 文档](https://docs.rs/sysinfo/latest/sysinfo/)
- 📚 [signal-hook 文档](https://docs.rs/signal-hook/latest/signal_hook/)

### 教程与文章

- 📖 [Unix 系统编程 - Rust 实现](https://www.lurklurk.org/effective-rust/)
- 📖 [优雅关闭模式](https://tokio.rs/tokio/topics/shutdown)
- 📖 [Rust 进程管理指南](https://rust-cli.github.io/book/)

### 示例项目

- 💻 [systemd-service-rs](https://github.com/systemd/systemd-service-rs) - 系统服务示例
- 💻 [htop-rs](https://github.com/cjbassi/htop-rs) - 系统监控工具

### 相关文档

- 🔗 [并发编程](../sync_primitives/README.md)
- 🔗 [异步运行时](../async_runtime/README.md)
- 🔗 [日志系统](../../05_toolchain/logging/README.md)

---

**文档版本**: 2.0.0  
**最后更新**: 2025-10-20  
**维护者**: Rust 学习社区
