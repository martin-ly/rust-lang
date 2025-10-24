# Rust 调试完整指南

> **学习目标**：掌握 Rust 程序调试的完整技术栈，从基础调试到生产环境问题排查。

---


## 📊 目录

- [📖 目录](#目录)
- [调试基础](#调试基础)
  - [Rust 调试的独特性](#rust-调试的独特性)
  - [调试符号](#调试符号)
  - [编译配置](#编译配置)
- [命令行调试](#命令行调试)
  - [使用 `println!` 调试](#使用-println-调试)
  - [使用 `dbg!` 宏](#使用-dbg-宏)
  - [使用 `log` 框架](#使用-log-框架)
- [GDB 调试](#gdb-调试)
  - [基本用法](#基本用法)
  - [常用命令](#常用命令)
  - [Rust 特定功能](#rust-特定功能)
- [LLDB 调试](#lldb-调试)
  - [基本用法1](#基本用法1)
  - [常用命令1](#常用命令1)
  - [Rust 插件](#rust-插件)
- [IDE 集成调试](#ide-集成调试)
  - [VS Code 调试](#vs-code-调试)
  - [IntelliJ IDEA/CLion 调试](#intellij-ideaclion-调试)
- [异步代码调试](#异步代码调试)
  - [Tokio Console](#tokio-console)
  - [异步调试技巧](#异步调试技巧)
- [性能调试](#性能调试)
  - [火焰图](#火焰图)
  - [Perf 分析](#perf-分析)
  - [内存分析](#内存分析)
- [并发调试](#并发调试)
  - [死锁检测](#死锁检测)
  - [数据竞争](#数据竞争)
  - [线程追踪](#线程追踪)
- [错误处理调试](#错误处理调试)
  - [panic 分析](#panic-分析)
  - [错误传播追踪](#错误传播追踪)
  - [自定义 panic hook](#自定义-panic-hook)
- [内存调试](#内存调试)
  - [Valgrind](#valgrind)
  - [AddressSanitizer](#addresssanitizer)
  - [内存泄漏检测](#内存泄漏检测)
- [调试最佳实践](#调试最佳实践)
  - [调试策略](#调试策略)
  - [可调试性设计](#可调试性设计)
  - [日志规范](#日志规范)
- [实战案例](#实战案例)
  - [案例1：死锁调试](#案例1死锁调试)
  - [案例2：内存泄漏排查](#案例2内存泄漏排查)
  - [案例3：性能瓶颈分析](#案例3性能瓶颈分析)
- [总结](#总结)
  - [调试工具总结](#调试工具总结)
  - [调试建议](#调试建议)
  - [持续学习](#持续学习)
- [相关资源](#相关资源)


## 📖 目录

- [Rust 调试完整指南](#rust-调试完整指南)
  - [📖 目录](#-目录)
  - [调试基础](#调试基础)
    - [Rust 调试的独特性](#rust-调试的独特性)
    - [调试符号](#调试符号)
    - [编译配置](#编译配置)
  - [命令行调试](#命令行调试)
    - [使用 `println!` 调试](#使用-println-调试)
    - [使用 `dbg!` 宏](#使用-dbg-宏)
    - [使用 `log` 框架](#使用-log-框架)
  - [GDB 调试](#gdb-调试)
    - [基本用法](#基本用法)
    - [常用命令](#常用命令)
    - [Rust 特定功能](#rust-特定功能)
  - [LLDB 调试](#lldb-调试)
    - [基本用法1](#基本用法1)
    - [常用命令1](#常用命令1)
    - [Rust 插件](#rust-插件)
  - [IDE 集成调试](#ide-集成调试)
    - [VS Code 调试](#vs-code-调试)
    - [IntelliJ IDEA/CLion 调试](#intellij-ideaclion-调试)
  - [异步代码调试](#异步代码调试)
    - [Tokio Console](#tokio-console)
    - [异步调试技巧](#异步调试技巧)
  - [性能调试](#性能调试)
    - [火焰图](#火焰图)
    - [Perf 分析](#perf-分析)
    - [内存分析](#内存分析)
  - [并发调试](#并发调试)
    - [死锁检测](#死锁检测)
    - [数据竞争](#数据竞争)
    - [线程追踪](#线程追踪)
  - [错误处理调试](#错误处理调试)
    - [panic 分析](#panic-分析)
    - [错误传播追踪](#错误传播追踪)
    - [自定义 panic hook](#自定义-panic-hook)
  - [内存调试](#内存调试)
    - [Valgrind](#valgrind)
    - [AddressSanitizer](#addresssanitizer)
    - [内存泄漏检测](#内存泄漏检测)
  - [调试最佳实践](#调试最佳实践)
    - [调试策略](#调试策略)
    - [可调试性设计](#可调试性设计)
    - [日志规范](#日志规范)
  - [实战案例](#实战案例)
    - [案例1：死锁调试](#案例1死锁调试)
    - [案例2：内存泄漏排查](#案例2内存泄漏排查)
    - [案例3：性能瓶颈分析](#案例3性能瓶颈分析)
  - [总结](#总结)
    - [调试工具总结](#调试工具总结)
    - [调试建议](#调试建议)
    - [持续学习](#持续学习)
  - [相关资源](#相关资源)

---

## 调试基础

### Rust 调试的独特性

Rust 的调试与传统语言有所不同：

```text
传统语言调试          vs      Rust 调试
├─ 空指针问题常见             ├─ 借用检查器消除空指针
├─ 内存泄漏频发               ├─ RAII 自动管理内存
├─ 数据竞争难查               ├─ 编译时防止数据竞争
├─ 未定义行为隐蔽             ├─ 安全性保证最小化 UB
└─ 运行时错误多样             └─ panic 和 Result 明确
```

**Rust 调试优势**：

1. **编译时捕获**：大量错误在编译期被捕获
2. **清晰的错误信息**：借用检查器提供详细错误提示
3. **类型安全**：减少类型相关的运行时错误
4. **内存安全**：自动管理内存，减少内存问题

**Rust 调试挑战**：

1. **优化激进**：Release 模式优化可能影响调试
2. **宏展开**：宏错误定位较困难
3. **异步复杂**：async/await 调试需要特殊工具
4. **所有权语义**：理解变量生命周期对调试很重要

### 调试符号

调试符号包含源代码位置、变量名等信息：

```toml
# Cargo.toml
[profile.dev]
opt-level = 0        # 不优化，便于调试
debug = true         # 包含完整调试信息
split-debuginfo = "packed"  # 调试信息打包方式

[profile.release]
opt-level = 3        # 最大优化
debug = false        # 不包含调试信息

[profile.release-with-debug]
inherits = "release"
debug = true         # Release + 调试符号
strip = "none"       # 不剥离符号
```

### 编译配置

```bash
# 开发模式（默认包含调试符号）
cargo build

# Release 模式（包含调试符号）
cargo build --profile release-with-debug

# 查看二进制文件是否包含调试符号
file target/debug/my_app
# 输出: ELF 64-bit ... not stripped

# 使用 rust-gdb/rust-lldb
rust-gdb target/debug/my_app
rust-lldb target/debug/my_app
```

---

## 命令行调试

### 使用 `println!` 调试

最简单的调试方法：

```rust
fn calculate(x: i32, y: i32) -> i32 {
    println!("calculate called with x={}, y={}", x, y);
    
    let result = x * 2 + y;
    println!("intermediate result: {}", result);
    
    let final_result = result / 2;
    println!("final_result: {}", final_result);
    
    final_result
}

// 使用 {:?} 调试打印
#[derive(Debug)]
struct Point {
    x: i32,
    y: i32,
}

fn main() {
    let p = Point { x: 10, y: 20 };
    println!("Point: {:?}", p);      // Debug 格式
    println!("Point: {:#?}", p);     // Pretty-print
}
```

### 使用 `dbg!` 宏

更强大的调试宏（自动打印文件名、行号、变量名）：

```rust
fn main() {
    let x = 5;
    let y = 10;
    
    // dbg! 返回表达式的值，可以插入到任何地方
    let result = dbg!(x + y);
    
    // 打印复杂表达式
    dbg!(x * 2 + y * 3);
    
    // 在链式调用中使用
    let numbers = vec![1, 2, 3, 4, 5];
    let sum: i32 = numbers
        .iter()
        .map(|n| dbg!(n * 2))  // 每个元素都会被打印
        .sum();
    
    dbg!(sum);
}

// 输出示例:
// [src/main.rs:6] x + y = 15
// [src/main.rs:9] x * 2 + y * 3 = 40
```

**条件调试**：

```rust
#[cfg(debug_assertions)]
macro_rules! debug_println {
    ($($arg:tt)*) => {
        eprintln!($($arg)*);
    };
}

#[cfg(not(debug_assertions))]
macro_rules! debug_println {
    ($($arg:tt)*) => {};
}

fn main() {
    debug_println!("This only prints in debug builds");
}
```

### 使用 `log` 框架

生产级日志记录：

```rust
use log::{debug, info, warn, error, trace};
use env_logger;

fn main() {
    // 初始化日志
    env_logger::init();
    
    trace!("Trace message");      // 最详细
    debug!("Debug message");      // 调试信息
    info!("Info message");        // 一般信息
    warn!("Warning message");     // 警告
    error!("Error message");      // 错误
}

// 使用示例：
fn process_data(data: &[u8]) -> Result<(), std::io::Error> {
    debug!("Processing {} bytes of data", data.len());
    
    if data.is_empty() {
        warn!("Empty data received");
        return Ok(());
    }
    
    // 处理逻辑
    info!("Successfully processed data");
    Ok(())
}
```

**日志级别控制**：

```bash
# 设置日志级别
RUST_LOG=debug cargo run

# 按模块设置
RUST_LOG=my_crate=debug,other_crate=info cargo run

# 只显示特定模块
RUST_LOG=my_crate::module=trace cargo run
```

---

## GDB 调试

### 基本用法

```bash
# 启动 GDB
rust-gdb target/debug/my_app

# 或者直接附加参数
rust-gdb --args target/debug/my_app arg1 arg2
```

### 常用命令

```gdb
# 启动和控制
(gdb) run                   # 运行程序
(gdb) start                 # 开始执行，在 main 停止
(gdb) continue              # 继续执行
(gdb) quit                  # 退出 GDB

# 断点
(gdb) break main            # 在 main 函数设置断点
(gdb) break file.rs:42      # 在文件的第42行设置断点
(gdb) break my_function     # 在函数设置断点
(gdb) info breakpoints      # 列出所有断点
(gdb) delete 1              # 删除断点1

# 单步执行
(gdb) next                  # 单步执行（不进入函数）
(gdb) step                  # 单步执行（进入函数）
(gdb) finish                # 执行到当前函数返回
(gdb) until 50              # 执行到第50行

# 检查变量
(gdb) print variable        # 打印变量值
(gdb) print *pointer        # 解引用指针
(gdb) info locals           # 显示所有局部变量
(gdb) info args             # 显示函数参数

# 调用栈
(gdb) backtrace             # 显示调用栈
(gdb) frame 2               # 切换到栈帧2
(gdb) up                    # 向上移动栈帧
(gdb) down                  # 向下移动栈帧
```

### Rust 特定功能

```gdb
# 查看 Rust 类型
(gdb) print my_vector
# $1 = Vec(size=3) = {1, 2, 3}

# 查看 Option 类型
(gdb) print my_option
# $2 = Some(42)

# 查看 Result 类型
(gdb) print my_result
# $3 = Ok("success")

# 查看字符串切片
(gdb) print my_str
# $4 = "Hello, Rust!"

# Rust 表达式求值
(gdb) print my_struct.field_name
(gdb) print my_vec.len()
```

**使用 `.gdbinit` 配置**：

```bash
# ~/.gdbinit
set pagination off
set print pretty on
set print array on
set print array-indexes on

# Rust 特定设置
python
import sys
sys.path.insert(0, '/path/to/rust/src/etc')
import gdb_rust_pretty_printer
gdb_rust_pretty_printer.register_printers(gdb)
end
```

---

## LLDB 调试

### 基本用法1

```bash
# 启动 LLDB
rust-lldb target/debug/my_app

# 或者
lldb target/debug/my_app
```

### 常用命令1

```lldb
# 启动和控制
(lldb) run                      # 运行程序
(lldb) process launch           # 启动进程
(lldb) continue                 # 继续执行
(lldb) quit                     # 退出

# 断点
(lldb) breakpoint set --name main
(lldb) breakpoint set --file file.rs --line 42
(lldb) breakpoint list          # 列出断点
(lldb) breakpoint delete 1      # 删除断点

# 单步执行
(lldb) next                     # 单步（不进入）
(lldb) step                     # 单步（进入）
(lldb) finish                   # 执行到返回
(lldb) thread step-out          # 跳出当前函数

# 检查变量
(lldb) frame variable           # 显示所有变量
(lldb) print variable           # 打印变量
(lldb) p *pointer               # 解引用指针

# 调用栈
(lldb) thread backtrace         # 显示调用栈
(lldb) frame select 2           # 选择栈帧
(lldb) up                       # 向上移动
(lldb) down                     # 向下移动
```

### Rust 插件

LLDB 自动加载 Rust 格式化器：

```lldb
# 查看 Vec
(lldb) p my_vec
(Vec<i32, alloc::alloc::Global>) my_vec = vec![1, 2, 3, 4, 5]

# 查看 String
(lldb) p my_string
(alloc::string::String) my_string = "Hello, Rust!"

# 查看 Option
(lldb) p my_option
(core::option::Option<i32>) my_option = Some(42)
```

---

## IDE 集成调试

### VS Code 调试

**安装插件**：

- rust-analyzer
- CodeLLDB (或 C/C++)

**配置 `.vscode/launch.json`**：

```json
{
    "version": "0.2.0",
    "configurations": [
        {
            "type": "lldb",
            "request": "launch",
            "name": "Debug executable 'my_app'",
            "cargo": {
                "args": [
                    "build",
                    "--bin=my_app",
                    "--package=my_app"
                ],
                "filter": {
                    "name": "my_app",
                    "kind": "bin"
                }
            },
            "args": [],
            "cwd": "${workspaceFolder}"
        },
        {
            "type": "lldb",
            "request": "launch",
            "name": "Debug unit tests",
            "cargo": {
                "args": [
                    "test",
                    "--no-run",
                    "--lib",
                    "--package=my_app"
                ],
                "filter": {
                    "name": "my_app",
                    "kind": "lib"
                }
            },
            "args": [],
            "cwd": "${workspaceFolder}"
        }
    ]
}
```

**调试功能**：

1. **断点**：点击行号左侧设置
2. **条件断点**：右键断点设置条件
3. **观察变量**：在 Variables 面板查看
4. **调用栈**：在 Call Stack 面板查看
5. **调试控制台**：执行表达式
6. **数据可视化**：自动格式化 Rust 类型

### IntelliJ IDEA/CLion 调试

**配置**：

1. 安装 Rust 插件
2. 创建 Run Configuration
3. 选择 Binary 或 Test

**高级功能**：

- **智能断点**：方法断点、异常断点
- **求值器**：在调试时求值表达式
- **变量查看器**：树形显示复杂类型
- **内存视图**：查看内存布局

---

## 异步代码调试

### Tokio Console

Tokio 提供专门的异步任务调试工具：

```toml
[dependencies]
tokio = { version = "1", features = ["full", "tracing"] }
console-subscriber = "0.2"
```

```rust
#[tokio::main]
async fn main() {
    // 启动 console subscriber
    console_subscriber::init();
    
    // 你的异步代码
    tokio::spawn(async {
        loop {
            tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
            println!("Task running");
        }
    });
    
    tokio::time::sleep(tokio::time::Duration::from_secs(60)).await;
}
```

**运行 tokio-console**：

```bash
# 安装
cargo install tokio-console

# 启动应用
cargo run

# 在另一个终端启动 console
tokio-console
```

**查看信息**：

- 任务列表和状态
- 任务运行时间
- 等待时间分布
- 任务依赖关系
- 资源使用情况

### 异步调试技巧

**1. 使用 tracing**：

```rust
use tracing::{info, debug, instrument};

#[instrument]
async fn fetch_data(url: &str) -> Result<String, reqwest::Error> {
    debug!("Fetching from: {}", url);
    let response = reqwest::get(url).await?;
    let text = response.text().await?;
    info!("Fetched {} bytes", text.len());
    Ok(text)
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::DEBUG)
        .init();
    
    fetch_data("https://example.com").await.ok();
}
```

**2. 死锁检测**：

```rust
use tokio::time::{timeout, Duration};

async fn may_hang() {
    // 可能hang住的代码
}

#[tokio::main]
async fn main() {
    match timeout(Duration::from_secs(5), may_hang()).await {
        Ok(_) => println!("Completed"),
        Err(_) => eprintln!("Operation timed out!"),
    }
}
```

**3. 任务取消追踪**：

```rust
use tokio::select;
use tokio_util::sync::CancellationToken;

async fn worker(token: CancellationToken) {
    loop {
        select! {
            _ = token.cancelled() => {
                eprintln!("Task cancelled");
                break;
            }
            _ = do_work() => {
                println!("Work done");
            }
        }
    }
}
```

---

## 性能调试

### 火焰图

**生成火焰图**：

```bash
# 安装工具
cargo install flamegraph

# 生成火焰图
cargo flamegraph

# 指定二进制
cargo flamegraph --bin my_app

# 在浏览器中打开 flamegraph.svg
```

**手动生成**：

```bash
# 使用 perf
perf record --call-graph dwarf ./target/release/my_app
perf script | stackcollapse-perf.pl | flamegraph.pl > flamegraph.svg
```

### Perf 分析

```bash
# 记录性能数据
perf record -g ./target/release/my_app

# 查看报告
perf report

# CPU 缓存分析
perf stat -e cache-references,cache-misses ./target/release/my_app

# 分支预测
perf stat -e branch-misses ./target/release/my_app
```

### 内存分析

**使用 heaptrack**：

```bash
# 安装
# Ubuntu: apt-get install heaptrack
# macOS: brew install heaptrack

# 运行分析
heaptrack ./target/debug/my_app

# 查看结果
heaptrack_gui heaptrack.my_app.*.gz
```

**使用 massif (Valgrind)**：

```bash
# 运行内存分析
valgrind --tool=massif ./target/debug/my_app

# 查看结果
ms_print massif.out.*
```

---

## 并发调试

### 死锁检测

**使用 parking_lot**：

```rust
use parking_lot::deadlock;
use std::thread;
use std::time::Duration;

fn main() {
    // 创建死锁检测线程
    thread::spawn(move || {
        loop {
            thread::sleep(Duration::from_secs(1));
            let deadlocks = deadlock::check_deadlock();
            if deadlocks.is_empty() {
                continue;
            }
            
            eprintln!("{} deadlocks detected", deadlocks.len());
            for (i, threads) in deadlocks.iter().enumerate() {
                eprintln!("Deadlock #{}", i);
                for t in threads {
                    eprintln!("Thread Id {:#?}", t.thread_id());
                    eprintln!("{:#?}", t.backtrace());
                }
            }
        }
    });
    
    // 你的代码
}
```

### 数据竞争

**使用 ThreadSanitizer**：

```bash
# 设置环境变量
export RUSTFLAGS="-Z sanitizer=thread"

# 使用 nightly
cargo +nightly build --target x86_64-unknown-linux-gnu

# 运行
./target/x86_64-unknown-linux-gnu/debug/my_app
```

### 线程追踪

```rust
use std::thread;

fn main() {
    let handle = thread::Builder::new()
        .name("worker-1".to_string())
        .spawn(|| {
            println!("Thread: {:?}", thread::current().name());
            // 工作代码
        })
        .unwrap();
    
    handle.join().unwrap();
}
```

---

## 错误处理调试

### panic 分析

**获取详细回溯**：

```bash
# 启用 backtrace
RUST_BACKTRACE=1 cargo run

# 完整 backtrace
RUST_BACKTRACE=full cargo run
```

**自定义 panic 消息**：

```rust
fn main() {
    panic!("Something went wrong: {}", get_error_details());
}

fn get_error_details() -> String {
    format!("Error code: {}, timestamp: {}", 42, chrono::Utc::now())
}
```

### 错误传播追踪

```rust
use anyhow::{Context, Result};

fn read_config() -> Result<Config> {
    let content = std::fs::read_to_string("config.toml")
        .context("Failed to read config file")?;
    
    let config = toml::from_str(&content)
        .context("Failed to parse config")?;
    
    Ok(config)
}

fn main() {
    if let Err(e) = read_config() {
        eprintln!("Error: {:?}", e);
        // 打印完整错误链
        for cause in e.chain() {
            eprintln!("  caused by: {}", cause);
        }
    }
}
```

### 自定义 panic hook

```rust
use std::panic;

fn main() {
    panic::set_hook(Box::new(|panic_info| {
        eprintln!("=== PANIC OCCURRED ===");
        
        if let Some(location) = panic_info.location() {
            eprintln!("File: {}", location.file());
            eprintln!("Line: {}", location.line());
            eprintln!("Column: {}", location.column());
        }
        
        if let Some(msg) = panic_info.payload().downcast_ref::<&str>() {
            eprintln!("Message: {}", msg);
        }
        
        // 发送到监控系统
        // send_to_sentry(panic_info);
    }));
    
    // 你的代码
    panic!("Test panic");
}
```

---

## 内存调试

### Valgrind

```bash
# 内存错误检测
valgrind --leak-check=full \
         --show-leak-kinds=all \
         --track-origins=yes \
         --verbose \
         ./target/debug/my_app

# 缓存分析
valgrind --tool=cachegrind ./target/debug/my_app
cachegrind-annotate cachegrind.out.*
```

### AddressSanitizer

```bash
# 设置环境变量
export RUSTFLAGS="-Z sanitizer=address"

# 编译
cargo +nightly build --target x86_64-unknown-linux-gnu

# 运行
./target/x86_64-unknown-linux-gnu/debug/my_app
```

### 内存泄漏检测

**使用 `dhat`**：

```rust
use dhat::{Dhat, DhatAlloc};

#[global_allocator]
static ALLOCATOR: DhatAlloc = DhatAlloc;

fn main() {
    let _dhat = Dhat::start_heap_profiling();
    
    // 你的代码
    let v = vec![1, 2, 3, 4, 5];
    std::mem::forget(v);  // 故意泄漏
    
    // dhat 自动生成报告
}
```

---

## 调试最佳实践

### 调试策略

```text
1. 复现问题
   ├─ 最小化复现步骤
   ├─ 记录环境信息
   └─ 编写测试用例

2. 隔离问题
   ├─ 二分查找法
   ├─ 添加日志点
   └─ 使用断点

3. 分析原因
   ├─ 检查假设
   ├─ 阅读相关代码
   └─ 查看文档

4. 验证修复
   ├─ 修改代码
   ├─ 运行测试
   └─ 回归测试
```

### 可调试性设计

**1. 添加调试输出**：

```rust
#[derive(Debug)]
struct Request {
    id: u64,
    data: Vec<u8>,
}

impl Request {
    fn validate(&self) -> Result<(), String> {
        #[cfg(debug_assertions)]
        eprintln!("Validating request {:?}", self);
        
        if self.data.is_empty() {
            return Err("Empty data".to_string());
        }
        Ok(())
    }
}
```

**2. 使用 Display trait**：

```rust
use std::fmt;

struct Error {
    kind: ErrorKind,
    message: String,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}: {}", self.kind, self.message)
    }
}
```

**3. 添加上下文信息**：

```rust
use std::backtrace::Backtrace;

struct DetailedError {
    message: String,
    backtrace: Backtrace,
    timestamp: chrono::DateTime<chrono::Utc>,
}

impl DetailedError {
    fn new(message: String) -> Self {
        Self {
            message,
            backtrace: Backtrace::capture(),
            timestamp: chrono::Utc::now(),
        }
    }
}
```

### 日志规范

```rust
use log::{debug, info, warn, error};

// ✅ 好的日志实践
fn process_request(req: &Request) {
    info!("Processing request id={}", req.id);
    
    match validate_request(req) {
        Ok(_) => debug!("Request validation passed"),
        Err(e) => {
            warn!("Request validation failed: {}", e);
            return;
        }
    }
    
    // ... 处理逻辑
    
    info!("Request processed successfully, duration={}ms", duration.as_millis());
}

// ❌ 不好的日志实践
fn bad_logging(req: &Request) {
    println!("Processing");  // 使用 println! 而不是 log
    // ... 没有足够的上下文信息
    println!("Done");        // 没有时间戳、请求ID等
}
```

---

## 实战案例

### 案例1：死锁调试

**问题**：程序在运行一段时间后hang住。

```rust
use std::sync::{Arc, Mutex};
use std::thread;

// 问题代码
fn deadlock_example() {
    let lock_a = Arc::new(Mutex::new(0));
    let lock_b = Arc::new(Mutex::new(0));
    
    let lock_a_clone = Arc::clone(&lock_a);
    let lock_b_clone = Arc::clone(&lock_b);
    
    let handle1 = thread::spawn(move || {
        let _a = lock_a.lock().unwrap();
        thread::sleep(std::time::Duration::from_millis(10));
        let _b = lock_b.lock().unwrap();  // 可能死锁
    });
    
    let handle2 = thread::spawn(move || {
        let _b = lock_b_clone.lock().unwrap();
        thread::sleep(std::time::Duration::from_millis(10));
        let _a = lock_a_clone.lock().unwrap();  // 可能死锁
    });
    
    handle1.join().unwrap();
    handle2.join().unwrap();
}
```

**调试步骤**：

1. 使用 `parking_lot` 的死锁检测
2. 使用 GDB 查看所有线程状态
3. 分析锁获取顺序

**解决方案**：

```rust
// 解决方案：统一锁顺序
fn fixed_version() {
    let lock_a = Arc::new(Mutex::new(0));
    let lock_b = Arc::new(Mutex::new(0));
    
    // 总是先锁 A，再锁 B
    let handle1 = thread::spawn(move || {
        let _a = lock_a.lock().unwrap();
        let _b = lock_b.lock().unwrap();
    });
    
    let handle2 = thread::spawn(move || {
        let _a = lock_a.lock().unwrap();  // 相同顺序
        let _b = lock_b.lock().unwrap();
    });
}
```

### 案例2：内存泄漏排查

**问题**：程序运行时间越长，内存占用越高。

**调试步骤**：

```bash
# 1. 使用 heaptrack 分析
heaptrack ./target/debug/my_app

# 2. 查看火焰图
heaptrack_gui heaptrack.my_app.*.gz

# 3. 找到泄漏点
```

**常见原因**：

```rust
// 原因1：忘记释放资源
use std::sync::Arc;
use std::thread;

struct LeakyCache {
    data: Arc<Vec<u8>>,
}

impl LeakyCache {
    fn add_data(&mut self, data: Vec<u8>) {
        // 创建循环引用
        self.data = Arc::new(data);
    }
}

// 原因2：全局静态数据累积
use once_cell::sync::Lazy;
use std::collections::HashMap;
use std::sync::Mutex;

static GLOBAL_CACHE: Lazy<Mutex<HashMap<String, Vec<u8>>>> = 
    Lazy::new(|| Mutex::new(HashMap::new()));

fn cache_data(key: String, value: Vec<u8>) {
    // 数据一直累积，从不清理
    GLOBAL_CACHE.lock().unwrap().insert(key, value);
}
```

**解决方案**：

```rust
// 使用弱引用打破循环
use std::sync::{Arc, Weak};

// 定期清理缓存
use std::collections::HashMap;
use std::time::{Duration, Instant};

struct TimedCache {
    data: HashMap<String, (Vec<u8>, Instant)>,
    ttl: Duration,
}

impl TimedCache {
    fn cleanup(&mut self) {
        let now = Instant::now();
        self.data.retain(|_, (_, time)| now.duration_since(*time) < self.ttl);
    }
}
```

### 案例3：性能瓶颈分析

**问题**：API 响应时间过长。

**调试步骤**：

```bash
# 1. 生成火焰图
cargo flamegraph --bin api_server

# 2. 使用 tracing 添加时间测量
```

```rust
use tracing::{info, instrument};
use std::time::Instant;

#[instrument]
async fn handle_request(req: Request) -> Response {
    let start = Instant::now();
    
    let result = process_data(&req.data).await;
    info!("process_data took {:?}", start.elapsed());
    
    let formatted = format_response(result);
    info!("format_response took {:?}", start.elapsed());
    
    formatted
}
```

**发现问题**：

```rust
// 问题：N+1 查询
async fn get_users_with_posts() -> Vec<UserWithPosts> {
    let users = db.get_all_users().await;
    
    let mut result = Vec::new();
    for user in users {
        // 每个用户都单独查询！
        let posts = db.get_posts_for_user(user.id).await;
        result.push(UserWithPosts { user, posts });
    }
    result
}
```

**解决方案**：

```rust
// 使用批量查询
async fn get_users_with_posts_optimized() -> Vec<UserWithPosts> {
    let users = db.get_all_users().await;
    let user_ids: Vec<_> = users.iter().map(|u| u.id).collect();
    
    // 一次查询获取所有帖子
    let all_posts = db.get_posts_for_users(&user_ids).await;
    
    // 组装结果
    users.into_iter().map(|user| {
        let posts = all_posts.get(&user.id).cloned().unwrap_or_default();
        UserWithPosts { user, posts }
    }).collect()
}
```

---

## 总结

Rust 调试虽然有其独特性，但提供了丰富的工具和技术：

### 调试工具总结

| 工具类别 | 工具 | 适用场景 |
|---------|------|----------|
| **命令行** | println!/dbg!/log | 快速调试、日志记录 |
| **调试器** | GDB/LLDB | 断点调试、变量检查 |
| **IDE** | VS Code/CLion | 可视化调试 |
| **异步** | tokio-console | 异步任务追踪 |
| **性能** | flamegraph/perf | 性能分析 |
| **并发** | ThreadSanitizer | 数据竞争检测 |
| **内存** | Valgrind/ASan | 内存错误检测 |

### 调试建议

1. **预防胜于调试**：充分利用 Rust 的类型系统和借用检查器
2. **添加日志**：在关键路径添加日志点
3. **编写测试**：单元测试和集成测试是最好的调试工具
4. **使用工具**：熟练掌握各种调试工具
5. **保持简单**：复杂代码更难调试，保持代码简洁

### 持续学习

- 关注 Rust 调试工具的发展
- 学习调试技巧和最佳实践
- 参与社区讨论

---

## 相关资源

- [performance-optimization.md](./performance-optimization.md) - 性能优化
- [observability-deep-dive.md](./observability-deep-dive.md) - 可观测性
- [debugging-tools.md](./debugging-tools.md) - 调试工具生态
- [production-debugging.md](./production-debugging.md) - 生产环境调试

**外部资源**：

- [The Rust Programming Language - Testing](https://doc.rust-lang.org/book/ch11-00-testing.html)
- [Rust Debugging Guide](https://github.com/rust-lang/rust/blob/master/src/etc/gdb_rust_pretty_printer.py)
- [tokio-console Documentation](https://docs.rs/tokio-console/)
- [Flamegraph](https://github.com/flamegraph-rs/flamegraph)

---

**文档版本**: 1.0  
**最后更新**: 2025-10-20  
**维护者**: C13 Reliability Team
