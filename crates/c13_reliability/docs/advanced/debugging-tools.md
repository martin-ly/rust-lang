# Rust 调试工具生态

> **学习目标**：全面了解 Rust 调试工具生态，掌握各类工具的使用场景和最佳实践。

---

## 📖 目录

- [Rust 调试工具生态](#rust-调试工具生态)
  - [📖 目录](#-目录)
  - [工具概览](#工具概览)
    - [工具分类](#工具分类)
    - [选择指南](#选择指南)
  - [调试器](#调试器)
    - [GDB (GNU Debugger)](#gdb-gnu-debugger)
    - [LLDB](#lldb)
    - [WinDbg (Windows)](#windbg-windows)
  - [性能分析工具](#性能分析工具)
    - [Flamegraph](#flamegraph)
    - [Perf (Linux)](#perf-linux)
    - [Instruments (macOS)](#instruments-macos)
    - [Criterion](#criterion)
  - [内存分析工具](#内存分析工具)
    - [Valgrind](#valgrind)
    - [Sanitizers](#sanitizers)
    - [Heaptrack](#heaptrack)
    - [DHAT](#dhat)
  - [并发调试工具](#并发调试工具)
    - [ThreadSanitizer](#threadsanitizer)
    - [Loom](#loom)
    - [parking\_lot deadlock detection](#parking_lot-deadlock-detection)
  - [异步调试工具](#异步调试工具)
    - [tokio-console](#tokio-console)
    - [tracing](#tracing)
    - [async-backtrace](#async-backtrace)
  - [日志与追踪](#日志与追踪)
    - [log 生态](#log-生态)
    - [tracing 生态](#tracing-生态)
    - [slog](#slog)
  - [错误处理工具](#错误处理工具)
    - [anyhow](#anyhow)
    - [thiserror](#thiserror)
    - [eyre](#eyre)
    - [color-backtrace](#color-backtrace)
  - [测试工具](#测试工具)
    - [cargo test](#cargo-test)
    - [nextest](#nextest)
    - [proptest](#proptest)
    - [quickcheck](#quickcheck)
  - [IDE 与编辑器集成](#ide-与编辑器集成)
    - [Visual Studio Code](#visual-studio-code)
    - [IntelliJ IDEA / CLion](#intellij-idea--clion)
    - [Vim/Neovim](#vimneovim)
  - [Web 开发调试](#web-开发调试)
    - [actix-web debug](#actix-web-debug)
    - [axum tracing](#axum-tracing)
    - [reqwest debugging](#reqwest-debugging)
  - [数据库调试](#数据库调试)
    - [sqlx logging](#sqlx-logging)
    - [diesel debug](#diesel-debug)
  - [系统监控工具](#系统监控工具)
    - [htop/btop](#htopbtop)
    - [strace/ltrace](#straceltrace)
    - [BPF 工具](#bpf-工具)
  - [工具链整合](#工具链整合)
    - [CI/CD 集成](#cicd-集成)
    - [Docker 调试](#docker-调试)
    - [Kubernetes 调试](#kubernetes-调试)
  - [最佳实践](#最佳实践)
    - [工具组合](#工具组合)
    - [性能开销](#性能开销)
    - [团队协作](#团队协作)
  - [总结](#总结)
    - [核心工具集](#核心工具集)
    - [选择建议](#选择建议)
  - [相关资源](#相关资源)

---

## 工具概览

### 工具分类

```text
Rust 调试工具生态
├─ 调试器
│  ├─ GDB/LLDB (通用调试器)
│  ├─ WinDbg (Windows)
│  └─ IDE 集成调试器
├─ 性能分析
│  ├─ flamegraph (CPU profiling)
│  ├─ perf/Instruments (系统级)
│  └─ criterion (基准测试)
├─ 内存分析
│  ├─ Valgrind (内存错误)
│  ├─ ASan/MSan (Sanitizers)
│  └─ heaptrack/dhat (堆分析)
├─ 并发调试
│  ├─ ThreadSanitizer (数据竞争)
│  ├─ loom (模型检查)
│  └─ deadlock detection
├─ 异步调试
│  ├─ tokio-console (任务监控)
│  ├─ tracing (分布式追踪)
│  └─ async-backtrace
├─ 日志/追踪
│  ├─ log ecosystem
│  ├─ tracing ecosystem
│  └─ slog
├─ 错误处理
│  ├─ anyhow/thiserror
│  ├─ eyre
│  └─ color-backtrace
└─ 测试工具
   ├─ cargo test/nextest
   ├─ proptest/quickcheck
   └─ criterion
```

### 选择指南

| 问题类型 | 推荐工具 | 使用场景 |
|---------|---------|----------|
| **逻辑错误** | GDB/LLDB, println!/dbg! | 断点调试、变量检查 |
| **性能问题** | flamegraph, perf, criterion | CPU热点、性能基准 |
| **内存泄漏** | Valgrind, heaptrack, ASan | 内存分配追踪 |
| **数据竞争** | ThreadSanitizer, loom | 并发bug |
| **死锁** | parking_lot detection | 多线程死锁 |
| **异步问题** | tokio-console, tracing | 任务hang、调度问题 |
| **生产问题** | tracing, logs, metrics | 分布式追踪、监控 |

---

## 调试器

### GDB (GNU Debugger)

**安装**：

```bash
# Linux
sudo apt-get install gdb

# macOS
brew install gdb

# Rust wrapper
rustup component add rust-gdb
```

**特点**：

- ✅ 功能强大，历史悠久
- ✅ 广泛支持，文档丰富
- ✅ Rust pretty-printer 支持
- ❌ 在 macOS 上配置复杂

**使用示例**：

```bash
# 启动调试
rust-gdb target/debug/my_app

# 常用命令
(gdb) break main
(gdb) run
(gdb) next
(gdb) print my_variable
(gdb) backtrace
```

### LLDB

**安装**：

```bash
# macOS (自带)
# Linux
sudo apt-get install lldb

# Rust wrapper
rustup component add rust-lldb
```

**特点**：

- ✅ macOS 默认调试器
- ✅ 现代化设计
- ✅ Rust 格式化器自动加载
- ✅ 更好的 C++/Rust 支持

**使用示例**：

```bash
# 启动调试
rust-lldb target/debug/my_app

# 常用命令
(lldb) breakpoint set --name main
(lldb) run
(lldb) thread step-over
(lldb) frame variable
(lldb) bt
```

### WinDbg (Windows)

**安装**：

```bash
# Windows Store
# 或下载 WinDbg Preview

# 生成 PDB 文件
cargo build --features pdb
```

**特点**：

- ✅ Windows 原生支持
- ✅ 内核调试能力
- ✅ 强大的脚本功能
- ❌ 学习曲线陡峭

---

## 性能分析工具

### Flamegraph

**安装与使用**：

```bash
# 安装
cargo install flamegraph

# 生成火焰图
cargo flamegraph

# 自定义选项
cargo flamegraph --bin my_app -- arg1 arg2

# 输出 SVG
# 生成 flamegraph.svg，在浏览器中打开
```

**特点**：

- ✅ 可视化 CPU 热点
- ✅ 易于识别性能瓶颈
- ✅ 支持多平台
- ✅ 交互式浏览

**最佳实践**：

```bash
# Release 模式 + 调试符号
cargo flamegraph --profile release-with-debug

# 指定采样率
perf record -F 999 -g ./my_app
```

### Perf (Linux)

**安装**：

```bash
# Ubuntu
sudo apt-get install linux-tools-common linux-tools-generic

# 允许用户使用 perf
echo -1 | sudo tee /proc/sys/kernel/perf_event_paranoid
```

**使用**：

```bash
# CPU profiling
perf record -g ./target/release/my_app
perf report

# 统计信息
perf stat ./target/release/my_app

# 缓存分析
perf stat -e cache-references,cache-misses ./target/release/my_app

# 实时监控
perf top
```

**高级功能**：

```bash
# 火焰图
perf script | stackcollapse-perf.pl | flamegraph.pl > perf.svg

# CPU 缓存
perf c2c record ./my_app
perf c2c report
```

### Instruments (macOS)

**使用**：

```bash
# 启动 Instruments
instruments

# 命令行
instruments -t "Time Profiler" -D trace.trace ./target/release/my_app
```

**特点**：

- ✅ macOS 原生工具
- ✅ 图形界面优秀
- ✅ 多种分析模板
- ✅ 时间序列分析

### Criterion

**添加依赖**：

```toml
[dev-dependencies]
criterion = { version = "0.5", features = ["html_reports"] }

[[bench]]
name = "my_benchmark"
harness = false
```

**编写基准测试**：

```rust
use criterion::{black_box, criterion_group, criterion_main, Criterion};

fn fibonacci(n: u64) -> u64 {
    match n {
        0 => 1,
        1 => 1,
        n => fibonacci(n-1) + fibonacci(n-2),
    }
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("fib 20", |b| b.iter(|| fibonacci(black_box(20))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
```

**运行**：

```bash
cargo bench

# 查看报告
open target/criterion/report/index.html
```

---

## 内存分析工具

### Valgrind

**安装**：

```bash
# Linux
sudo apt-get install valgrind

# macOS
brew install valgrind
```

**使用**：

```bash
# 内存错误检测
valgrind --leak-check=full \
         --show-leak-kinds=all \
         --track-origins=yes \
         ./target/debug/my_app

# 缓存分析
valgrind --tool=cachegrind ./target/debug/my_app

# 堆分析
valgrind --tool=massif ./target/debug/my_app
ms_print massif.out.*
```

**特点**：

- ✅ 功能全面
- ✅ 检测内存错误
- ✅ 缓存性能分析
- ❌ 运行速度慢（10-50x）

### Sanitizers

**AddressSanitizer (ASan)**：

```bash
# 设置环境变量
export RUSTFLAGS="-Z sanitizer=address"

# 编译
cargo +nightly build --target x86_64-unknown-linux-gnu

# 运行
./target/x86_64-unknown-linux-gnu/debug/my_app
```

**MemorySanitizer (MSan)**：

```bash
export RUSTFLAGS="-Z sanitizer=memory"
cargo +nightly build --target x86_64-unknown-linux-gnu
```

**LeakSanitizer (LSan)**：

```bash
export RUSTFLAGS="-Z sanitizer=leak"
cargo +nightly build
```

**特点**：

- ✅ 快速（2-3x 开销）
- ✅ 编译时插桩
- ✅ 精确错误定位
- ❌ 需要 nightly Rust

### Heaptrack

**安装与使用**：

```bash
# 安装
sudo apt-get install heaptrack

# 运行分析
heaptrack ./target/debug/my_app

# 查看结果
heaptrack_gui heaptrack.my_app.*.gz
```

**特点**：

- ✅ 可视化堆分析
- ✅ 时间线视图
- ✅ 低开销
- ✅ 易于使用

### DHAT

**使用**：

```toml
[dependencies]
dhat = "0.3"
```

```rust
use dhat::{Dhat, DhatAlloc};

#[global_allocator]
static ALLOCATOR: DhatAlloc = DhatAlloc;

fn main() {
    let _dhat = Dhat::start_heap_profiling();
    
    // 你的代码
    
    // 自动生成 dhat-heap.json
}
```

**查看报告**：

```bash
# 使用 dh_view.html (包含在 dhat 中)
firefox target/dhat-heap.json
```

---

## 并发调试工具

### ThreadSanitizer

**使用**：

```bash
export RUSTFLAGS="-Z sanitizer=thread"
cargo +nightly build --target x86_64-unknown-linux-gnu

# 运行
./target/x86_64-unknown-linux-gnu/debug/my_app
```

**检测内容**：

- 数据竞争
- 死锁
- 不正确的同步

**示例输出**：

```text
==================
WARNING: ThreadSanitizer: data race (pid=12345)
  Write of size 4 at 0x7b0400000000 by thread T1:
    #0 my_crate::function src/lib.rs:42
```

### Loom

**添加依赖**：

```toml
[dev-dependencies]
loom = "0.7"
```

**编写测试**：

```rust
#[cfg(loom)]
use loom::{thread, sync::Arc, sync::atomic::{AtomicUsize, Ordering}};

#[test]
#[cfg(loom)]
fn test_concurrent_increment() {
    loom::model(|| {
        let counter = Arc::new(AtomicUsize::new(0));
        
        let handles: Vec<_> = (0..2)
            .map(|_| {
                let counter = Arc::clone(&counter);
                thread::spawn(move || {
                    counter.fetch_add(1, Ordering::SeqCst);
                })
            })
            .collect();
        
        for handle in handles {
            handle.join().unwrap();
        }
        
        assert_eq!(counter.load(Ordering::SeqCst), 2);
    });
}
```

**特点**：

- ✅ 模型检查（穷尽测试）
- ✅ 检测微妙的并发bug
- ✅ 可重现问题
- ❌ 只适用于小规模并发

### parking_lot deadlock detection

**使用**：

```toml
[dependencies]
parking_lot = "0.12"
```

```rust
use parking_lot::deadlock;
use std::thread;
use std::time::Duration;

fn main() {
    // 启动死锁检测线程
    thread::spawn(move || {
        loop {
            thread::sleep(Duration::from_secs(1));
            let deadlocks = deadlock::check_deadlock();
            if deadlocks.is_empty() {
                continue;
            }

            println!("{} deadlocks detected", deadlocks.len());
            for (i, threads) in deadlocks.iter().enumerate() {
                println!("Deadlock #{}", i);
                for t in threads {
                    println!("Thread Id {:#?}", t.thread_id());
                    println!("{:#?}", t.backtrace());
                }
            }
        }
    });
    
    // 你的代码
}
```

---

## 异步调试工具

### tokio-console

**添加依赖**：

```toml
[dependencies]
tokio = { version = "1", features = ["full", "tracing"] }
console-subscriber = "0.2"
```

**启用**：

```rust
#[tokio::main]
async fn main() {
    console_subscriber::init();
    
    // 异步代码
}
```

**使用**：

```bash
# 安装
cargo install tokio-console

# 启动应用
cargo run

# 在另一个终端
tokio-console
```

**功能**：

- 任务列表和状态
- 运行时间统计
- 等待时间分布
- 资源使用情况
- 异步调用图

### tracing

**添加依赖**：

```toml
[dependencies]
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter"] }
```

**使用**：

```rust
use tracing::{info, debug, warn, error, instrument};

#[instrument]
async fn fetch_data(url: &str) -> Result<Data, Error> {
    debug!("Fetching from: {}", url);
    
    let response = reqwest::get(url).await?;
    info!("Got response: status={}", response.status());
    
    let data = response.json().await?;
    Ok(data)
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt()
        .with_max_level(tracing::Level::DEBUG)
        .with_target(false)
        .init();
    
    fetch_data("https://api.example.com").await.ok();
}
```

### async-backtrace

**添加依赖**：

```toml
[dependencies]
async-backtrace = "0.2"
```

**使用**：

```rust
use async_backtrace::frame;

#[frame]
async fn inner() {
    tokio::time::sleep(tokio::time::Duration::from_secs(1)).await;
}

#[tokio::main]
async fn main() {
    // 在另一个任务中打印 backtrace
    tokio::spawn(async {
        loop {
            tokio::time::sleep(tokio::time::Duration::from_secs(5)).await;
            async_backtrace::taskdump_tree(true);
        }
    });
    
    inner().await;
}
```

---

## 日志与追踪

### log 生态

**核心 crate**：

- `log` - 日志门面
- `env_logger` - 简单日志实现
- `fern` - 灵活配置
- `log4rs` - 类似 log4j

**示例**：

```rust
use log::{info, debug, error};

fn main() {
    env_logger::Builder::from_env(
        env_logger::Env::default().default_filter_or("info")
    ).init();
    
    info!("Application started");
    debug!("Debug information");
    error!("An error occurred");
}
```

### tracing 生态

**核心 crate**：

- `tracing` - 结构化日志
- `tracing-subscriber` - 订阅者实现
- `tracing-appender` - 文件输出
- `tracing-opentelemetry` - OpenTelemetry 集成

**高级示例**：

```rust
use tracing::{info_span, instrument};
use tracing_subscriber::layer::SubscriberExt;

#[instrument]
async fn process_request(id: u64) {
    let span = info_span!("database_query", request_id = id);
    let _enter = span.enter();
    
    // 数据库操作
}

fn main() {
    let subscriber = tracing_subscriber::registry()
        .with(tracing_subscriber::fmt::layer())
        .with(tracing_subscriber::filter::LevelFilter::INFO);
    
    tracing::subscriber::set_global_default(subscriber).unwrap();
}
```

### slog

**特点**：

- 结构化日志
- 高性能
- 可组合

```rust
use slog::{Drain, Logger, o, info};

fn main() {
    let drain = slog_term::term_full().fuse();
    let drain = slog_async::Async::new(drain).build().fuse();
    let log = Logger::root(drain, o!());
    
    info!(log, "Application started"; "version" => "1.0.0");
}
```

---

## 错误处理工具

### anyhow

```rust
use anyhow::{Context, Result};

fn read_config() -> Result<Config> {
    let content = std::fs::read_to_string("config.toml")
        .context("Failed to read config")?;
    
    let config: Config = toml::from_str(&content)
        .context("Failed to parse config")?;
    
    Ok(config)
}
```

### thiserror

```rust
use thiserror::Error;

#[derive(Error, Debug)]
pub enum MyError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("Parse error: {0}")]
    Parse(String),
    
    #[error("Not found: {id}")]
    NotFound { id: u64 },
}
```

### eyre

```rust
use color_eyre::eyre::{Result, WrapErr};

fn main() -> Result<()> {
    color_eyre::install()?;
    
    let config = read_config()
        .wrap_err("Failed to load application config")?;
    
    Ok(())
}
```

### color-backtrace

```rust
fn main() {
    color_backtrace::install();
    
    // 你的代码
}
```

---

## 测试工具

### cargo test

```bash
# 运行所有测试
cargo test

# 运行特定测试
cargo test test_name

# 显示输出
cargo test -- --nocapture

# 并行度
cargo test -- --test-threads=1
```

### nextest

```bash
# 安装
cargo install cargo-nextest

# 运行测试
cargo nextest run

# 更快的测试执行
# 更好的输出格式
# JUnit 报告
cargo nextest run --profile ci
```

### proptest

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn test_sort(ref mut v in prop::collection::vec(any::<i32>(), 0..100)) {
        v.sort();
        
        for i in 1..v.len() {
            assert!(v[i-1] <= v[i]);
        }
    }
}
```

### quickcheck

```rust
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[quickcheck]
fn reverse_reverse_is_identity(xs: Vec<i32>) -> bool {
    let mut ys = xs.clone();
    ys.reverse();
    ys.reverse();
    xs == ys
}
```

---

## IDE 与编辑器集成

### Visual Studio Code

**必装插件**：

- `rust-analyzer` - LSP 服务器
- `CodeLLDB` - LLDB 调试器
- `crates` - 依赖管理
- `Error Lens` - 内联错误显示

**调试配置**: 见 [rust-debugging.md](./rust-debugging.md)

### IntelliJ IDEA / CLion

**特点**：

- 强大的重构支持
- 内置调试器
- 数据库工具
- 性能分析

### Vim/Neovim

**插件**：

- `rust.vim` - 语法高亮
- `coc-rust-analyzer` - LSP 客户端
- `vim-test` - 测试运行
- `termdebug` - GDB 集成

---

## Web 开发调试

### actix-web debug

```rust
use actix_web::{middleware::Logger, App, HttpServer};

#[actix_web::main]
async fn main() {
    env_logger::init_from_env(env_logger::Env::default().default_filter_or("info"));
    
    HttpServer::new(|| {
        App::new()
            .wrap(Logger::default())
            .wrap(Logger::new("%a %{User-Agent}i"))
    })
    .bind("127.0.0.1:8080")?
    .run()
    .await
}
```

### axum tracing

```rust
use axum::{Router, middleware};
use tower_http::trace::TraceLayer;

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();
    
    let app = Router::new()
        .layer(TraceLayer::new_for_http());
    
    axum::Server::bind(&"0.0.0.0:3000".parse().unwrap())
        .serve(app.into_make_service())
        .await
        .unwrap();
}
```

### reqwest debugging

```rust
let client = reqwest::Client::builder()
    .connection_verbose(true)  // 详细输出
    .build()?;
```

---

## 数据库调试

### sqlx logging

```rust
use sqlx::postgres::PgPoolOptions;
use tracing_subscriber;

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();
    
    let pool = PgPoolOptions::new()
        .max_connections(5)
        .connect("postgres://user:pass@localhost/db")
        .await?;
    
    // SQL 查询会自动记录日志
}
```

### diesel debug

```rust
use diesel::debug_query;

let query = users.filter(id.eq(1));
println!("{}", debug_query::<Pg, _>(&query));
```

---

## 系统监控工具

### htop/btop

```bash
# 安装
sudo apt-get install htop
# 或
cargo install bottom  # btm
```

### strace/ltrace

```bash
# 系统调用追踪
strace ./target/debug/my_app

# 库函数追踪
ltrace ./target/debug/my_app

# 过滤特定调用
strace -e open,read ./target/debug/my_app
```

### BPF 工具

```bash
# bpftrace
sudo bpftrace -e 'tracepoint:syscalls:sys_enter_read { @[comm] = count(); }'

# bcc tools
sudo opensnoop  # 监控文件打开
sudo tcptracer  # 追踪 TCP 连接
```

---

## 工具链整合

### CI/CD 集成

```yaml
# .github/workflows/debug.yml
name: Debug Build

on: [push, pull_request]

jobs:
  debug:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      
      - name: Install Rust
        uses: actions-rs/toolchain@v1
        with:
          toolchain: stable
          
      - name: Run tests with backtrace
        run: RUST_BACKTRACE=1 cargo test
        
      - name: Run with sanitizer
        run: |
          rustup toolchain install nightly
          RUSTFLAGS="-Z sanitizer=address" cargo +nightly build
```

### Docker 调试

```dockerfile
FROM rust:1.90 as builder

# 包含调试符号
RUN cargo build

# 调试镜像
FROM ubuntu:22.04
COPY --from=builder /app/target/debug/my_app /usr/local/bin/
RUN apt-get update && apt-get install -y gdb

CMD ["gdb", "/usr/local/bin/my_app"]
```

### Kubernetes 调试

```bash
# 进入 Pod
kubectl exec -it pod-name -- bash

# 查看日志
kubectl logs -f pod-name

# Port forward
kubectl port-forward pod-name 8080:8080

# 调试容器
kubectl debug pod-name -it --image=ubuntu --target=container-name
```

---

## 最佳实践

### 工具组合

**开发阶段**：

- IDE 调试器 + println!/dbg!
- cargo test
- clippy + rustfmt

**性能调优**：

- flamegraph
- criterion
- perf

**内存问题**：

- Valgrind
- ASan
- heaptrack

**并发问题**：

- ThreadSanitizer
- loom
- deadlock detection

**生产环境**：

- tracing + OpenTelemetry
- Prometheus + Grafana
- Sentry/error tracking

### 性能开销

| 工具 | 开销 | 使用场景 |
|------|------|----------|
| println! | 低 | 开发调试 |
| tracing | 低-中 | 生产日志 |
| GDB/LLDB | 中 | 开发调试 |
| ASan | 2-3x | 开发/CI |
| TSan | 5-10x | 开发/CI |
| Valgrind | 10-50x | 深度分析 |
| loom | 很高 | 小规模测试 |

### 团队协作

1. **统一工具链**：团队使用相同的调试工具
2. **文档化**：记录调试步骤和技巧
3. **自动化**：CI/CD 集成调试检查
4. **分享经验**：定期分享调试案例

---

## 总结

Rust 拥有丰富的调试工具生态：

### 核心工具集

**必备**：

- GDB/LLDB
- tracing
- cargo test
- flamegraph

**推荐**：

- tokio-console (异步)
- ASan (内存)
- criterion (性能)
- nextest (测试)

**高级**：

- loom (并发模型检查)
- Valgrind (深度内存分析)
- perf (系统级分析)

### 选择建议

1. **从简单开始**：println!/dbg! → GDB → 专用工具
2. **按需选择**：根据问题类型选择工具
3. **组合使用**：多种工具配合效果更好
4. **持续学习**：跟踪工具发展

---

## 相关资源

- [rust-debugging.md](./rust-debugging.md) - Rust 调试完整指南
- [production-debugging.md](./production-debugging.md) - 生产环境调试
- [Rust Performance Book](https://nnethercote.github.io/perf-book/)
- [Are We Observable Yet?](https://www.areweasyncyet.rs/)

---

**文档版本**: 1.0  
**最后更新**: 2025-10-20  
**维护者**: C13 Reliability Team
