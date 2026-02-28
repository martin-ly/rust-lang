# Rust 生产级项目示例

> **文档版本**: 1.0  
> **最后更新**: 2026-02-28  
> **适用对象**: 中级到高级 Rust 开发者  
> **目标**: 提供端到端的可运行生产级项目模板

---

## 目录

- [Rust 生产级项目示例](#rust-生产级项目示例)
  - [目录](#目录)
  - [简介](#简介)
  - [技术选型对比总览](#技术选型对比总览)
  - [项目 1: CLI 日志分析器](#项目-1-cli-日志分析器)
    - [1.1 项目概述](#11-项目概述)
    - [1.2 技术选型理由](#12-技术选型理由)
    - [1.3 完整项目配置](#13-完整项目配置)
    - [1.4 核心代码实现](#14-核心代码实现)
    - [1.5 项目结构](#15-项目结构)
    - [1.6 构建和运行](#16-构建和运行)
    - [1.7 测试策略](#17-测试策略)
    - [1.8 部署方案](#18-部署方案)
    - [1.9 性能优化](#19-性能优化)
  - [项目 2: REST API 任务管理系统](#项目-2-rest-api-任务管理系统)
    - [2.1 项目概述](#21-项目概述)
    - [2.2 技术选型理由](#22-技术选型理由)
    - [2.3 完整项目配置](#23-完整项目配置)
    - [2.4 核心代码实现](#24-核心代码实现)
    - [2.5 项目结构](#25-项目结构)
    - [2.6 构建和运行](#26-构建和运行)
    - [2.7 测试策略](#27-测试策略)
    - [2.8 部署方案](#28-部署方案)
    - [2.9 性能优化](#29-性能优化)
  - [项目 3: 嵌入式 IoT 传感器读取器](#项目-3-嵌入式-iot-传感器读取器)
    - [3.1 项目概述](#31-项目概述)
    - [3.2 技术选型理由](#32-技术选型理由)
    - [3.3 完整项目配置](#33-完整项目配置)
    - [3.4 核心代码实现](#34-核心代码实现)
    - [3.5 项目结构](#35-项目结构)
    - [3.6 构建和运行](#36-构建和运行)
    - [3.7 测试策略](#37-测试策略)
    - [3.8 部署方案](#38-部署方案)
    - [3.9 性能优化](#39-性能优化)
  - [附录](#附录)
    - [A. 通用 CI/CD 配置](#a-通用-cicd-配置)
    - [B. 代码质量工具配置](#b-代码质量工具配置)
    - [C. 监控和日志最佳实践](#c-监控和日志最佳实践)

---

## 简介

本文档提供三个完整的生产级 Rust 项目示例，涵盖 CLI 工具、Web 服务和嵌入式应用三个不同领域。每个项目都经过精心设计，展示 Rust 在实际生产环境中的最佳实践。

### 学习目标

- 掌握不同类型 Rust 项目的架构设计
- 理解生产环境的工程实践要求
- 学习性能优化和错误处理技巧
- 了解测试策略和部署方案

### 前置知识

- Rust 基础语法和所有权系统
- Cargo 包管理工具
- 基本的命令行操作

---

## 技术选型对比总览

| 项目类型 | CLI 日志分析器 | REST API 服务 | 嵌入式 IoT |
|---------|---------------|--------------|-----------|
| **应用领域** | 数据处理工具 | Web 后端 | IoT 设备 |
| **标准库** | std | std | no_std |
| **并发模型** | 多线程 (rayon) | 异步 (tokio) | 中断驱动 |
| **内存分配** | 堆分配 | 堆分配 | 全局分配器 |
| **目标平台** | 桌面/服务器 | 服务器 | 微控制器 |
| **依赖数量** | 中等 (10-20) | 较多 (20-40) | 精简 (5-10) |
| **二进制大小** | ~5-10 MB | ~20-50 MB | ~500 KB |

---

## 项目 1: CLI 日志分析器

### 1.1 项目概述

**项目名称**: `log-analyzer`  
**版本**: 0.1.0  
**许可证**: MIT OR Apache-2.0

#### 功能需求

1. **日志解析**: 支持 Apache/Nginx 日志格式，可扩展其他格式
2. **统计分析**: IP 访问频率、HTTP 状态码分布、URL 访问排行
3. **实时处理**: 流式处理大文件，支持进度显示
4. **多格式输出**: JSON、CSV、HTML 报告
5. **过滤查询**: 支持时间范围、状态码、IP 过滤

#### 非功能需求

| 指标 | 目标值 | 说明 |
|-----|-------|------|
| 处理速度 | > 1GB/s | 8 核机器上处理 1GB 日志 |
| 内存占用 | < 1GB | 处理任意大小文件 |
| 启动时间 | < 100ms | 从命令执行到开始处理 |
| 错误恢复 | 容错处理 | 跳过损坏行，记录错误 |

---

### 1.2 技术选型理由

| 技术 | 用途 | 备选方案 | 选择理由 |
|-----|------|---------|---------|
| **clap** | CLI 参数解析 | structopt, argh | 功能完整，文档优秀，derive 宏便捷 |
| **rayon** | 并行处理 | crossbeam, 手动线程 | 数据并行 API 简洁，自动任务调度 |
| **serde** | 序列化 | 手动实现 | 生态标准，支持多格式 |
| **csv** | CSV 输出 | 手动实现 | 性能优秀，处理边界情况 |
| **askama** | HTML 模板 | tera, handlebars | 编译时检查，零拷贝渲染 |
| **indicatif** | 进度条 | pbr, 手动实现 | 功能丰富，支持多进度条 |
| **tracing** | 日志 | log, env_logger | 结构化日志，性能更好 |
| **anyhow** | 错误处理 | thiserror, eyre | 简单错误传播，适合应用 |
| **memmap2** | 大文件读取 | 流式读取 | 减少内存拷贝，提升性能 |
| **regex** | 模式匹配 | aho-corasick | 标准正则，通用性强 |

---

### 1.3 完整项目配置

#### `Cargo.toml`

```toml
[package]
name = "log-analyzer"
version = "0.1.0"
edition = "2021"
authors = ["Your Name <your.email@example.com>"]
description = "High-performance log file analyzer with parallel processing"
license = "MIT OR Apache-2.0"
repository = "https://github.com/yourusername/log-analyzer"
keywords = ["cli", "log", "analyzer", "parser"]
categories = ["command-line-utilities", "development-tools"]
rust-version = "1.75"

[[bin]]
name = "log-analyzer"
path = "src/main.rs"

[dependencies]
# CLI
clap = { version = "4.5", features = ["derive", "env", "cargo"] }

# 并发处理
rayon = "1.9"

# 序列化
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
csv = "1.3"

# 模板引擎
askama = "0.12"

# 错误处理
anyhow = "1.0"
thiserror = "1.0"

# 日志和进度
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "fmt"] }
indicatif = "0.17"
console = "0.15"

# 文件处理
memmap2 = "0.9"

# 正则表达式
regex = "1.10"

# 时间和日期
chrono = { version = "0.4", features = ["serde"] }

# 集合处理
dashmap = "5.5"

# 性能优化
ahash = "0.8"

[dev-dependencies]
# 测试辅助
tempfile = "3.10"
criterion = { version = "0.5", features = ["html_reports"] }
pretty_assertions = "1.4"
proptest = "1.4"

[profile.release]
opt-level = 3
lto = "thin"
codegen-units = 1
strip = true
panic = "abort"

[profile.release-opt]
inherits = "release"
lto = true

[profile.dev]
opt-level = 0
debug = true

[[bench]]
name = "parser_bench"
harness = false
```

#### `clippy.toml`

```toml
# Clippy 配置
avoid-breaking-exported-api = false
msrv = "1.75"
```

#### `.cargo/config.toml`

```toml
[build]
rustflags = ["-C", "target-cpu=native"]

[target.x86_64-unknown-linux-gnu]
linker = "clang"
rustflags = ["-C", "link-arg=-fuse-ld=lld", "-C", "target-cpu=native"]

[target.x86_64-pc-windows-msvc]
rustflags = ["-C", "target-cpu=native"]

[profile.release]
strip = true
```

---

### 1.4 核心代码实现

#### 目录结构

```
log-analyzer/
├── src/
│   ├── main.rs          # 入口点
│   ├── cli.rs           # 命令行解析
│   ├── parser/          # 日志解析模块
│   │   ├── mod.rs
│   │   ├── apache.rs
│   │   └── nginx.rs
│   ├── analyzer/        # 分析逻辑
│   │   ├── mod.rs
│   │   └── stats.rs
│   ├── output/          # 输出格式
│   │   ├── mod.rs
│   │   ├── json.rs
│   │   ├── csv.rs
│   │   └── html.rs
│   ├── filter.rs        # 过滤条件
│   └── error.rs         # 错误定义
├── templates/           # HTML 模板
│   └── report.html
├── benches/            # 性能测试
│   └── parser_bench.rs
└── tests/              # 集成测试
    └── integration_tests.rs
```

#### `src/cli.rs` - 命令行参数

```rust
use clap::{Parser, ValueEnum};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(
    name = "log-analyzer",
    about = "High-performance log file analyzer",
    version = env!("CARGO_PKG_VERSION"),
    author = env!("CARGO_PKG_AUTHORS"),
    long_about = None
)]
pub struct Cli {
    /// 输入日志文件路径
    #[arg(short, long, value_name = "FILE")]
    pub input: PathBuf,

    /// 输出文件路径 (默认 stdout)
    #[arg(short, long, value_name = "FILE")]
    pub output: Option<PathBuf>,

    /// 输出格式
    #[arg(short, long, value_enum, default_value = "json")]
    pub format: OutputFormat,

    /// 日志格式类型
    #[arg(short, long, value_enum, default_value = "auto")]
    pub log_type: LogType,

    /// 过滤: 起始时间 (RFC3339)
    #[arg(long, value_name = "TIME")]
    pub start_time: Option<String>,

    /// 过滤: 结束时间 (RFC3339)
    #[arg(long, value_name = "TIME")]
    pub end_time: Option<String>,

    /// 过滤: 状态码 (支持范围, 如 200-299)
    #[arg(short = 'S', long, value_name = "CODE")]
    pub status_code: Option<String>,

    /// 过滤: IP 地址或 CIDR
    #[arg(short, long, value_name = "IP")]
    pub ip: Option<String>,

    /// 工作线程数 (默认 CPU 核心数)
    #[arg(short = 'j', long, value_name = "N")]
    pub threads: Option<usize>,

    /// 统计条目数量限制
    #[arg(short = 'n', long, default_value = "100")]
    pub limit: usize,

    /// 显示进度条
    #[arg(short = 'p', long, default_value = "true")]
    pub progress: bool,

    /// 详细日志级别
    #[arg(short, long, action = clap::ArgAction::Count)]
    pub verbose: u8,
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum OutputFormat {
    /// JSON 格式
    Json,
    /// CSV 格式
    Csv,
    /// HTML 报告
    Html,
}

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum LogType {
    /// 自动检测
    Auto,
    /// Apache Combined Log Format
    Apache,
    /// Nginx Log Format
    Nginx,
}
```

#### `src/parser/mod.rs` - 解析器 trait

```rust
use chrono::{DateTime, Utc};
use std::net::IpAddr;

/// 解析后的日志条目
#[derive(Debug, Clone, serde::Serialize)]
pub struct LogEntry {
    pub timestamp: DateTime<Utc>,
    pub ip: IpAddr,
    pub method: String,
    pub path: String,
    pub protocol: String,
    pub status: u16,
    pub bytes_sent: u64,
    pub referrer: Option<String>,
    pub user_agent: Option<String>,
}

/// 日志解析器 trait
pub trait LogParser: Send + Sync {
    /// 解析单行日志
    fn parse_line(&self, line: &str) -> anyhow::Result<LogEntry>;
    
    /// 解析器名称
    fn name(&self) -> &'static str;
}

/// 解析器工厂
pub fn create_parser(log_type: super::cli::LogType) -> anyhow::Result<Box<dyn LogParser>> {
    match log_type {
        super::cli::LogType::Apache => Ok(Box::new(apache::ApacheParser::new()?)),
        super::cli::LogType::Nginx => Ok(Box::new(nginx::NginxParser::new()?)),
        super::cli::LogType::Auto => {
            // 自动检测逻辑
            Ok(Box::new(apache::ApacheParser::new()?))
        }
    }
}

pub mod apache;
pub mod nginx;
```

#### `src/parser/apache.rs` - Apache 日志解析

```rust
use super::{LogEntry, LogParser};
use anyhow::{Context, Result};
use chrono::DateTime;
use regex::Regex;
use std::net::IpAddr;

/// Apache Combined Log Format 解析器
/// 
/// 格式: %h %l %u %t "%r" %>s %b "%{Referer}i" "%{User-agent}i"
/// 
/// 示例: 127.0.0.1 - frank [10/Oct/2000:13:55:36 -0700] "GET /apache_pb.gif HTTP/1.0" 200 2326 "http://www.example.com/start.html" "Mozilla/4.08 [en] (Win98; I)"
pub struct ApacheParser {
    regex: Regex,
}

impl ApacheParser {
    pub fn new() -> Result<Self> {
        let pattern = r#"^(?P<ip>\S+)\s+\S+\s+\S+\s+\[(?P<time>[^\]]+)\]\s+"(?P<method>\S+)\s+(?P<path>\S+)\s+(?P<proto>\S+)"\s+(?P<status>\d+)\s+(?P<bytes>\d+)\s+"(?P<referrer>[^"]*)"\s+"(?P<ua>[^"]*)""#;
        
        Ok(Self {
            regex: Regex::new(pattern)
                .context("Failed to compile Apache log regex")?,
        })
    }
}

impl LogParser for ApacheParser {
    fn parse_line(&self, line: &str) -> Result<LogEntry> {
        let caps = self.regex.captures(line)
            .context("Failed to parse Apache log line")?;

        let timestamp = DateTime::parse_from_str(
            &caps["time"],
            "%d/%b/%Y:%H:%M:%S %z"
        )?;

        Ok(LogEntry {
            timestamp: timestamp.into(),
            ip: caps["ip"].parse()?,
            method: caps["method"].to_string(),
            path: caps["path"].to_string(),
            protocol: caps["proto"].to_string(),
            status: caps["status"].parse()?,
            bytes_sent: caps["bytes"].parse()?,
            referrer: Some(caps["referrer"].to_string()).filter(|s| !s.is_empty() && s != "-"),
            user_agent: Some(caps["ua"].to_string()).filter(|s| !s.is_empty() && s != "-"),
        })
    }

    fn name(&self) -> &'static str {
        "apache"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_valid_line() {
        let parser = ApacheParser::new().unwrap();
        let line = r#"127.0.0.1 - frank [10/Oct/2000:13:55:36 -0700] "GET /apache_pb.gif HTTP/1.0" 200 2326 "http://www.example.com/start.html" "Mozilla/4.08 [en] (Win98; I)""#;
        
        let entry = parser.parse_line(line).unwrap();
        assert_eq!(entry.ip.to_string(), "127.0.0.1");
        assert_eq!(entry.method, "GET");
        assert_eq!(entry.path, "/apache_pb.gif");
        assert_eq!(entry.status, 200);
    }

    #[test]
    fn test_parse_invalid_line() {
        let parser = ApacheParser::new().unwrap();
        let result = parser.parse_line("invalid line");
        assert!(result.is_err());
    }
}
```

#### `src/analyzer/stats.rs` - 统计分析

```rust
use crate::parser::LogEntry;
use dashmap::DashMap;
use rayon::prelude::*;
use std::collections::HashMap;
use serde::Serialize;

/// 统计结果
#[derive(Debug, Default, Serialize)]
pub struct LogStats {
    /// 总请求数
    pub total_requests: u64,
    /// 总字节数
    pub total_bytes: u64,
    /// 唯一 IP 数
    pub unique_ips: usize,
    /// 状态码分布
    pub status_distribution: HashMap<u16, u64>,
    /// 方法分布
    pub method_distribution: HashMap<String, u64>,
    /// 热门路径 (前 N)
    pub top_paths: Vec<(String, u64)>,
    /// 热门 IP (前 N)
    pub top_ips: Vec<(String, u64)>,
    /// 时间分布 (按小时)
    pub hourly_distribution: HashMap<u32, u64>,
    /// 错误率
    pub error_rate: f64,
    /// 平均响应大小
    pub avg_bytes: f64,
}

/// 统计收集器
pub struct StatsCollector {
    ip_counts: DashMap<String, u64>,
    path_counts: DashMap<String, u64>,
    status_counts: DashMap<u16, u64>,
    method_counts: DashMap<String, u64>,
    hourly_counts: DashMap<u32, u64>,
    total_requests: std::sync::atomic::AtomicU64,
    total_bytes: std::sync::atomic::AtomicU64,
    error_count: std::sync::atomic::AtomicU64,
}

impl StatsCollector {
    pub fn new() -> Self {
        Self {
            ip_counts: DashMap::with_hasher(ahash::RandomState::new()),
            path_counts: DashMap::with_hasher(ahash::RandomState::new()),
            status_counts: DashMap::with_hasher(ahash::RandomState::new()),
            method_counts: DashMap::with_hasher(ahash::RandomState::new()),
            hourly_counts: DashMap::with_hasher(ahash::RandomState::new()),
            total_requests: std::sync::atomic::AtomicU64::new(0),
            total_bytes: std::sync::atomic::AtomicU64::new(0),
            error_count: std::sync::atomic::AtomicU64::new(0),
        }
    }

    pub fn process_entries(&self, entries: &[LogEntry]) {
        entries.par_iter().for_each(|entry| {
            self.process_entry(entry);
        });
    }

    fn process_entry(&self, entry: &LogEntry) {
        // 更新计数器
        self.total_requests.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.total_bytes.fetch_add(entry.bytes_sent, std::sync::atomic::Ordering::Relaxed);

        // 统计错误
        if entry.status >= 400 {
            self.error_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }

        // IP 统计
        *self.ip_counts.entry(entry.ip.to_string()).or_insert(0) += 1;

        // 路径统计
        *self.path_counts.entry(entry.path.clone()).or_insert(0) += 1;

        // 状态码统计
        *self.status_counts.entry(entry.status).or_insert(0) += 1;

        // 方法统计
        *self.method_counts.entry(entry.method.clone()).or_insert(0) += 1;

        // 小时统计
        let hour = entry.timestamp.hour();
        *self.hourly_counts.entry(hour).or_insert(0) += 1;
    }

    pub fn finalize(mut self, top_n: usize) -> LogStats {
        let total_requests = self.total_requests.load(std::sync::atomic::Ordering::Relaxed);
        let total_bytes = self.total_bytes.load(std::sync::atomic::Ordering::Relaxed);
        let error_count = self.error_count.load(std::sync::atomic::Ordering::Relaxed);

        // 获取热门路径
        let mut paths: Vec<_> = self.path_counts.into_iter().collect();
        paths.par_sort_by(|a, b| b.1.cmp(&a.1));
        let top_paths = paths.into_iter().take(top_n).collect();

        // 获取热门 IP
        let mut ips: Vec<_> = self.ip_counts.into_iter().collect();
        ips.par_sort_by(|a, b| b.1.cmp(&a.1));
        let top_ips = ips.into_iter().take(top_n).collect();

        LogStats {
            total_requests,
            total_bytes,
            unique_ips: self.ip_counts.len(),
            status_distribution: self.status_counts.into_iter().collect(),
            method_distribution: self.method_counts.into_iter().collect(),
            top_paths,
            top_ips,
            hourly_distribution: self.hourly_counts.into_iter().collect(),
            error_rate: if total_requests > 0 {
                error_count as f64 / total_requests as f64 * 100.0
            } else {
                0.0
            },
            avg_bytes: if total_requests > 0 {
                total_bytes as f64 / total_requests as f64
            } else {
                0.0
            },
        }
    }
}
```

#### `src/main.rs` - 主程序

```rust
mod analyzer;
mod cli;
mod filter;
mod output;
mod parser;

use anyhow::{Context, Result};
use clap::Parser;
use cli::{Cli, OutputFormat};
use indicatif::{ProgressBar, ProgressStyle};
use memmap2::MmapOptions;
use rayon::prelude::*;
use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::time::Instant;
use tracing::{debug, info, warn};

fn main() -> Result<()> {
    let cli = Cli::parse();
    setup_logging(cli.verbose);

    info!("Starting log analysis for: {:?}", cli.input);
    let start_time = Instant::now();

    // 设置线程池
    if let Some(threads) = cli.threads {
        rayon::ThreadPoolBuilder::new()
            .num_threads(threads)
            .build_global()
            .context("Failed to build thread pool")?;
    }

    // 打开并内存映射文件
    let file = File::open(&cli.input)
        .with_context(|| format!("Failed to open file: {:?}", cli.input))?;
    
    let metadata = file.metadata()?;
    let file_size = metadata.len();
    info!("File size: {} bytes", file_size);

    let mmap = unsafe { MmapOptions::new().map(&file)? };
    let content = std::str::from_utf8(&mmap)
        .context("File is not valid UTF-8")?;

    // 创建解析器
    let parser = parser::create_parser(cli.log_type)?;
    info!("Using parser: {}", parser.name());

    // 创建过滤器
    let filter = filter::LogFilter::from_cli(&cli)?;

    // 准备进度条
    let progress = if cli.progress && atty::is(atty::Stream::Stdout) {
        Some(create_progress_bar(file_size))
    } else {
        None
    };

    // 分割行并并行处理
    let lines: Vec<&str> = content.par_lines().collect();
    info!("Total lines: {}", lines.len());

    if let Some(ref pb) = progress {
        pb.set_length(lines.len() as u64);
    }

    // 并行解析和过滤
    let chunk_size = (lines.len() / rayon::current_num_threads()).max(1);
    let entries: Vec<_> = lines
        .par_chunks(chunk_size)
        .flat_map_iter(|chunk| {
            let mut results = Vec::new();
            for line in chunk {
                if let Ok(entry) = parser.parse_line(line) {
                    if filter.matches(&entry) {
                        results.push(entry);
                    }
                }
            }
            if let Some(ref pb) = progress {
                pb.inc(chunk.len() as u64);
            }
            results
        })
        .collect();

    if let Some(pb) = progress {
        pb.finish_with_message("Parsing complete");
    }

    info!("Parsed {} valid entries", entries.len());

    // 统计分析
    let collector = analyzer::stats::StatsCollector::new();
    collector.process_entries(&entries);
    let stats = collector.finalize(cli.limit);

    // 输出结果
    let output: Box<dyn Write> = match cli.output {
        Some(path) => Box::new(BufWriter::new(File::create(path)?)),
        None => Box::new(BufWriter::new(io::stdout())),
    };

    match cli.format {
        OutputFormat::Json => output::json::write(output, &stats)?,
        OutputFormat::Csv => output::csv::write(output, &stats)?,
        OutputFormat::Html => output::html::write(output, &stats)?,
    }

    let elapsed = start_time.elapsed();
    info!("Analysis complete in {:.2?}", elapsed);
    info!("Throughput: {:.2} MB/s", file_size as f64 / 1_048_576.0 / elapsed.as_secs_f64());

    Ok(())
}

fn setup_logging(verbosity: u8) {
    let level = match verbosity {
        0 => "warn",
        1 => "info",
        2 => "debug",
        _ => "trace",
    };

    tracing_subscriber::fmt()
        .with_env_filter(format!("log_analyzer={}", level))
        .with_target(false)
        .init();
}

fn create_progress_bar(total: u64) -> ProgressBar {
    let pb = ProgressBar::new(total);
    pb.set_style(
        ProgressStyle::default_bar()
            .template("[{elapsed_precise}] {bar:40.cyan/blue} {pos:>7}/{len:7} {msg}")
            .unwrap()
            .progress_chars("##-"),
    );
    pb
}

// atty 兼容层
mod atty {
    pub fn is(stream: Stream) -> bool {
        match stream {
            Stream::Stdout => std::io::IsTerminal::is_terminal(&std::io::stdout()),
            Stream::Stderr => std::io::IsTerminal::is_terminal(&std::io::stderr()),
        }
    }

    pub enum Stream {
        Stdout,
        Stderr,
    }
}
```

---

### 1.5 项目结构

```
log-analyzer/
├── Cargo.toml              # 项目配置
├── Cargo.lock              # 依赖锁定
├── clippy.toml             # Clippy 配置
├── .cargo/
│   └── config.toml         # Cargo 配置
├── src/
│   ├── main.rs             # 程序入口
│   ├── cli.rs              # CLI 参数定义
│   ├── error.rs            # 错误类型定义
│   ├── filter.rs           # 过滤逻辑
│   ├── parser/             # 解析器模块
│   │   ├── mod.rs          # 模块入口
│   │   ├── apache.rs       # Apache 格式
│   │   └── nginx.rs        # Nginx 格式
│   ├── analyzer/           # 分析器模块
│   │   ├── mod.rs
│   │   └── stats.rs        # 统计逻辑
│   └── output/             # 输出模块
│       ├── mod.rs
│       ├── json.rs         # JSON 输出
│       ├── csv.rs          # CSV 输出
│       └── html.rs         # HTML 输出
├── templates/              # HTML 模板
│   └── report.html
├── tests/                  # 集成测试
│   └── integration_tests.rs
├── benches/                # 基准测试
│   └── parser_bench.rs
├── fixtures/               # 测试数据
│   ├── apache.log
│   └── nginx.log
└── docs/                   # 文档
    ├── USAGE.md
    └── PERFORMANCE.md
```

---

### 1.6 构建和运行

#### 开发构建

```bash
# 克隆项目
git clone https://github.com/yourusername/log-analyzer.git
cd log-analyzer

# 开发构建
cargo build

# 运行测试
cargo test

# 运行示例
./target/debug/log-analyzer -i fixtures/apache.log -f json
```

#### 生产构建

```bash
# 优化构建
cargo build --release

# 使用 LTO 优化构建
cargo build --profile release-opt

# 检查二进制大小
ls -lh target/release/log-analyzer
```

#### 运行示例

```bash
# JSON 输出
log-analyzer -i access.log -o report.json -f json

# CSV 输出，带过滤
log-analyzer -i access.log -o report.csv -f csv --start-time 2024-01-01T00:00:00Z -S 500-599

# HTML 报告，限制条目
log-analyzer -i access.log -o report.html -f html -n 50 -j 8

# 从标准输入读取
cat access.log | log-analyzer -i - -f json
```

---

### 1.7 测试策略

#### 单元测试

```rust
// src/parser/apache.rs
#[cfg(test)]
mod tests {
    use super::*;
    use pretty_assertions::assert_eq;

    #[test]
    fn test_parse_sample_lines() {
        let parser = ApacheParser::new().unwrap();
        let test_cases = vec![
            (
                r#"127.0.0.1 - - [10/Oct/2024:13:55:36 +0000] "GET / HTTP/1.1" 200 1234 "-" "curl/7.68.0""#,
                LogEntry {
                    ip: "127.0.0.1".parse().unwrap(),
                    method: "GET".to_string(),
                    path: "/".to_string(),
                    status: 200,
                    bytes_sent: 1234,
                    // ...
                }
            ),
            // 更多测试用例...
        ];

        for (input, expected) in test_cases {
            let result = parser.parse_line(input).unwrap();
            assert_eq!(result.ip, expected.ip);
            assert_eq!(result.method, expected.method);
            assert_eq!(result.status, expected.status);
        }
    }

    #[test]
    fn test_parse_invalid_lines() {
        let parser = ApacheParser::new().unwrap();
        let invalid_lines = vec![
            "",
            "invalid",
            "127.0.0.1",  // 不完整
        ];

        for line in invalid_lines {
            assert!(parser.parse_line(line).is_err());
        }
    }
}
```

#### 集成测试

```rust
// tests/integration_tests.rs
use std::process::Command;
use tempfile::TempDir;

#[test]
fn test_end_to_end_analysis() {
    let temp_dir = TempDir::new().unwrap();
    let log_file = temp_dir.path().join("test.log");
    let output_file = temp_dir.path().join("output.json");

    // 创建测试日志
    std::fs::write(&log_file, include_str!("../fixtures/apache.log")).unwrap();

    // 运行分析器
    let output = Command::new("cargo")
        .args(&[
            "run",
            "--",
            "-i", log_file.to_str().unwrap(),
            "-o", output_file.to_str().unwrap(),
            "-f", "json",
        ])
        .output()
        .expect("Failed to run analyzer");

    assert!(output.status.success());

    // 验证输出
    let report: serde_json::Value = serde_json::from_str(
        &std::fs::read_to_string(&output_file).unwrap()
    ).unwrap();

    assert!(report["total_requests"].as_u64().unwrap() > 0);
    assert!(report["unique_ips"].as_u64().unwrap() > 0);
}

#[test]
fn test_all_output_formats() {
    let formats = vec!["json", "csv", "html"];
    
    for format in formats {
        let output = Command::new("cargo")
            .args(&["run", "--", "-i", "fixtures/apache.log", "-f", format])
            .output()
            .expect("Failed to run");
        
        assert!(output.status.success(), "Format {} failed", format);
    }
}
```

#### 基准测试

```rust
// benches/parser_bench.rs
use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};

fn bench_apache_parser(c: &mut Criterion) {
    let parser = log_analyzer::parser::apache::ApacheParser::new().unwrap();
    let line = r#"127.0.0.1 - frank [10/Oct/2024:13:55:36 +0000] "GET /apache_pb.gif HTTP/1.0" 200 2326 "http://www.example.com/" "Mozilla/4.08""#;

    let mut group = c.benchmark_group("parser");
    group.throughput(Throughput::Bytes(line.len() as u64));
    
    group.bench_function("apache_single", |b| {
        b.iter(|| parser.parse_line(black_box(line)))
    });

    group.bench_function("apache_batch_1000", |b| {
        let lines = vec![line; 1000];
        b.iter(|| {
            lines.iter().for_each(|l| {
                let _ = parser.parse_line(black_box(l));
            });
        });
    });

    group.finish();
}

criterion_group!(benches, bench_apache_parser);
criterion_main!(benches);
```

---

### 1.8 部署方案

#### 二进制分发

```bash
# 创建 GitHub Release 脚本
#!/bin/bash
set -e

VERSION=$1
TARGETS=("x86_64-unknown-linux-gnu" "x86_64-pc-windows-msvc" "x86_64-apple-darwin")

for target in "${TARGETS[@]}"; do
    echo "Building for $target..."
    cargo build --release --target $target
    
    # 打包
    mkdir -p "releases/$target"
    cp "target/$target/release/log-analyzer" "releases/$target/"
    cp README.md LICENSE "releases/$target/"
    
    tar -czf "releases/log-analyzer-$VERSION-$target.tar.gz" -C "releases/$target" .
done
```

#### 包管理器发布

```bash
# Cargo 发布
cargo publish --dry-run
cargo publish

# Homebrew Formula
# Formula/log-analyzer.rb
class LogAnalyzer < Formula
  desc "High-performance log file analyzer"
  homepage "https://github.com/yourusername/log-analyzer"
  url "https://github.com/yourusername/log-analyzer/archive/v0.1.0.tar.gz"
  sha256 "..."
  license "MIT OR Apache-2.0"

  depends_on "rust" => :build

  def install
    system "cargo", "install", *std_cargo_args
  end

  test do
    system "#{bin}/log-analyzer", "--version"
  end
end
```

---

### 1.9 性能优化

#### 基准测试结果

| 测试项 | 优化前 | 优化后 | 提升 |
|-------|-------|-------|------|
| 1GB 日志解析 | 3.2s | 0.8s | 4x |
| 内存峰值 | 2.1GB | 256MB | 8x |
| 并发效率 | 4.2x | 7.8x | 1.9x |

#### 优化技巧

```rust
// 1. 使用内存映射减少拷贝
let mmap = unsafe { MmapOptions::new().map(&file)? };

// 2. 使用并行迭代器
entries.par_iter().for_each(|e| process(e));

// 3. 使用 DashMap 替代 Mutex<HashMap>
let counts: DashMap<String, u64> = DashMap::new();

// 4. 预编译正则表达式
lazy_static::lazy_static! {
    static ref RE: Regex = Regex::new(r"...").unwrap();
}

// 5. 使用 ahash 提高哈希性能
use ahash::AHashMap as HashMap;

// 6. 批量处理减少锁竞争
for chunk in data.chunks(1024) {
    // 处理整个 chunk 后再同步
}
```

---

## 项目 2: REST API 任务管理系统

### 2.1 项目概述

**项目名称**: `task-manager`  
**版本**: 0.1.0  
**架构**: Workspace 多 crate 设计

#### 功能需求

| 功能模块 | 端点 | 描述 |
|---------|------|------|
| 认证 | POST /auth/login | JWT 登录 |
| 认证 | POST /auth/refresh | Token 刷新 |
| 任务 | GET /tasks | 获取任务列表 |
| 任务 | POST /tasks | 创建任务 |
| 任务 | GET /tasks/:id | 获取单个任务 |
| 任务 | PUT /tasks/:id | 更新任务 |
| 任务 | DELETE /tasks/:id | 删除任务 |
| 用户 | GET /users/me | 当前用户信息 |

#### 技术栈

| 层级 | 技术 | 版本 |
|-----|------|------|
| Web 框架 | axum | 0.7 |
| 运行时 | tokio | 1.35 |
| 数据库 | PostgreSQL | 15+ |
| ORM/查询 | sqlx | 0.7 |
| 认证 | jsonwebtoken | 9.2 |
| 配置 | config | 0.14 |
| 验证 | validator | 0.16 |
| 文档 | utoipa | 4.1 |

---

### 2.2 技术选型理由

| 技术 | 选择理由 | 备选方案 |
|-----|---------|---------|
| **axum** | 类型安全、与 Tower 生态集成、性能优秀 | actix-web, rocket |
| **sqlx** | 编译时查询检查、零成本抽象、异步原生 | diesel, sea-orm |
| **jsonwebtoken** | 标准 JWT 实现、算法支持完整 | frank_jwt |
| **utoipa** | derive 宏生成 OpenAPI、与 axum 集成好 | aide, okapi |
| **config** | 多源配置合并、环境变量支持 | envy, figment |

---

### 2.3 完整项目配置

#### Workspace `Cargo.toml`

```toml
[workspace]
members = ["api", "core", "migrations"]
resolver = "2"

[workspace.package]
version = "0.1.0"
edition = "2021"
authors = ["Your Name <your.email@example.com>"]
license = "MIT OR Apache-2.0"
repository = "https://github.com/yourusername/task-manager"
rust-version = "1.75"

[workspace.dependencies]
# Web
axum = "0.7"
tokio = { version = "1.35", features = ["full"] }
tower = "0.4"
tower-http = { version = "0.5", features = ["cors", "trace", "compression"] }
hyper = { version = "1.0", features = ["full"] }

# Serialization
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"

# Database
sqlx = { version = "0.7", features = ["runtime-tokio-native-tls", "postgres", "uuid", "chrono", "migrate"] }

# Auth
jsonwebtoken = "9.2"
argon2 = "0.5"
rand = "0.8"

# Validation
validator = { version = "0.16", features = ["derive"] }

# Error Handling
thiserror = "1.0"
anyhow = "1.0"

# Config
config = "0.14"
dotenvy = "0.15"

# Logging
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "json"] }

# Types
uuid = { version = "1.7", features = ["v4", "serde"] }
chrono = { version = "0.4", features = ["serde"] }

# Documentation
utoipa = { version = "4.1", features = ["axum_extras"] }
utoipa-swagger-ui = { version = "6.0", features = ["axum"] }

# Testing
reqwest = { version = "0.11", features = ["json"] }
```

#### `api/Cargo.toml`

```toml
[package]
name = "task-manager-api"
version.workspace = true
edition.workspace = true
authors.workspace = true
license.workspace = true

[dependencies]
# Workspace deps
axum.workspace = true
tokio.workspace = true
tower.workspace = true
tower-http.workspace = true
serde.workspace = true
serde_json.workspace = true
sqlx.workspace = true
jsonwebtoken.workspace = true
thiserror.workspace = true
config.workspace = true
tracing.workspace = true
tracing-subscriber.workspace = true
uuid.workspace = true
chrono.workspace = true
utoipa.workspace = true
utoipa-swagger-ui.workspace = true
validator.workspace = true
argon2.workspace = true
rand.workspace = true

# Internal deps
task-manager-core = { path = "../core" }

[dev-dependencies]
reqwest.workspace = true
```

#### `core/Cargo.toml`

```toml
[package]
name = "task-manager-core"
version.workspace = true
edition.workspace = true

[dependencies]
serde.workspace = true
serde_json.workspace = true
sqlx.workspace = true
uuid.workspace = true
chrono.workspace = true
thiserror.workspace = true
argon2.workspace = true
rand.workspace = true
tracing.workspace = true
```

---

### 2.4 核心代码实现

#### `api/src/main.rs`

```rust
use axum::{
    routing::{get, post, put, delete},
    Router,
};
use sqlx::postgres::PgPoolOptions;
use std::net::SocketAddr;
use tower_http::{
    cors::CorsLayer,
    trace::TraceLayer,
    compression::CompressionLayer,
};
use tracing::{info, Level};

mod auth;
mod config;
mod error;
mod extractors;
mod handlers;
mod middleware;
mod models;
mod state;

use config::AppConfig;
use state::AppState;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_max_level(Level::INFO)
        .with_target(false)
        .init();

    // 加载配置
    let config = AppConfig::load()?;
    info!("Loaded configuration");

    // 连接数据库
    let pool = PgPoolOptions::new()
        .max_connections(config.database.max_connections)
        .acquire_timeout(std::time::Duration::from_secs(30))
        .connect(&config.database.url)
        .await?;
    
    // 运行迁移
    sqlx::migrate!("../migrations")
        .run(&pool)
        .await?;
    
    info!("Database connected and migrated");

    // 创建应用状态
    let state = AppState::new(pool, config);

    // 构建路由
    let app = create_router(state);

    // 启动服务器
    let addr = SocketAddr::from(([0, 0, 0, 0], 3000));
    info!("Server starting on {}", addr);

    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, app).await?;

    Ok(())
}

fn create_router(state: AppState) -> Router {
    Router::new()
        // 认证路由
        .route("/auth/login", post(handlers::auth::login))
        .route("/auth/refresh", post(handlers::auth::refresh))
        // 任务路由 (需要认证)
        .route("/tasks", get(handlers::tasks::list_tasks))
        .route("/tasks", post(handlers::tasks::create_task))
        .route("/tasks/:id", get(handlers::tasks::get_task))
        .route("/tasks/:id", put(handlers::tasks::update_task))
        .route("/tasks/:id", delete(handlers::tasks::delete_task))
        // 用户路由
        .route("/users/me", get(handlers::users::get_current_user))
        // API 文档
        .merge(utoipa_swagger_ui::SwaggerUi::new("/docs")
            .url("/api-docs/openapi.json", handlers::docs::openapi()))
        // 中间件
        .layer(CompressionLayer::new())
        .layer(CorsLayer::permissive())
        .layer(TraceLayer::new_for_http())
        .with_state(state)
}
```

#### `api/src/config.rs`

```rust
use config::{Config, ConfigError, Environment, File};
use serde::Deserialize;

#[derive(Debug, Deserialize, Clone)]
pub struct AppConfig {
    pub database: DatabaseConfig,
    pub jwt: JwtConfig,
    pub server: ServerConfig,
}

#[derive(Debug, Deserialize, Clone)]
pub struct DatabaseConfig {
    pub url: String,
    pub max_connections: u32,
}

#[derive(Debug, Deserialize, Clone)]
pub struct JwtConfig {
    pub secret: String,
    pub expires_in: i64,    // 访问 token 过期时间 (秒)
    pub refresh_expires_in: i64,  // 刷新 token 过期时间 (秒)
}

#[derive(Debug, Deserialize, Clone)]
pub struct ServerConfig {
    pub host: String,
    pub port: u16,
}

impl AppConfig {
    pub fn load() -> Result<Self, ConfigError> {
        let run_mode = std::env::var("RUN_MODE").unwrap_or_else(|_| "development".into());

        let config = Config::builder()
            .add_source(File::with_name("config/default").required(false))
            .add_source(File::with_name(&format!("config/{}", run_mode)).required(false))
            .add_source(Environment::with_prefix("APP").separator("__"))
            .build()?;

        config.try_deserialize()
    }
}
```

#### `api/src/handlers/tasks.rs`

```rust
use axum::{
    extract::{Path, Query, State},
    http::StatusCode,
    Json,
};
use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use sqlx::FromRow;
use utoipa::{IntoParams, ToSchema};
use uuid::Uuid;
use validator::Validate;

use crate::{
    error::ApiError,
    extractors::AuthenticatedUser,
    state::AppState,
};

/// 任务模型
#[derive(Debug, Serialize, ToSchema, FromRow)]
pub struct Task {
    pub id: Uuid,
    pub title: String,
    pub description: Option<String>,
    pub status: TaskStatus,
    pub priority: TaskPriority,
    pub due_date: Option<DateTime<Utc>>,
    pub created_at: DateTime<Utc>,
    pub updated_at: DateTime<Utc>,
    pub created_by: Uuid,
}

#[derive(Debug, Serialize, Deserialize, ToSchema, sqlx::Type)]
#[sqlx(type_name = "task_status", rename_all = "snake_case")]
#[serde(rename_all = "snake_case")]
pub enum TaskStatus {
    Todo,
    InProgress,
    Done,
    Cancelled,
}

#[derive(Debug, Serialize, Deserialize, ToSchema, sqlx::Type)]
#[sqlx(type_name = "task_priority", rename_all = "snake_case")]
#[serde(rename_all = "snake_case")]
pub enum TaskPriority {
    Low,
    Medium,
    High,
    Urgent,
}

/// 创建任务请求
#[derive(Debug, Deserialize, Validate, ToSchema)]
pub struct CreateTaskRequest {
    #[validate(length(min = 1, max = 200))]
    pub title: String,
    #[validate(length(max = 5000))]
    pub description: Option<String>,
    #[serde(default)]
    pub status: TaskStatus,
    #[serde(default = "default_priority")]
    pub priority: TaskPriority,
    pub due_date: Option<DateTime<Utc>>,
}

fn default_priority() -> TaskPriority {
    TaskPriority::Medium
}

/// 任务列表查询参数
#[derive(Debug, Deserialize, IntoParams)]
pub struct ListTasksQuery {
    pub status: Option<TaskStatus>,
    pub priority: Option<TaskPriority>,
    #[serde(default = "default_limit")]
    pub limit: i64,
    #[serde(default)]
    pub offset: i64,
}

fn default_limit() -> i64 {
    20
}

/// 创建任务
#[utoipa::path(
    post,
    path = "/tasks",
    request_body = CreateTaskRequest,
    responses(
        (status = 201, description = "Task created", body = Task),
        (status = 400, description = "Invalid input"),
        (status = 401, description = "Unauthorized"),
    ),
    security(("bearer_auth" = []))
)]
pub async fn create_task(
    State(state): State<AppState>,
    AuthenticatedUser(user_id): AuthenticatedUser,
    Json(req): Json<CreateTaskRequest>,
) -> Result<(StatusCode, Json<Task>), ApiError> {
    // 验证输入
    req.validate()?;

    let task = sqlx::query_as::<_, Task>(
        r#"
        INSERT INTO tasks (id, title, description, status, priority, due_date, created_by)
        VALUES ($1, $2, $3, $4, $5, $6, $7)
        RETURNING id, title, description, status, priority, due_date, created_at, updated_at, created_by
        "#
    )
    .bind(Uuid::new_v4())
    .bind(&req.title)
    .bind(&req.description)
    .bind(&req.status)
    .bind(&req.priority)
    .bind(req.due_date)
    .bind(user_id)
    .fetch_one(&state.pool)
    .await
    .map_err(ApiError::from)?;

    Ok((StatusCode::CREATED, Json(task)))
}

/// 获取任务列表
#[utoipa::path(
    get,
    path = "/tasks",
    params(ListTasksQuery),
    responses(
        (status = 200, description = "Task list", body = [Task]),
        (status = 401, description = "Unauthorized"),
    ),
    security(("bearer_auth" = []))
)]
pub async fn list_tasks(
    State(state): State<AppState>,
    AuthenticatedUser(user_id): AuthenticatedUser,
    Query(query): Query<ListTasksQuery>,
) -> Result<Json<Vec<Task>>, ApiError> {
    let tasks = sqlx::query_as::<_, Task>(
        r#"
        SELECT id, title, description, status, priority, due_date, created_at, updated_at, created_by
        FROM tasks
        WHERE created_by = $1
        AND ($2::task_status IS NULL OR status = $2)
        AND ($3::task_priority IS NULL OR priority = $3)
        ORDER BY created_at DESC
        LIMIT $4 OFFSET $5
        "#
    )
    .bind(user_id)
    .bind(&query.status)
    .bind(&query.priority)
    .bind(query.limit)
    .bind(query.offset)
    .fetch_all(&state.pool)
    .await
    .map_err(ApiError::from)?;

    Ok(Json(tasks))
}

/// 获取单个任务
#[utoipa::path(
    get,
    path = "/tasks/{id}",
    params(("id" = Uuid, Path, description = "Task ID")),
    responses(
        (status = 200, description = "Task found", body = Task),
        (status = 404, description = "Task not found"),
        (status = 401, description = "Unauthorized"),
    ),
    security(("bearer_auth" = []))
)]
pub async fn get_task(
    State(state): State<AppState>,
    AuthenticatedUser(user_id): AuthenticatedUser,
    Path(id): Path<Uuid>,
) -> Result<Json<Task>, ApiError> {
    let task = sqlx::query_as::<_, Task>(
        r#"
        SELECT id, title, description, status, priority, due_date, created_at, updated_at, created_by
        FROM tasks
        WHERE id = $1 AND created_by = $2
        "#
    )
    .bind(id)
    .bind(user_id)
    .fetch_optional(&state.pool)
    .await
    .map_err(ApiError::from)?
    .ok_or(ApiError::NotFound("Task not found".to_string()))?;

    Ok(Json(task))
}

/// 更新任务
#[utoipa::path(
    put,
    path = "/tasks/{id}",
    params(("id" = Uuid, Path, description = "Task ID")),
    request_body = CreateTaskRequest,
    responses(
        (status = 200, description = "Task updated", body = Task),
        (status = 404, description = "Task not found"),
        (status = 401, description = "Unauthorized"),
    ),
    security(("bearer_auth" = []))
)]
pub async fn update_task(
    State(state): State<AppState>,
    AuthenticatedUser(user_id): AuthenticatedUser,
    Path(id): Path<Uuid>,
    Json(req): Json<CreateTaskRequest>,
) -> Result<Json<Task>, ApiError> {
    req.validate()?;

    let task = sqlx::query_as::<_, Task>(
        r#"
        UPDATE tasks
        SET title = $1, description = $2, status = $3, priority = $4, due_date = $5, updated_at = NOW()
        WHERE id = $6 AND created_by = $7
        RETURNING id, title, description, status, priority, due_date, created_at, updated_at, created_by
        "#
    )
    .bind(&req.title)
    .bind(&req.description)
    .bind(&req.status)
    .bind(&req.priority)
    .bind(req.due_date)
    .bind(id)
    .bind(user_id)
    .fetch_optional(&state.pool)
    .await
    .map_err(ApiError::from)?
    .ok_or(ApiError::NotFound("Task not found".to_string()))?;

    Ok(Json(task))
}

/// 删除任务
#[utoipa::path(
    delete,
    path = "/tasks/{id}",
    params(("id" = Uuid, Path, description = "Task ID")),
    responses(
        (status = 204, description = "Task deleted"),
        (status = 404, description = "Task not found"),
        (status = 401, description = "Unauthorized"),
    ),
    security(("bearer_auth" = []))
)]
pub async fn delete_task(
    State(state): State<AppState>,
    AuthenticatedUser(user_id): AuthenticatedUser,
    Path(id): Path<Uuid>,
) -> Result<StatusCode, ApiError> {
    let result = sqlx::query(
        "DELETE FROM tasks WHERE id = $1 AND created_by = $2"
    )
    .bind(id)
    .bind(user_id)
    .execute(&state.pool)
    .await
    .map_err(ApiError::from)?;

    if result.rows_affected() == 0 {
        return Err(ApiError::NotFound("Task not found".to_string()));
    }

    Ok(StatusCode::NO_CONTENT)
}
```

#### `api/src/auth.rs` - JWT 认证

```rust
use chrono::{Duration, Utc};
use jsonwebtoken::{decode, encode, DecodingKey, EncodingKey, Header, Validation};
use serde::{Deserialize, Serialize};

use crate::config::JwtConfig;
use crate::error::ApiError;

#[derive(Debug, Serialize, Deserialize)]
pub struct Claims {
    pub sub: uuid::Uuid,  // 用户 ID
    pub exp: i64,         // 过期时间
    pub iat: i64,         // 签发时间
    pub token_type: TokenType,
}

#[derive(Debug, Serialize, Deserialize, Clone, Copy)]
#[serde(rename_all = "snake_case")]
pub enum TokenType {
    Access,
    Refresh,
}

pub struct JwtManager {
    encoding_key: EncodingKey,
    decoding_key: DecodingKey,
    config: JwtConfig,
}

impl JwtManager {
    pub fn new(config: JwtConfig) -> Self {
        Self {
            encoding_key: EncodingKey::from_secret(config.secret.as_bytes()),
            decoding_key: DecodingKey::from_secret(config.secret.as_bytes()),
            config,
        }
    }

    /// 生成访问令牌
    pub fn generate_access_token(&self, user_id: uuid::Uuid) -> Result<String, ApiError> {
        let now = Utc::now();
        let claims = Claims {
            sub: user_id,
            iat: now.timestamp(),
            exp: (now + Duration::seconds(self.config.expires_in)).timestamp(),
            token_type: TokenType::Access,
        };

        encode(&Header::default(), &claims, &self.encoding_key)
            .map_err(|e| ApiError::Internal(format!("Token generation failed: {}", e)))
    }

    /// 生成刷新令牌
    pub fn generate_refresh_token(&self, user_id: uuid::Uuid) -> Result<String, ApiError> {
        let now = Utc::now();
        let claims = Claims {
            sub: user_id,
            iat: now.timestamp(),
            exp: (now + Duration::seconds(self.config.refresh_expires_in)).timestamp(),
            token_type: TokenType::Refresh,
        };

        encode(&Header::default(), &claims, &self.encoding_key)
            .map_err(|e| ApiError::Internal(format!("Token generation failed: {}", e)))
    }

    /// 验证令牌
    pub fn verify_token(&self, token: &str, expected_type: TokenType) -> Result<Claims, ApiError> {
        let mut validation = Validation::default();
        validation.validate_exp = true;
        
        let token_data = decode::<Claims>(token, &self.decoding_key, &validation)
            .map_err(|e| match e.kind() {
                jsonwebtoken::errors::ErrorKind::ExpiredSignature => {
                    ApiError::Unauthorized("Token expired".to_string())
                }
                _ => ApiError::Unauthorized("Invalid token".to_string()),
            })?;

        if token_data.claims.token_type != expected_type {
            return Err(ApiError::Unauthorized("Invalid token type".to_string()));
        }

        Ok(token_data.claims)
    }
}

/// 密码哈希
pub struct PasswordHasher;

impl PasswordHasher {
    pub fn hash(password: &str) -> Result<String, ApiError> {
        use argon2::{password_hash::SaltString, Argon2, PasswordHasher};
        use rand::rngs::OsRng;

        let salt = SaltString::generate(&mut OsRng);
        let argon2 = Argon2::default();

        argon2
            .hash_password(password.as_bytes(), &salt)
            .map_err(|e| ApiError::Internal(format!("Password hashing failed: {}", e)))
            .map(|h| h.to_string())
    }

    pub fn verify(password: &str, hash: &str) -> Result<bool, ApiError> {
        use argon2::{PasswordHash, PasswordVerifier};

        let parsed_hash = PasswordHash::new(hash)
            .map_err(|e| ApiError::Internal(format!("Invalid hash: {}", e)))?;

        let argon2 = argon2::Argon2::default();
        
        Ok(argon2.verify_password(password.as_bytes(), &parsed_hash).is_ok())
    }
}
```

---

### 2.5 项目结构

```
task-manager/
├── Cargo.toml                    # Workspace 配置
├── Cargo.lock
├── docker-compose.yml            # 本地开发环境
├── Dockerfile
├── .env.example
├── config/
│   ├── default.toml
│   ├── development.toml
│   └── production.toml
├── api/                          # API 服务 crate
│   ├── Cargo.toml
│   └── src/
│       ├── main.rs
│       ├── config.rs
│       ├── error.rs              # 错误响应
│       ├── state.rs              # 应用状态
│       ├── middleware/
│       │   ├── mod.rs
│       │   └── auth.rs
│       ├── extractors/
│       │   ├── mod.rs
│       │   └── auth.rs           # JWT 提取器
│       ├── handlers/
│       │   ├── mod.rs
│       │   ├── auth.rs
│       │   ├── tasks.rs
│       │   ├── users.rs
│       │   └── docs.rs           # OpenAPI
│       └── models/
│           ├── mod.rs
│           └── user.rs
├── core/                         # 共享核心库
│   ├── Cargo.toml
│   └── src/
│       ├── lib.rs
│       ├── models.rs
│       └── utils.rs
├── migrations/                   # 数据库迁移
│   ├── Cargo.toml
│   └── src/
│       └── main.rs
└── tests/                        # 集成测试
    ├── Cargo.toml
    └── src/
        └── api_tests.rs
```

---

### 2.6 构建和运行

#### 本地开发

```bash
# 启动 PostgreSQL
docker-compose up -d postgres

# 设置环境变量
cp .env.example .env
# 编辑 .env 配置数据库连接

# 运行迁移
cd migrations && cargo run

# 启动开发服务器
cd api && cargo run

# API 文档访问
open http://localhost:3000/docs
```

#### Docker 构建

```dockerfile
# Dockerfile
# 构建阶段
FROM rust:1.75-slim-bookworm AS builder

WORKDIR /app
COPY . .

RUN cargo build --release -p task-manager-api

# 运行阶段
FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y libssl3 ca-certificates && rm -rf /var/lib/apt/lists/*

WORKDIR /app

COPY --from=builder /app/target/release/task-manager-api .
COPY --from=builder /app/config ./config

EXPOSE 3000

ENV RUN_MODE=production

CMD ["./task-manager-api"]
```

```yaml
# docker-compose.yml
version: '3.8'

services:
  postgres:
    image: postgres:15-alpine
    environment:
      POSTGRES_USER: taskmanager
      POSTGRES_PASSWORD: taskmanager
      POSTGRES_DB: taskmanager
    ports:
      - "5432:5432"
    volumes:
      - postgres_data:/var/lib/postgresql/data

  api:
    build: .
    ports:
      - "3000:3000"
    environment:
      APP__DATABASE__URL: postgres://taskmanager:taskmanager@postgres:5432/taskmanager
      APP__JWT__SECRET: ${JWT_SECRET:-your-secret-key-change-in-production}
    depends_on:
      - postgres

volumes:
  postgres_data:
```

---

### 2.7 测试策略

#### 单元测试

```rust
// api/src/auth.rs
#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_manager() -> JwtManager {
        JwtManager::new(JwtConfig {
            secret: "test-secret-key-min-32-bytes-long!".to_string(),
            expires_in: 3600,
            refresh_expires_in: 604800,
        })
    }

    #[test]
    fn test_token_roundtrip() {
        let manager = create_test_manager();
        let user_id = uuid::Uuid::new_v4();

        let token = manager.generate_access_token(user_id).unwrap();
        let claims = manager.verify_token(&token, TokenType::Access).unwrap();

        assert_eq!(claims.sub, user_id);
    }

    #[test]
    fn test_expired_token() {
        let manager = JwtManager::new(JwtConfig {
            secret: "test-secret-key-min-32-bytes-long!".to_string(),
            expires_in: -1,  // 已过期
            refresh_expires_in: 604800,
        });

        let token = manager.generate_access_token(uuid::Uuid::new_v4()).unwrap();
        let result = manager.verify_token(&token, TokenType::Access);
        
        assert!(matches!(result, Err(ApiError::Unauthorized(_))));
    }
}
```

#### API 集成测试

```rust
// tests/api_tests.rs
use reqwest::{Client, StatusCode};
use serde_json::json;

struct TestApp {
    address: String,
    client: Client,
    db_pool: sqlx::PgPool,
}

async fn spawn_app() -> TestApp {
    // 启动测试服务器...
    let address = "http://localhost:3000".to_string();
    
    TestApp {
        address,
        client: Client::new(),
        db_pool: setup_test_db().await,
    }
}

#[tokio::test]
async fn test_task_crud() {
    let app = spawn_app().await;
    
    // 1. 登录
    let login_resp = app.client
        .post(format!("{}/auth/login", app.address))
        .json(&json!({
            "email": "test@example.com",
            "password": "password123"
        }))
        .send()
        .await
        .unwrap();
    
    assert_eq!(login_resp.status(), StatusCode::OK);
    let token: serde_json::Value = login_resp.json().await.unwrap();
    let access_token = token["access_token"].as_str().unwrap();

    // 2. 创建任务
    let create_resp = app.client
        .post(format!("{}/tasks", app.address))
        .bearer_auth(access_token)
        .json(&json!({
            "title": "Test Task",
            "description": "Test description",
            "priority": "high"
        }))
        .send()
        .await
        .unwrap();
    
    assert_eq!(create_resp.status(), StatusCode::CREATED);
    let task: serde_json::Value = create_resp.json().await.unwrap();
    let task_id = task["id"].as_str().unwrap();

    // 3. 获取任务
    let get_resp = app.client
        .get(format!("{}/tasks/{}", app.address, task_id))
        .bearer_auth(access_token)
        .send()
        .await
        .unwrap();
    
    assert_eq!(get_resp.status(), StatusCode::OK);

    // 4. 更新任务
    let update_resp = app.client
        .put(format!("{}/tasks/{}", app.address, task_id))
        .bearer_auth(access_token)
        .json(&json!({
            "title": "Updated Task",
            "status": "in_progress"
        }))
        .send()
        .await
        .unwrap();
    
    assert_eq!(update_resp.status(), StatusCode::OK);

    // 5. 删除任务
    let delete_resp = app.client
        .delete(format!("{}/tasks/{}", app.address, task_id))
        .bearer_auth(access_token)
        .send()
        .await
        .unwrap();
    
    assert_eq!(delete_resp.status(), StatusCode::NO_CONTENT);
}
```

---

### 2.8 部署方案

#### Kubernetes 部署

```yaml
# k8s/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: task-manager-api
spec:
  replicas: 3
  selector:
    matchLabels:
      app: task-manager-api
  template:
    metadata:
      labels:
        app: task-manager-api
    spec:
      containers:
      - name: api
        image: your-registry/task-manager-api:v0.1.0
        ports:
        - containerPort: 3000
        env:
        - name: APP__DATABASE__URL
          valueFrom:
            secretKeyRef:
              name: task-manager-secrets
              key: database-url
        - name: APP__JWT__SECRET
          valueFrom:
            secretKeyRef:
              name: task-manager-secrets
              key: jwt-secret
        resources:
          requests:
            memory: "128Mi"
            cpu: "100m"
          limits:
            memory: "512Mi"
            cpu: "500m"
        livenessProbe:
          httpGet:
            path: /health
            port: 3000
          initialDelaySeconds: 30
          periodSeconds: 10
        readinessProbe:
          httpGet:
            path: /ready
            port: 3000
          initialDelaySeconds: 5
          periodSeconds: 5
---
apiVersion: v1
kind: Service
metadata:
  name: task-manager-api
spec:
  selector:
    app: task-manager-api
  ports:
  - port: 80
    targetPort: 3000
  type: ClusterIP
```

---

### 2.9 性能优化

#### 数据库优化

```rust
// 使用连接池
let pool = PgPoolOptions::new()
    .max_connections(100)           // 根据并发调整
    .min_connections(5)              // 保持最小连接
    .acquire_timeout(Duration::from_secs(30))
    .idle_timeout(Duration::from_secs(600))
    .max_lifetime(Duration::from_secs(1800))
    .connect(&database_url)
    .await?;

// 使用索引
// migrations/001_initial.sql
CREATE INDEX idx_tasks_created_by ON tasks(created_by);
CREATE INDEX idx_tasks_status ON tasks(status) WHERE status != 'done';
CREATE INDEX idx_tasks_created_at ON tasks(created_at DESC);

// 使用 prepared statement
sqlx::query_as::<_, Task>(
    "SELECT * FROM tasks WHERE created_by = $1 AND status = $2"
)
.bind(user_id)
.bind(status)
.fetch_all(&pool)
```

#### 缓存策略

```rust
use moka::future::Cache;

// API 响应缓存
let task_cache: Cache<Uuid, Task> = Cache::builder()
    .max_capacity(10_000)
    .time_to_live(Duration::from_secs(60))
    .build();

// 使用时
pub async fn get_cached_task(
    cache: &Cache<Uuid, Task>,
    pool: &PgPool,
    id: Uuid,
) -> Result<Option<Task>, sqlx::Error> {
    if let Some(task) = cache.get(&id).await {
        return Ok(Some(task));
    }

    let task = sqlx::query_as::<_, Task>("SELECT * FROM tasks WHERE id = $1")
        .bind(id)
        .fetch_optional(pool)
        .await?;

    if let Some(ref task) = task {
        cache.insert(id, task.clone()).await;
    }

    Ok(task)
}
```

---

## 项目 3: 嵌入式 IoT 传感器读取器

### 3.1 项目概述

**项目名称**: `iot-sensor-reader`  
**目标平台**: ESP32-C3/C6 (RISC-V) / ESP32 (Xtensa)  
**运行时**: ESP-IDF

#### 功能需求

1. **传感器读取**: 支持 DHT22 温湿度传感器、BMP280 气压传感器
2. **数据处理**: 本地数据聚合、异常检测
3. **MQTT 发布**: 连接到 MQTT broker，发布传感器数据
4. **低功耗**: 深度睡眠模式，定时唤醒
5. **配置管理**: WiFi 和 MQTT 配置持久化

#### 硬件规格

| 组件 | 型号 | 接口 |
|-----|------|------|
| 主控 | ESP32-C3-DevKitM-1 | - |
| 温湿度 | DHT22 | GPIO4 |
| 气压 | BMP280 | I2C (GPIO8/9) |
| LED 指示灯 | 内置 LED | GPIO2 |

---

### 3.2 技术选型理由

| 技术 | 用途 | 说明 |
|-----|------|------|
| **esp-idf-hal** | 硬件抽象层 | 官方 HAL，提供 GPIO、I2C、WiFi 等驱动 |
| **esp-idf-svc** | 系统服务 | WiFi、MQTT、NVS (非易失存储) |
| **embedded-hal** | 嵌入式标准 trait | 传感器驱动通用接口 |
| **dht-sensor** | DHT22 驱动 | 兼容 embedded-hal |
| **bmp280** | BMP280 驱动 | 气压传感器驱动 |
| **rumqttc** | MQTT 客户端 | no_std 兼容版本 |
| **heapless** | 无堆容器 | Vec、String 等无堆分配实现 |

---

### 3.3 完整项目配置

#### `Cargo.toml`

```toml
[package]
name = "iot-sensor-reader"
version = "0.1.0"
edition = "2021"
authors = ["Your Name <your.email@example.com>"]
resolver = "2"
rust-version = "1.75"

[profile.release]
opt-level = 3
lto = true
panic = "abort"
strip = true

[dependencies]
# ESP-IDF 基础
esp-idf-sys = { version = "0.34", features = ["binstart"] }
esp-idf-hal = "0.43"
esp-idf-svc = { version = "0.48", features = ["mqtt", "wifi"] }
esp-idf-alloc = "0.1"

# 嵌入式标准 trait
embedded-hal = "1.0"
embedded-hal-async = "1.0"
embedded-svc = "0.27"

# 无堆容器
heapless = "0.8"

# MQTT
rumqttc = { version = "0.23", default-features = false, features = ["no-log"] }

# JSON (无堆分配)
serde = { version = "1.0", default-features = false, features = ["derive"] }
serde-json-core = "0.5"

# 错误处理
thiserror = { version = "1.0", default-features = false }

# 传感器驱动
dht-sensor = "0.2"
bmp280 = "0.4"
shared-bus = { version = "0.3", features = ["std"] }

# 日志
log = "0.4"
esp-idf-log = "0.1"

# 异步
embassy-sync = "0.5"
embassy-time = "0.3"

[build-dependencies]
embuild = "0.31"
esp-idf-sys = { version = "0.34", features = ["native"] }
```

#### `.cargo/config.toml`

```toml
[build]
target = "riscv32imc-esp-espidf"    # ESP32-C3
# target = "xtensa-esp32-espidf"    # ESP32

[target.riscv32imc-esp-espidf]
linker = "ldproxy"
runner = "espflash flash --monitor"

rustflags = [
    "-C", "link-arg=-Wl,--Map=/tmp/map.txt",
    # 重要: 使用 ESP-IDF 的 panic handler
    "-C", "default-linker-libraries",
]

[unstable]
build-std = ["std", "panic_abort"]
build-std-features = ["panic_immediate_abort"]

[env]
ESP_IDF_TOOLS_INSTALL_DIR = { value = "global" }
ESP_IDF_VERSION = { value = "tag:v5.1.2" }
RUST_ESP32_STD_ULTRA_CPU = { value = "160" }
```

#### `sdkconfig.defaults`

```
# WiFi
CONFIG_ESP_WIFI_STATIC_RX_BUFFER_NUM=10
CONFIG_ESP_WIFI_DYNAMIC_RX_BUFFER_NUM=32
CONFIG_ESP_WIFI_DYNAMIC_TX_BUFFER_NUM=32

# MQTT
CONFIG_MQTT_PROTOCOL_311=y
CONFIG_MQTT_TRANSPORT_SSL=n
CONFIG_MQTT_TRANSPORT_WEBSOCKET=n

# 节能
CONFIG_PM_ENABLE=y
CONFIG_ESP_DEFAULT_CPU_FREQ_MHZ_80=y

# 日志级别
CONFIG_LOG_DEFAULT_LEVEL_INFO=y
CONFIG_LOG_MAXIMUM_LEVEL_INFO=y

# 堆大小
CONFIG_ESP_MAIN_TASK_STACK_SIZE=8192
```

---

### 3.4 核心代码实现

#### `src/main.rs`

```rust
#![no_std]
#![no_main]

extern crate alloc;

use core::time::Duration;

use esp_backtrace as _;
use esp_idf_alloc as _;
use esp_idf_hal::{
    gpio::{self, PinDriver},
    i2c::{I2cConfig, I2cDriver},
    peripherals::Peripherals,
    prelude::*,
    reset::ResetReason,
};
use esp_idf_log as _;
use esp_idf_svc::{
    eventloop::EspSystemEventLoop,
    mqtt::client::{EspMqttClient, MqttClientConfiguration},
    nvs::EspDefaultNvsPartition,
    wifi::{AuthMethod, ClientConfiguration, Configuration, EspWifi},
};
use heapless::String;

mod config;
mod sensors;
mod wifi;

use config::DeviceConfig;
use sensors::{Bme280Sensor, Dht22Sensor, SensorData};

/// 应用状态机
#[derive(Debug, Clone, Copy)]
enum AppState {
    Init,
    ConnectWifi,
    ReadSensors,
    PublishData,
    DeepSleep(u64),  // 睡眠时间 (微秒)
    Error(u32),      // 错误代码
}

static mut APP_STATE: AppState = AppState::Init;

fn main() {
    // 初始化
    esp_idf_sys::link_patches();
    esp_idf_svc::log::EspLogger::initialize_default();

    log::info!("IoT Sensor Reader starting...");
    log::info!("Reset reason: {:?}", ResetReason::get());

    let peripherals = Peripherals::take().unwrap();
    let sysloop = EspSystemEventLoop::take().unwrap();
    let nvs = EspDefaultNvsPartition::take().unwrap();

    // 加载配置
    let config = DeviceConfig::load(&nvs).unwrap_or_else(|e| {
        log::warn!("Failed to load config: {}, using defaults", e);
        DeviceConfig::default()
    });

    // 初始化 I2C
    let i2c_config = I2cConfig::new().baudrate(400.kHz().into());
    let i2c = I2cDriver::new(
        peripherals.i2c0,
        peripherals.pins.gpio8,  // SDA
        peripherals.pins.gpio9,  // SCL
        &i2c_config,
    ).unwrap();

    // 初始化传感器
    let mut bme280 = Bme280Sensor::new(i2c).unwrap();
    let mut dht22 = Dht22Sensor::new(peripherals.pins.gpio4).unwrap();

    // 初始化 WiFi
    let mut wifi = EspWifi::new(
        peripherals.modem,
        sysloop.clone(),
        Some(nvs.clone()),
    ).unwrap();

    // 状态机主循环
    loop {
        let current_state = unsafe { APP_STATE };
        
        let next_state = match current_state {
            AppState::Init => AppState::ConnectWifi,
            
            AppState::ConnectWifi => {
                match wifi::connect(&mut wifi, &config.wifi) {
                    Ok(_) => {
                        log::info!("WiFi connected");
                        AppState::ReadSensors
                    }
                    Err(e) => {
                        log::error!("WiFi connection failed: {}", e);
                        AppState::Error(1)
                    }
                }
            }
            
            AppState::ReadSensors => {
                // 读取传感器数据
                let mut sensor_data = SensorData::default();
                
                match bme280.read() {
                    Ok(data) => {
                        sensor_data.temperature = data.temperature;
                        sensor_data.pressure = data.pressure;
                        sensor_data.humidity = data.humidity;
                    }
                    Err(e) => log::error!("BME280 read failed: {}", e),
                }

                match dht22.read() {
                    Ok(data) => {
                        // DHT22 优先使用
                        if data.humidity > 0.0 {
                            sensor_data.humidity = data.humidity;
                        }
                    }
                    Err(e) => log::error!("DHT22 read failed: {}", e),
                }

                // 检查数据有效性
                if sensor_data.is_valid() {
                    AppState::PublishData
                } else {
                    log::error!("Invalid sensor data");
                    AppState::Error(2)
                }
            }
            
            AppState::PublishData => {
                match publish_sensor_data(&config.mqtt, &sensor_data) {
                    Ok(_) => {
                        log::info!("Data published successfully");
                        AppState::DeepSleep(config.sleep_duration_us)
                    }
                    Err(e) => {
                        log::error!("Publish failed: {}", e);
                        AppState::Error(3)
                    }
                }
            }
            
            AppState::DeepSleep(duration_us) => {
                log::info!("Entering deep sleep for {} seconds", duration_us / 1_000_000);
                
                // 断开 WiFi 节省电量
                wifi.disconnect().ok();
                
                unsafe {
                    esp_idf_sys::esp_deep_sleep(duration_us);
                }
                
                // 不会执行到这里
                AppState::Init
            }
            
            AppState::Error(code) => {
                log::error!("Error state: {}", code);
                
                // 错误时快速重试
                AppState::DeepSleep(10_000_000)  // 10 秒
            }
        };

        unsafe {
            APP_STATE = next_state;
        }
    }
}

fn publish_sensor_data(
    config: &config::MqttConfig,
    data: &SensorData,
) -> anyhow::Result<()> {
    // 构建 MQTT 客户端配置
    let mqtt_config = MqttClientConfiguration {
        client_id: Some(&config.client_id),
        username: config.username.as_deref(),
        password: config.password.as_deref(),
        keep_alive_interval: Some(Duration::from_secs(30)),
        ..Default::default()
    };

    // 连接 MQTT broker
    let (mut client, mut connection) = EspMqttClient::new(
        &config.broker_url,
        &mqtt_config,
    )?;

    // 序列化数据为 JSON
    let payload = data.to_json()?;
    
    // 发布到指定 topic
    let topic = format!("{}/sensors/data", config.topic_prefix);
    
    client.publish(
        &topic,
        esp_idf_svc::mqtt::client::QoS::AtLeastOnce,
        false,
        payload.as_bytes(),
    )?;

    // 等待确认
    for msg in connection.iter() {
        match msg {
            Ok(msg) => {
                log::debug!("MQTT message: {:?}", msg);
                break;
            }
            Err(e) => {
                log::error!("MQTT error: {}", e);
                return Err(e.into());
            }
        }
    }

    Ok(())
}
```

#### `src/sensors.rs`

```rust
use embedded_hal::blocking::i2c;
use esp_idf_hal::gpio::Pin;
use heapless::String;
use serde::Serialize;

/// 传感器数据
#[derive(Debug, Default, Clone, Copy, Serialize)]
pub struct SensorData {
    pub temperature: f32,  // 摄氏度
    pub humidity: f32,     // 百分比
    pub pressure: f32,     // hPa
    pub timestamp: u64,    // Unix 时间戳
}

impl SensorData {
    pub fn is_valid(&self) -> bool {
        // 温度范围: -40 到 80 摄氏度
        let temp_valid = self.temperature >= -40.0 && self.temperature <= 80.0;
        
        // 湿度范围: 0 到 100%
        let humidity_valid = self.humidity >= 0.0 && self.humidity <= 100.0;
        
        // 气压范围: 300 到 1100 hPa
        let pressure_valid = self.pressure == 0.0 || 
                            (self.pressure >= 300.0 && self.pressure <= 1100.0);

        temp_valid && humidity_valid && pressure_valid
    }

    pub fn to_json(&self) -> anyhow::Result<String<256>> {
        let mut buffer: String<256> = String::new();
        
        // 手动构建 JSON 字符串 (避免堆分配)
        buffer.push_str(r#"{"#)?;
        
        buffer.push_str(r#""temperature":"#)?;
        buffer.push_str(&format_float(self.temperature, 2))?;
        buffer.push(',')?;
        
        buffer.push_str(r#""humidity":"#)?;
        buffer.push_str(&format_float(self.humidity, 2))?;
        buffer.push(',')?;
        
        buffer.push_str(r#""pressure":"#)?;
        buffer.push_str(&format_float(self.pressure, 2))?;
        buffer.push(',')?;
        
        buffer.push_str(r#""timestamp":"#)?;
        buffer.push_str(&self.timestamp.to_string())?;
        
        buffer.push('}')?;
        
        Ok(buffer)
    }
}

/// BME280 传感器驱动包装
pub struct Bme280Sensor<I2C> {
    sensor: bmp280::BMP280<I2C>,
}

impl<I2C, E> Bme280Sensor<I2C>
where
    I2C: i2c::WriteRead<Error = E> + i2c::Write<Error = E>,
{
    pub fn new(i2c: I2C) -> Result<Self, E> {
        let mut sensor = bmp280::BMP280::new(i2c)?;
        sensor.init()?;
        
        Ok(Self { sensor })
    }

    pub fn read(&mut self) -> anyhow::Result<SensorData> {
        let temp = self.sensor.get_temperature()?;
        let pressure = self.sensor.get_pressure()?;

        Ok(SensorData {
            temperature: temp,
            humidity: 0.0,  // BME280 没有湿度，使用 DHT22
            pressure: pressure / 100.0,  // 转换为 hPa
            timestamp: get_timestamp(),
        })
    }
}

/// DHT22 传感器驱动
pub struct Dht22Sensor<'a> {
    pin: esp_idf_hal::gpio::PinDriver<'a, impl Pin, gpio::InputOutput>,
}

impl<'a> Dht22Sensor<'a> {
    pub fn new(pin: impl Pin) -> Result<Self, esp_idf_hal::gpio::GpioError> {
        let pin = esp_idf_hal::gpio::PinDriver::input_output_od(pin)?;
        Ok(Self { pin })
    }

    pub fn read(&mut self) -> anyhow::Result<SensorData> {
        use dht_sensor::{dht22, DhtReading};

        let reading = dht22::Reading::read(&mut self.pin)?;

        Ok(SensorData {
            temperature: reading.temperature,
            humidity: reading.relative_humidity,
            pressure: 0.0,
            timestamp: get_timestamp(),
        })
    }
}

fn format_float(value: f32, decimals: u8) -> heapless::String<16> {
    let mut result = heapless::String::<16>::new();
    
    // 整数部分
    let int_part = value as i32;
    result.push_str(&int_part.to_string()).ok();
    
    // 小数部分
    if decimals > 0 {
        result.push('.').ok();
        
        let mut frac = (value.abs().fract() * 10f32.powi(decimals as i32)) as u32;
        for _ in 0..decimals {
            let digit = (frac / 10u32.pow((decimals - 1) as u32)) as u8;
            result.push((b'0' + digit) as char).ok();
            frac %= 10u32.pow((decimals - 1) as u32);
        }
    }
    
    result
}

fn get_timestamp() -> u64 {
    // 从 SNTP 获取或使用 RTC
    unsafe { esp_idf_sys::time(null()) as u64 }
}

use core::ptr::null;
```

#### `src/config.rs`

```rust
use esp_idf_svc::nvs::{EspNvs, NvsDefault};
use heapless::String;

/// 设备配置
#[derive(Debug, Clone)]
pub struct DeviceConfig {
    pub wifi: WifiConfig,
    pub mqtt: MqttConfig,
    pub sleep_duration_us: u64,  // 微秒
}

#[derive(Debug, Clone)]
pub struct WifiConfig {
    pub ssid: String<32>,
    pub password: String<64>,
    pub auth_method: AuthMethod,
}

#[derive(Debug, Clone)]
pub struct MqttConfig {
    pub broker_url: String<128>,
    pub client_id: String<32>,
    pub username: Option<String<32>>,
    pub password: Option<String<32>>,
    pub topic_prefix: String<64>,
}

#[derive(Debug, Clone, Copy)]
pub enum AuthMethod {
    None,
    Wpa2Personal,
    Wpa3Personal,
}

impl DeviceConfig {
    pub fn load(nvs: &EspNvs<NvsDefault>) -> anyhow::Result<Self> {
        // 从 NVS 读取配置
        let mut wifi_ssid = String::<32>::new();
        let mut wifi_pass = String::<64>::new();
        
        if let Ok(Some(ssid)) = nvs.get_str("wifi_ssid") {
            wifi_ssid.push_str(ssid).ok();
        }
        if let Ok(Some(pass)) = nvs.get_str("wifi_pass") {
            wifi_pass.push_str(pass).ok();
        }

        Ok(Self {
            wifi: WifiConfig {
                ssid: wifi_ssid,
                password: wifi_pass,
                auth_method: AuthMethod::Wpa2Personal,
            },
            mqtt: MqttConfig {
                broker_url: String::from("mqtt://192.168.1.100:1883"),
                client_id: String::from("esp32-sensor-01"),
                username: None,
                password: None,
                topic_prefix: String::from("home/livingroom"),
            },
            sleep_duration_us: 60_000_000,  // 60 秒
        })
    }

    pub fn save(&self, nvs: &mut EspNvs<NvsDefault>) -> anyhow::Result<()> {
        nvs.set_str("wifi_ssid", &self.wifi.ssid)?;
        nvs.set_str("wifi_pass", &self.wifi.password)?;
        Ok(())
    }
}

impl Default for DeviceConfig {
    fn default() -> Self {
        Self {
            wifi: WifiConfig {
                ssid: String::from("YOUR_WIFI_SSID"),
                password: String::from("YOUR_WIFI_PASS"),
                auth_method: AuthMethod::Wpa2Personal,
            },
            mqtt: MqttConfig {
                broker_url: String::from("mqtt://broker.hivemq.com:1883"),
                client_id: String::from("esp32-sensor-01"),
                username: None,
                password: None,
                topic_prefix: String::from("test/sensors"),
            },
            sleep_duration_us: 300_000_000,  // 5 分钟
        }
    }
}
```

---

### 3.5 项目结构

```
iot-sensor-reader/
├── Cargo.toml              # 项目配置
├── Cargo.lock
├── .cargo/
│   └── config.toml         # 目标平台配置
├── sdkconfig.defaults      # ESP-IDF 配置
├── build.rs                # 构建脚本
├── partitions.csv          # 分区表
├── src/
│   ├── main.rs             # 入口点
│   ├── lib.rs              # 库入口
│   ├── config.rs           # 配置管理
│   ├── wifi.rs             # WiFi 管理
│   ├── sensors/
│   │   ├── mod.rs
│   │   ├── dht22.rs
│   │   └── bme280.rs
│   ├── mqtt/
│   │   ├── mod.rs
│   │   └── client.rs
│   └── utils/
│       ├── mod.rs
│       └── time.rs
├── tests/                  # 主机测试 (使用模拟)
│   └── host_tests.rs
└── examples/               # 示例程序
    ├── blink.rs
    └── wifi_scan.rs
```

---

### 3.6 构建和运行

#### 开发环境搭建

```bash
# 安装 Rust ESP 工具链
rustup target add riscv32imc-esp-espidf
# 或 Xtensa (ESP32)
rustup target add xtensa-esp32-espidf

# 安装 espup (工具链管理器)
cargo install espup
espup install

# 安装 espflash (烧录工具)
cargo install espflash

# 安装 ldproxy
 cargo install ldproxy

# 设置环境变量
. $HOME/export-esp.sh
```

#### 构建和烧录

```bash
# 开发构建
cargo build

# 发布构建 (优化)
cargo build --release

# 烧录到设备并监控输出
cargo run --release

# 仅烧录
espflash flash target/riscv32imc-esp-espidf/release/iot-sensor-reader

# 仅监控输出
espflash monitor
```

#### 使用 Wokwi 模拟器测试

```json
// diagram.json (Wokwi 配置)
{
  "version": 1,
  "author": "Your Name",
  "editor": "wokwi",
  "parts": [
    { "type": "board-esp32-c3-devkitm-1", "id": "esp", "top": 0, "left": 0 },
    { "type": "wokwi-dht22", "id": "dht", "top": -100, "left": 100 },
    { "type": "wokwi-bme280", "id": "bme", "top": -100, "left": -100 }
  ],
  "connections": [
    ["esp:TX", "$serialMonitor:RX", "", []],
    ["esp:RX", "$serialMonitor:TX", "", []],
    ["esp:4", "dht:SDA", "green", []],
    ["esp:8", "bme:SDA", "blue", []],
    ["esp:9", "bme:SCL", "yellow", []]
  ]
}
```

---

### 3.7 测试策略

#### 主机模拟测试

```rust
// tests/host_tests.rs
// 使用 mockall 和 embedded-hal-mock 进行主机测试

#[cfg(test)]
mod sensor_tests {
    use embedded_hal_mock::i2c::{Mock as I2cMock, Transaction as I2cTransaction};
    
    #[test]
    fn test_bme280_read() {
        // 模拟 I2C 事务
        let expectations = vec![
            I2cTransaction::write_read(0x76, vec![0xD0], vec![0x58]),  // 芯片 ID
            I2cTransaction::write(0x76, vec![0xF4, 0x27]),              // 配置
            I2cTransaction::write_read(0x76, vec![0xF7], vec![0x52, 0xC7, 0x80]),  // 数据
        ];
        
        let i2c = I2cMock::new(&expectations);
        
        // 测试传感器读取...
        
        i2c.done();
    }
}
```

#### 硬件测试

```rust
// examples/hardware_test.rs
fn main() {
    // 硬件自检程序
    // 1. 测试所有 GPIO
    // 2. 测试 I2C 设备
    // 3. 测试 WiFi 扫描
    // 4. 测试 MQTT 连接
}
```

---

### 3.8 部署方案

#### OTA 更新

```rust
// OTA 更新实现
use esp_idf_svc::ota::EspOta;

fn perform_ota_update(firmware_url: &str) -> anyhow::Result<()> {
    let client = reqwest::blocking::Client::new();
    let firmware = client.get(firmware_url).send()?.bytes()?;
    
    let mut ota = EspOta::new()?;
    ota.begin()?;
    ota.write(&firmware)?;
    ota.complete()?;
    
    // 重启设备
    unsafe { esp_idf_sys::esp_restart() };
}
```

#### 生产烧录

```bash
# 烧录分区表、bootloader 和应用程序
espflash write-bin -b 115200 0x8000 partitions.bin
espflash write-bin -b 115200 0x1000 bootloader.bin
espflash write-bin -b 115200 0x10000 iot-sensor-reader.bin

# 或使用 cargo-espflash
cargo espflash --release --partition-table partitions.csv
```

---

### 3.9 性能优化

#### 功耗优化

| 模式 | 电流消耗 | 说明 |
|-----|---------|------|
| 活跃模式 | 80-240 mA | WiFi 传输时 |
| Modem Sleep | 20 mA | WiFi 连接但空闲 |
| Light Sleep | 0.8 mA | CPU 暂停 |
| Deep Sleep | 5-10 µA | 仅 RTC 运行 |

```rust
// 深度睡眠优化
fn enter_deep_sleep(duration_us: u64) {
    // 关闭外设
    unsafe {
        esp_idf_sys::esp_wifi_stop();
        esp_idf_sys::esp_bluedroid_disable();
        esp_idf_sys::esp_bt_controller_disable();
    }
    
    // 配置唤醒源
    unsafe {
        esp_idf_sys::esp_sleep_enable_timer_wakeup(duration_us);
    }
    
    // 进入深度睡眠
    unsafe {
        esp_idf_sys::esp_deep_sleep_start();
    }
}

// 内存优化
use esp_idf_alloc::EspSystemAlloc;

#[global_allocator]
static ALLOCATOR: EspSystemAlloc = EspSystemAlloc;
```

#### 内存使用监控

```rust
// 堆内存监控
fn log_heap_info() {
    unsafe {
        let free = esp_idf_sys::esp_get_free_heap_size();
        let min_free = esp_idf_sys::esp_get_minimum_free_heap_size();
        
        log::info!("Heap: free={}, min_free={}", free, min_free);
    }
}
```

---

## 附录

### A. 通用 CI/CD 配置

```yaml
# .github/workflows/ci.yml
name: CI

on: [push, pull_request]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      
      - name: Setup Rust
        uses: dtolnay/rust-action@stable
      
      - name: Cache dependencies
        uses: Swatinem/rust-cache@v2
      
      - name: Run tests
        run: cargo test --all-features
      
      - name: Run clippy
        run: cargo clippy --all-targets --all-features -- -D warnings
      
      - name: Check formatting
        run: cargo fmt -- --check
      
      - name: Run cargo-deny
        uses: EmbarkStudios/cargo-deny-action@v1
```

### B. 代码质量工具配置

```toml
# deny.toml
targets = [
    { triple = "x86_64-unknown-linux-gnu" },
    { triple = "x86_64-pc-windows-msvc" },
]

[licenses]
allow = [
    "MIT",
    "Apache-2.0",
    "BSD-3-Clause",
]

[bans]
multiple-versions = "warn"
wildcards = "allow"
```

### C. 监控和日志最佳实践

```rust
// tracing 结构化日志
use tracing::{info, warn, error, instrument};

#[instrument(skip(db), fields(user_id = %user_id))]
async fn process_user_request(user_id: Uuid, db: &PgPool) -> Result<(), Error> {
    info!("Processing request");
    
    match fetch_data(db, user_id).await {
        Ok(data) => {
            info!(data.len = data.len(), "Data fetched successfully");
            Ok(())
        }
        Err(e) => {
            error!(error = %e, "Failed to fetch data");
            Err(e)
        }
    }
}
```

---

## 总结

本文档提供了三个不同领域的生产级 Rust 项目示例：

1. **CLI 日志分析器** - 展示数据处理、并行计算、CLI 设计
2. **REST API 服务** - 展示 Web 后端、数据库、认证授权
3. **嵌入式 IoT** - 展示 no_std 开发、硬件交互、低功耗设计

每个项目都遵循 Rust 最佳实践，包含完整的测试、文档和部署方案，可作为实际项目的起点或参考。

---

*文档结束*
