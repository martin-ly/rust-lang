# Rust CLI 工具开发实战指南 (2025)

> **全面掌握 Rust CLI 工具开发，打造专业命令行应用**
>
> **版本**: Rust 1.90+ | **更新日期**: 2025-10-20 | **难度**: ⭐⭐⭐

## 📊 目录

- [Rust CLI 工具开发实战指南 (2025)](#rust-cli-工具开发实战指南-2025)
  - [📊 目录](#-目录)
  - [📋 目录1](#-目录1)
  - [1. CLI 开发基础1](#1-cli-开发基础1)
    - [1.1 为什么用 Rust 开发 CLI1](#11-为什么用-rust-开发-cli1)
    - [1.2 Hello CLI1](#12-hello-cli1)
    - [1.3 项目结构1](#13-项目结构1)
  - [2. 命令行参数解析1](#2-命令行参数解析1)
    - [2.1 Clap 基础1](#21-clap-基础1)
    - [2.2 子命令1](#22-子命令1)
    - [2.3 高级参数处理1](#23-高级参数处理1)
  - [3. 用户交互1](#3-用户交互1)
    - [3.1 输入输出1](#31-输入输出1)
    - [3.2 交互式提示1](#32-交互式提示1)
    - [3.3 进度条1](#33-进度条1)
  - [4. 配置管理1](#4-配置管理1)
    - [4.1 环境变量1](#41-环境变量1)
    - [4.2 配置文件1](#42-配置文件1)
    - [4.3 优先级管理1](#43-优先级管理1)
  - [5. 错误处理1](#5-错误处理1)
    - [5.1 Error 类型设计1](#51-error-类型设计1)
    - [5.2 友好的错误消息1](#52-友好的错误消息1)
    - [5.3 退出码1](#53-退出码1)
  - [6. 日志和调试1](#6-日志和调试1)
    - [6.1 日志级别1](#61-日志级别1)
    - [6.2 彩色输出1](#62-彩色输出1)
    - [6.3 调试模式1](#63-调试模式1)
  - [7. 文件和目录操作1](#7-文件和目录操作1)
    - [7.1 文件读写1](#71-文件读写1)
    - [7.2 目录遍历1](#72-目录遍历1)
    - [7.3 文件监控1](#73-文件监控1)
  - [8. 实战案例1](#8-实战案例1)
    - [8.1 文件搜索工具1](#81-文件搜索工具1)
    - [8.2 JSON 处理工具1](#82-json-处理工具1)
    - [8.3 Git 子命令工具1](#83-git-子命令工具1)
  - [9. 打包和发布1](#9-打包和发布1)
    - [9.1 跨平台编译1](#91-跨平台编译1)
    - [9.2 安装脚本1](#92-安装脚本1)
    - [9.3 发布到 crates.io1](#93-发布到-cratesio1)
  - [10. 常见陷阱1](#10-常见陷阱1)
  - [11. 最佳实践1](#11-最佳实践1)
  - [12. 参考资源1](#12-参考资源1)
    - [官方文档](#官方文档)
    - [推荐库](#推荐库)
    - [学习资源](#学习资源)
  - [总结](#总结)

## 📋 目录1

- [Rust CLI 工具开发实战指南 (2025)](#rust-cli-工具开发实战指南-2025)
  - [📊 目录](#-目录)
  - [📋 目录1](#-目录1)
  - [1. CLI 开发基础1](#1-cli-开发基础1)
    - [1.1 为什么用 Rust 开发 CLI1](#11-为什么用-rust-开发-cli1)
    - [1.2 Hello CLI1](#12-hello-cli1)
    - [1.3 项目结构1](#13-项目结构1)
  - [2. 命令行参数解析1](#2-命令行参数解析1)
    - [2.1 Clap 基础1](#21-clap-基础1)
    - [2.2 子命令1](#22-子命令1)
    - [2.3 高级参数处理1](#23-高级参数处理1)
  - [3. 用户交互1](#3-用户交互1)
    - [3.1 输入输出1](#31-输入输出1)
    - [3.2 交互式提示1](#32-交互式提示1)
    - [3.3 进度条1](#33-进度条1)
  - [4. 配置管理1](#4-配置管理1)
    - [4.1 环境变量1](#41-环境变量1)
    - [4.2 配置文件1](#42-配置文件1)
    - [4.3 优先级管理1](#43-优先级管理1)
  - [5. 错误处理1](#5-错误处理1)
    - [5.1 Error 类型设计1](#51-error-类型设计1)
    - [5.2 友好的错误消息1](#52-友好的错误消息1)
    - [5.3 退出码1](#53-退出码1)
  - [6. 日志和调试1](#6-日志和调试1)
    - [6.1 日志级别1](#61-日志级别1)
    - [6.2 彩色输出1](#62-彩色输出1)
    - [6.3 调试模式1](#63-调试模式1)
  - [7. 文件和目录操作1](#7-文件和目录操作1)
    - [7.1 文件读写1](#71-文件读写1)
    - [7.2 目录遍历1](#72-目录遍历1)
    - [7.3 文件监控1](#73-文件监控1)
  - [8. 实战案例1](#8-实战案例1)
    - [8.1 文件搜索工具1](#81-文件搜索工具1)
    - [8.2 JSON 处理工具1](#82-json-处理工具1)
    - [8.3 Git 子命令工具1](#83-git-子命令工具1)
  - [9. 打包和发布1](#9-打包和发布1)
    - [9.1 跨平台编译1](#91-跨平台编译1)
    - [9.2 安装脚本1](#92-安装脚本1)
    - [9.3 发布到 crates.io1](#93-发布到-cratesio1)
  - [10. 常见陷阱1](#10-常见陷阱1)
  - [11. 最佳实践1](#11-最佳实践1)
  - [12. 参考资源1](#12-参考资源1)
    - [官方文档](#官方文档)
    - [推荐库](#推荐库)
    - [学习资源](#学习资源)
  - [总结](#总结)

---

## 1. CLI 开发基础1

### 1.1 为什么用 Rust 开发 CLI1

**Rust CLI 的优势**:

```text
┌────────────────────────────────────────────────────────────┐
│              Rust CLI 工具的核心优势                       │
├────────────────────────────────────────────────────────────┤
│  ⚡ 性能    - 接近 C/C++ 的执行速度                        │
│  📦 分发    - 单一二进制文件，无运行时依赖                │
│  🔒 可靠性  - 编译时保证内存安全和线程安全                │
│  🛠️  生态    - 丰富的 CLI 开发库 (clap, tokio, serde)     │
│  📊 维护性  - 强类型系统减少运行时错误                     │
└────────────────────────────────────────────────────────────┘
```

### 1.2 Hello CLI1

```rust
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();
    
    if args.len() < 2 {
        eprintln!("用法: {} <name>", args[0]);
        std::process::exit(1);
    }
    
    println!("Hello, {}!", args[1]);
}
```

**运行**:

```bash
$ cargo run -- World
Hello, World!
```

### 1.3 项目结构1

```text
my-cli/
├── Cargo.toml
├── src/
│   ├── main.rs          # 入口文件
│   ├── cli.rs           # CLI 定义
│   ├── commands/        # 子命令实现
│   │   ├── mod.rs
│   │   ├── list.rs
│   │   └── add.rs
│   ├── config.rs        # 配置管理
│   ├── error.rs         # 错误类型
│   └── utils.rs         # 工具函数
├── tests/               # 集成测试
│   └── cli_tests.rs
└── README.md
```

---

## 2. 命令行参数解析1

### 2.1 Clap 基础1

```rust
use clap::Parser;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 基本 CLI 定义
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Parser)]
#[command(name = "mycli")]
#[command(about = "A simple CLI tool", long_about = None)]
struct Cli {
    /// 输入文件路径
    #[arg(short, long)]
    input: String,
    
    /// 输出文件路径
    #[arg(short, long)]
    output: Option<String>,
    
    /// 详细输出
    #[arg(short, long)]
    verbose: bool,
    
    /// 重复次数
    #[arg(short = 'n', long, default_value = "1")]
    count: u32,
}

fn main() {
    let cli = Cli::parse();
    
    println!("Input: {}", cli.input);
    println!("Output: {:?}", cli.output);
    println!("Verbose: {}", cli.verbose);
    println!("Count: {}", cli.count);
}
```

**使用**:

```bash
$ mycli --input file.txt --output out.txt --verbose --count 3
Input: file.txt
Output: Some("out.txt")
Verbose: true
Count: 3
```

### 2.2 子命令1

```rust
use clap::{Parser, Subcommand};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 带子命令的 CLI
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Parser)]
#[command(name = "git-like")]
#[command(about = "A git-like CLI tool")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Add a new item
    Add {
        /// Item name
        name: String,
        
        /// Item description
        #[arg(short, long)]
        description: Option<String>,
    },
    
    /// List all items
    List {
        /// Show detailed information
        #[arg(short, long)]
        verbose: bool,
    },
    
    /// Remove an item
    Remove {
        /// Item ID
        id: u32,
    },
}

fn main() {
    let cli = Cli::parse();
    
    match cli.command {
        Commands::Add { name, description } => {
            println!("Adding item: {}", name);
            if let Some(desc) = description {
                println!("Description: {}", desc);
            }
        }
        Commands::List { verbose } => {
            println!("Listing items (verbose: {})", verbose);
        }
        Commands::Remove { id } => {
            println!("Removing item with ID: {}", id);
        }
    }
}
```

**使用**:

```bash
$ git-like add "Task 1" --description "First task"
Adding item: Task 1
Description: First task

$ git-like list --verbose
Listing items (verbose: true)

$ git-like remove 123
Removing item with ID: 123
```

### 2.3 高级参数处理1

```rust
use clap::{Parser, ValueEnum};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 枚举参数
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum OutputFormat {
    Json,
    Yaml,
    Toml,
}

#[derive(Parser)]
struct Cli {
    /// Output format
    #[arg(short = 'f', long, value_enum, default_value = "json")]
    format: OutputFormat,
    
    /// File paths (multiple values)
    #[arg(short, long, num_args = 1..)]
    files: Vec<String>,
    
    /// Enable all features
    #[arg(long, conflicts_with = "minimal")]
    full: bool,
    
    /// Enable minimal features
    #[arg(long, conflicts_with = "full")]
    minimal: bool,
}

fn main() {
    let cli = Cli::parse();
    
    println!("Format: {:?}", cli.format);
    println!("Files: {:?}", cli.files);
}
```

**使用**:

```bash
$ mycli --format yaml --files file1.txt file2.txt file3.txt
Format: Yaml
Files: ["file1.txt", "file2.txt", "file3.txt"]
```

---

## 3. 用户交互1

### 3.1 输入输出1

```rust
use std::io::{self, Write};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 读取用户输入
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn read_user_input(prompt: &str) -> io::Result<String> {
    print!("{}", prompt);
    io::stdout().flush()?;
    
    let mut input = String::new();
    io::stdin().read_line(&mut input)?;
    
    Ok(input.trim().to_string())
}

fn main() -> io::Result<()> {
    let name = read_user_input("请输入你的名字: ")?;
    println!("你好, {}!", name);
    
    Ok(())
}
```

### 3.2 交互式提示1

```rust
use dialoguer::{Confirm, Input, Select};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// dialoguer: 交互式提示库
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() {
    // 文本输入
    let name: String = Input::new()
        .with_prompt("你的名字")
        .default("Alice".to_string())
        .interact()
        .unwrap();
    
    // 选择
    let languages = &["Rust", "Go", "Python", "TypeScript"];
    let selection = Select::new()
        .with_prompt("选择你最喜欢的语言")
        .items(languages)
        .default(0)
        .interact()
        .unwrap();
    
    println!("你选择了: {}", languages[selection]);
    
    // 确认
    if Confirm::new()
        .with_prompt("是否继续?")
        .interact()
        .unwrap()
    {
        println!("继续执行...");
    } else {
        println!("已取消");
    }
}
```

### 3.3 进度条1

```rust
use indicatif::{ProgressBar, ProgressStyle};
use std::thread;
use std::time::Duration;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// indicatif: 进度条和加载动画
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() {
    // 基本进度条
    let pb = ProgressBar::new(100);
    for _ in 0..100 {
        pb.inc(1);
        thread::sleep(Duration::from_millis(50));
    }
    pb.finish_with_message("完成!");
    
    // 自定义样式
    let pb = ProgressBar::new(100);
    pb.set_style(
        ProgressStyle::default_bar()
            .template("[{elapsed_precise}] {bar:40.cyan/blue} {pos:>7}/{len:7} {msg}")
            .unwrap()
            .progress_chars("=>-"),
    );
    
    for i in 0..100 {
        pb.set_message(format!("Processing item {}", i));
        pb.inc(1);
        thread::sleep(Duration::from_millis(30));
    }
    pb.finish_with_message("全部完成!");
}
```

---

## 4. 配置管理1

### 4.1 环境变量1

```rust
use std::env;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 读取环境变量
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() {
    // 必需的环境变量
    let api_key = env::var("API_KEY")
        .expect("环境变量 API_KEY 未设置");
    
    // 可选的环境变量
    let log_level = env::var("LOG_LEVEL")
        .unwrap_or_else(|_| "info".to_string());
    
    // 解析为特定类型
    let max_retries: u32 = env::var("MAX_RETRIES")
        .unwrap_or_else(|_| "3".to_string())
        .parse()
        .expect("MAX_RETRIES 必须是数字");
    
    println!("API Key: {}", api_key);
    println!("Log Level: {}", log_level);
    println!("Max Retries: {}", max_retries);
}
```

### 4.2 配置文件1

```rust
use serde::{Deserialize, Serialize};
use config::{Config, ConfigError, File};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 配置结构
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Debug, Deserialize, Serialize)]
struct Settings {
    server: ServerConfig,
    database: DatabaseConfig,
}

#[derive(Debug, Deserialize, Serialize)]
struct ServerConfig {
    host: String,
    port: u16,
}

#[derive(Debug, Deserialize, Serialize)]
struct DatabaseConfig {
    url: String,
    max_connections: u32,
}

impl Settings {
    fn new() -> Result<Self, ConfigError> {
        let config = Config::builder()
            .add_source(File::with_name("config/default"))
            .add_source(File::with_name("config/local").required(false))
            .build()?;
        
        config.try_deserialize()
    }
}

fn main() -> Result<(), ConfigError> {
    let settings = Settings::new()?;
    
    println!("Server: {}:{}", settings.server.host, settings.server.port);
    println!("Database URL: {}", settings.database.url);
    
    Ok(())
}
```

**config/default.toml**:

```toml
[server]
host = "0.0.0.0"
port = 8080

[database]
url = "postgres://localhost/mydb"
max_connections = 10
```

### 4.3 优先级管理1

```rust
use clap::Parser;
use std::env;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 配置优先级: CLI 参数 > 环境变量 > 配置文件 > 默认值
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Parser)]
struct Cli {
    /// Server port
    #[arg(short, long)]
    port: Option<u16>,
}

fn get_port() -> u16 {
    let cli = Cli::parse();
    
    // 1. CLI 参数
    if let Some(port) = cli.port {
        return port;
    }
    
    // 2. 环境变量
    if let Ok(port_str) = env::var("APP_PORT") {
        if let Ok(port) = port_str.parse() {
            return port;
        }
    }
    
    // 3. 配置文件 (略)
    
    // 4. 默认值
    8080
}

fn main() {
    let port = get_port();
    println!("Using port: {}", port);
}
```

---

## 5. 错误处理1

### 5.1 Error 类型设计1

```rust
use thiserror::Error;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 自定义错误类型
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Error, Debug)]
pub enum CliError {
    #[error("文件不存在: {path}")]
    FileNotFound { path: String },
    
    #[error("IO 错误: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("解析错误: {0}")]
    Parse(String),
    
    #[error("配置无效: {0}")]
    InvalidConfig(String),
}

type Result<T> = std::result::Result<T, CliError>;

fn read_config(path: &str) -> Result<String> {
    if !std::path::Path::new(path).exists() {
        return Err(CliError::FileNotFound {
            path: path.to_string(),
        });
    }
    
    std::fs::read_to_string(path).map_err(Into::into)
}

fn main() {
    match read_config("config.toml") {
        Ok(content) => println!("配置内容: {}", content),
        Err(e) => eprintln!("错误: {}", e),
    }
}
```

### 5.2 友好的错误消息1

```rust
use colored::*;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 彩色错误消息
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn print_error(message: &str) {
    eprintln!("{} {}", "错误:".red().bold(), message);
}

fn print_warning(message: &str) {
    eprintln!("{} {}", "警告:".yellow().bold(), message);
}

fn print_success(message: &str) {
    println!("{} {}", "成功:".green().bold(), message);
}

fn main() {
    print_error("无法连接到数据库");
    print_warning("配置文件使用默认值");
    print_success("任务完成!");
}
```

### 5.3 退出码1

```rust
use std::process;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 标准退出码
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
const EXIT_SUCCESS: i32 = 0;
const EXIT_FAILURE: i32 = 1;
const EXIT_INVALID_INPUT: i32 = 2;

fn main() {
    let result = run_app();
    
    match result {
        Ok(_) => process::exit(EXIT_SUCCESS),
        Err(e) => {
            eprintln!("错误: {}", e);
            process::exit(EXIT_FAILURE);
        }
    }
}

fn run_app() -> Result<(), String> {
    // 应用逻辑
    Ok(())
}
```

---

## 6. 日志和调试1

### 6.1 日志级别1

```rust
use env_logger;
use log::{debug, error, info, warn};

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 日志记录
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() {
    env_logger::init();
    
    debug!("调试信息");
    info!("普通信息");
    warn!("警告信息");
    error!("错误信息");
}
```

**使用**:

```bash
$ RUST_LOG=debug cargo run
[DEBUG] 调试信息
[INFO] 普通信息
[WARN] 警告信息
[ERROR] 错误信息
```

### 6.2 彩色输出1

```rust
use colored::*;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 彩色终端输出
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() {
    println!("{}", "普通文本".normal());
    println!("{}", "红色文本".red());
    println!("{}", "绿色文本".green());
    println!("{}", "粗体".bold());
    println!("{}", "粗体红色".red().bold());
    println!("{}", "背景黄色".on_yellow());
}
```

### 6.3 调试模式1

```rust
use clap::Parser;
use log::LevelFilter;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 调试模式
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Parser)]
struct Cli {
    /// Enable debug mode
    #[arg(short, long)]
    debug: bool,
}

fn main() {
    let cli = Cli::parse();
    
    let log_level = if cli.debug {
        LevelFilter::Debug
    } else {
        LevelFilter::Info
    };
    
    env_logger::Builder::new()
        .filter_level(log_level)
        .init();
    
    log::debug!("调试模式已启用");
    log::info!("应用启动");
}
```

---

## 7. 文件和目录操作1

### 7.1 文件读写1

```rust
use std::fs;
use std::io::Write;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 文件操作
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() -> std::io::Result<()> {
    // 读取文件
    let content = fs::read_to_string("input.txt")?;
    println!("文件内容: {}", content);
    
    // 写入文件
    fs::write("output.txt", "Hello, file!")?;
    
    // 追加到文件
    let mut file = fs::OpenOptions::new()
        .append(true)
        .create(true)
        .open("log.txt")?;
    
    writeln!(file, "New log entry")?;
    
    Ok(())
}
```

### 7.2 目录遍历1

```rust
use walkdir::WalkDir;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// walkdir: 递归目录遍历
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() {
    for entry in WalkDir::new("src")
        .into_iter()
        .filter_map(|e| e.ok())
    {
        if entry.file_type().is_file() {
            println!("{}", entry.path().display());
        }
    }
}
```

### 7.3 文件监控1

```rust
use notify::{watcher, RecursiveMode, Watcher};
use std::sync::mpsc::channel;
use std::time::Duration;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// notify: 文件系统监控
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
fn main() {
    let (tx, rx) = channel();
    let mut watcher = watcher(tx, Duration::from_secs(1)).unwrap();
    
    watcher
        .watch("src", RecursiveMode::Recursive)
        .unwrap();
    
    println!("监控 src 目录...");
    
    loop {
        match rx.recv() {
            Ok(event) => println!("文件变化: {:?}", event),
            Err(e) => eprintln!("错误: {:?}", e),
        }
    }
}
```

---

## 8. 实战案例1

### 8.1 文件搜索工具1

```rust
use clap::Parser;
use regex::Regex;
use std::fs;
use walkdir::WalkDir;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// 简单的 grep 工具
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Parser)]
#[command(name = "rgrep")]
#[command(about = "Search for patterns in files")]
struct Cli {
    /// Pattern to search for
    pattern: String,
    
    /// Directory to search in
    #[arg(default_value = ".")]
    path: String,
}

fn main() {
    let cli = Cli::parse();
    let regex = Regex::new(&cli.pattern).expect("Invalid regex");
    
    for entry in WalkDir::new(&cli.path)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().is_file())
    {
        if let Ok(content) = fs::read_to_string(entry.path()) {
            for (line_num, line) in content.lines().enumerate() {
                if regex.is_match(line) {
                    println!(
                        "{}:{}:{}",
                        entry.path().display(),
                        line_num + 1,
                        line
                    );
                }
            }
        }
    }
}
```

### 8.2 JSON 处理工具1

```rust
use clap::Parser;
use serde_json::Value;
use std::fs;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// JSON 格式化工具
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Parser)]
#[command(name = "jfmt")]
#[command(about = "Format JSON files")]
struct Cli {
    /// Input JSON file
    input: String,
    
    /// Pretty print
    #[arg(short, long)]
    pretty: bool,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    
    let content = fs::read_to_string(&cli.input)?;
    let value: Value = serde_json::from_str(&content)?;
    
    let output = if cli.pretty {
        serde_json::to_string_pretty(&value)?
    } else {
        serde_json::to_string(&value)?
    };
    
    println!("{}", output);
    
    Ok(())
}
```

### 8.3 Git 子命令工具1

```rust
use clap::{Parser, Subcommand};
use std::process::Command;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Git 子命令工具
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#[derive(Parser)]
#[command(name = "git-enhanced")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Quick commit with message
    Qcommit {
        /// Commit message
        message: String,
    },
    
    /// Show repository statistics
    Stats,
}

fn main() {
    let cli = Cli::parse();
    
    match cli.command {
        Commands::Qcommit { message } => {
            // git add -A
            Command::new("git")
                .args(&["add", "-A"])
                .status()
                .expect("git add failed");
            
            // git commit -m "message"
            Command::new("git")
                .args(&["commit", "-m", &message])
                .status()
                .expect("git commit failed");
            
            println!("快速提交完成!");
        }
        Commands::Stats => {
            // git log --oneline | wc -l
            let output = Command::new("git")
                .args(&["log", "--oneline"])
                .output()
                .expect("git log failed");
            
            let commit_count = String::from_utf8_lossy(&output.stdout)
                .lines()
                .count();
            
            println!("总提交数: {}", commit_count);
        }
    }
}
```

---

## 9. 打包和发布1

### 9.1 跨平台编译1

```bash
# Linux -> Windows
cargo build --release --target x86_64-pc-windows-gnu

# Linux -> macOS
cargo build --release --target x86_64-apple-darwin

# 列出所有支持的目标
rustup target list
```

### 9.2 安装脚本1

```bash
#!/bin/bash
# install.sh

set -e

# 检测操作系统
OS="$(uname -s)"
case "$OS" in
    Linux)  TARGET="x86_64-unknown-linux-gnu" ;;
    Darwin) TARGET="x86_64-apple-darwin" ;;
    *)      echo "不支持的操作系统: $OS"; exit 1 ;;
esac

# 下载二进制文件
URL="https://github.com/user/repo/releases/latest/download/mycli-$TARGET"
curl -L "$URL" -o /usr/local/bin/mycli

# 添加执行权限
chmod +x /usr/local/bin/mycli

echo "安装完成! 运行 'mycli --help' 查看帮助"
```

### 9.3 发布到 crates.io1

```bash
# 登录 crates.io
cargo login

# 发布
cargo publish
```

**Cargo.toml**:

```toml
[package]
name = "mycli"
version = "0.1.0"
authors = ["Your Name <you@example.com>"]
edition = "2021"
description = "A CLI tool for..."
license = "MIT"
repository = "https://github.com/user/mycli"
keywords = ["cli", "tool"]
categories = ["command-line-utilities"]
```

---

## 10. 常见陷阱1

1. **忘记刷新 stdout**
   - 使用 `print!` 时需要 `stdout().flush()`

2. **错误处理不完整**
   - 所有可能失败的操作都应该处理错误
   - 给用户友好的错误提示

3. **未测试边界情况**
   - 空文件
   - 非常大的文件
   - 无效输入

4. **跨平台兼容性**
   - 使用 `std::path::PathBuf` 而非字符串拼接路径
   - 测试不同操作系统

5. **性能问题**
   - 避免频繁的系统调用
   - 使用缓冲 IO

---

## 11. 最佳实践1

1. **提供清晰的帮助文档**
   - 使用 `--help` 显示详细用法
   - 提供示例

2. **支持管道操作**
   - 从 stdin 读取输入
   - 输出到 stdout

3. **遵循 UNIX 哲学**
   - 单一职责
   - 可组合

4. **提供进度反馈**
   - 长时间操作显示进度条
   - 详细模式输出日志

5. **版本控制**
   - 使用 `--version` 显示版本号
   - 遵循语义化版本

---

## 12. 参考资源1

### 官方文档

- [Rust CLI Book](https://rust-cli.github.io/book/)
- [Clap](https://docs.rs/clap)

### 推荐库

- [clap](https://crates.io/crates/clap) - 参数解析
- [dialoguer](https://crates.io/crates/dialoguer) - 交互式提示
- [indicatif](https://crates.io/crates/indicatif) - 进度条
- [colored](https://crates.io/crates/colored) - 彩色输出

### 学习资源

- [Command Line Apps in Rust](https://rust-cli.github.io/book/)
- [Rust CLI Examples](https://github.com/rust-cli)

---

## 总结

Rust CLI 开发的核心优势:

1. **高性能** - 快速启动，低内存占用
2. **可靠性** - 编译时错误检查
3. **易分发** - 单一二进制文件
4. **丰富生态** - 成熟的 CLI 开发库

通过本指南，你已经掌握了 Rust CLI 工具开发的核心技术和最佳实践！
