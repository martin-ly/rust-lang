# CLI 应用开发指南

> **创建日期**: 2026-02-13
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 文档定位

本指南为官方 **Command Line Book** 的补充与项目内导航，帮助在开发 Rust 命令行应用时快速定位到本项目的相关模块和示例。

**形式化引用**：T-OW2、T-BR1（进程间资源）、[SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS](../research_notes/SAFE_UNSAFE_COMPREHENSIVE_ANALYSIS.md)（子进程安全边界）。

---

## 官方 CLI Book 入口

| 资源 | URL | 说明 |
| :--- | :--- | :--- |
| **Command Line Book** | <https://rust-cli.github.io/book/> | 官方 CLI 应用开发教程 |
| **CLI Book 源码** | <https://github.com/rust-cli/book> | 贡献与反馈 |

---

## 本项目对应模块

| CLI 开发主题 | 官方 CLI Book | 本项目对应 |
| :--- | :--- | :--- |
| 参数解析 | clap、structopt | C03 控制流、[cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) |
| 标准输入输出 | std::io | [C07 进程管理](../../crates/c07_process/) |
| 子进程与管道 | std::process | C07 [进程管理](../../crates/c07_process/docs/) |
| 文件系统 | std::fs | C03、C08 算法 |
| 错误处理 | anyhow、thiserror | [error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md) |
| 异步 CLI | tokio | [C06 异步](../../crates/c06_async/)、[async_patterns](../02_reference/quick_reference/async_patterns.md) |

---

## 快速开始示例

### 1. 最小 CLI 应用

```rust
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("用法: {} <名称>", args[0]);
        std::process::exit(1);
    }

    println!("你好, {}!", args[1]);
}
```

### 2. 使用 clap 构建专业 CLI

```toml
[dependencies]
clap = { version = "4.0", features = ["derive"] }
```

```rust
use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(name = "mycli")]
#[command(about = "一个示例 CLI 工具")]
struct Cli {
    #[arg(short, long, help = "设置 verbose 模式")]
    verbose: bool,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// 添加文件
    Add { path: String },
    /// 删除文件
    Remove { path: String },
    /// 列出所有文件
    List,
}

fn main() {
    let cli = Cli::parse();

    if cli.verbose {
        println!("Verbose 模式已启用");
    }

    match cli.command {
        Commands::Add { path } => {
            println!("添加文件: {}", path);
        }
        Commands::Remove { path } => {
            println!("删除文件: {}", path);
        }
        Commands::List => {
            println!("列出所有文件...");
        }
    }
}
```

### 3. 异步 CLI 示例

```toml
[dependencies]
tokio = { version = "1.0", features = ["full"] }
reqwest = { version = "0.11", features = ["json"] }
clap = { version = "4.0", features = ["derive"] }
```

```rust
use clap::Parser;
use reqwest;

#[derive(Parser)]
#[command(name = "httpcli")]
struct Args {
    #[arg(help = "要请求的 URL")]
    url: String,
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let args = Args::parse();

    let response = reqwest::get(&args.url).await?;
    let body = response.text().await?;

    println!("{}", body);

    Ok(())
}
```

### 4. 带进度条的 CLI

```toml
[dependencies]
indicatif = "0.17"
```

```rust
use indicatif::{ProgressBar, ProgressStyle};
use std::thread;
use std::time::Duration;

fn main() {
    let pb = ProgressBar::new(100);
    pb.set_style(
        ProgressStyle::default_bar()
            .template("{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} ({eta})")
            .unwrap()
    );

    for i in 0..100 {
        thread::sleep(Duration::from_millis(50));
        pb.set_position(i + 1);
    }

    pb.finish_with_message("完成！");
}
```

### 5. 错误处理最佳实践 {#错误处理最佳实践}

```rust
use thiserror::Error;

#[derive(Error, Debug)]
enum CliError {
    #[error("IO 错误: {0}")]
    Io(#[from] std::io::Error),

    #[error("解析错误: {0}")]
    Parse(String),

    #[error("无效参数: {0}")]
    InvalidArg(String),
}

type Result<T> = std::result::Result<T, CliError>;

fn process_file(path: &str) -> Result<String> {
    if path.is_empty() {
        return Err(CliError::InvalidArg("路径不能为空".to_string()));
    }

    let content = std::fs::read_to_string(path)?;
    Ok(content)
}

fn main() {
    match process_file("test.txt") {
        Ok(content) => println!("{}", content),
        Err(e) => {
            eprintln!("错误: {}", e);
            std::process::exit(1);
        }
    }
}
```

---

## 推荐学习路径

1. **入门**: 通读 [Command Line Book](https://rust-cli.github.io/book/) 快速教程
2. **巩固**: 学习 C07 进程管理（std::process、std::io）
3. **进阶**: C03 错误处理 + [error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md)
4. **高级**: C06 异步 + 高性能 CLI 工具开发

---

## 常用 crate 推荐

| 用途 | crate | 说明 |
| :--- | :--- | :--- |
| 参数解析 | clap | 最流行的 CLI 参数解析库 |
| 错误处理 | anyhow、thiserror | 生产级错误传播 |
| 终端交互 | crossterm、ratatui | TUI 应用 |
| 进度条 | indicatif | 进度显示 |
| 彩色输出 | colored、owo-colors | 终端彩色文本 |
| 日志 | tracing、env_logger | 日志记录 |
| 配置 | config、clap | 配置文件管理 |

---

## 最佳实践

### 1. 使用 `?` 操作符传播错误

```rust
fn read_config(path: &str) -> Result<Config, Box<dyn std::error::Error>> {
    let content = std::fs::read_to_string(path)?;
    let config: Config = toml::from_str(&content)?;
    Ok(config)
}
```

### 2. 提供有意义的错误信息

```rust
fn main() {
    if let Err(e) = run() {
        eprintln!("{} {}", "错误:".red().bold(), e);
        std::process::exit(1);
    }
}
```

### 3. 使用 exit codes

```rust
use std::process::ExitCode;

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("错误: {}", e);
            ExitCode::FAILURE
        }
    }
}
```

---

## 使用场景

### 场景1: 简单命令行工具

快速构建文件处理工具：

```rust
// 使用 std::env 处理简单参数
// 适用于：批量重命名、日志分析、数据转换
```

### 场景2: 专业级 CLI 应用

构建类似 `cargo` 或 `rg` 的专业工具：

- 使用 [clap](#2-使用-clap-构建专业-cli) 定义复杂子命令
- 添加 [进度条](#4-带进度条的-cli) 提升用户体验
- 实现 [彩色输出](#2-提供有意义的错误信息)

### 场景3: 异步 CLI 工具

构建网络相关的 CLI 工具：

- 使用 [tokio](#3-异步-cli-示例) 处理并发请求
- 实现 [超时处理](#错误处理最佳实践)
- 参考 [C06 异步](../../crates/c06_async/docs/00_MASTER_INDEX.md) 深入学习

### 场景4: TUI 应用

构建终端用户界面应用：

- 使用 `ratatui` 创建交互式界面
- 结合 [C07 进程管理](../../crates/c07_process/) 处理子进程
- 实现键盘导航和事件处理

---

## 形式化链接

| 链接类型 | 目标文档 |
| :--- | :--- |
| **前置知识** | [C03 控制流](../../crates/c03_control_fn/docs/00_MASTER_INDEX.md) |
| :--- | :--- |
| **错误处理** | [error_handling_cheatsheet](../02_reference/quick_reference/error_handling_cheatsheet.md) |
| **异步编程** | [C06 异步](../../crates/c06_async/docs/00_MASTER_INDEX.md) |
| :--- | :--- |
| **Cargo 工具** | [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md) |
| **相关指南** | [TROUBLESHOOTING_GUIDE.md](./TROUBLESHOOTING_GUIDE.md) |
| :--- | :--- |

---

## 相关文档

- [C07 进程管理](../../crates/c07_process/docs/00_MASTER_INDEX.md)
- [故障排查指南](./TROUBLESHOOTING_GUIDE.md)
- [cargo_cheatsheet](../02_reference/quick_reference/cargo_cheatsheet.md)
- [官方 Command Line Book](https://rust-cli.github.io/book/)
- [C03 控制流](../../crates/c03_control_fn/docs/00_MASTER_INDEX.md)
- [C06 异步](../../crates/c06_async/docs/00_MASTER_INDEX.md)
