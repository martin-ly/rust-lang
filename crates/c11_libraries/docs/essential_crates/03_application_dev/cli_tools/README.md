# CLI 工具开发

> **核心库**: clap, dialoguer, indicatif, console, colored  
> **适用场景**: 命令行工具、交互式程序、进度显示、终端美化

---

## 📋 目录

- [CLI 工具开发](#cli-工具开发)
  - [📋 目录](#-目录)
  - [概述](#概述)
    - [CLI 工具特点](#cli-工具特点)
    - [Rust CLI 生态](#rust-cli-生态)
  - [核心库对比](#核心库对比)
    - [功能矩阵](#功能矩阵)
    - [选择指南](#选择指南)
  - [clap - 参数解析](#clap---参数解析)
    - [核心特性](#核心特性)
    - [基础用法：Derive API](#基础用法derive-api)
    - [高级用法：子命令](#高级用法子命令)
    - [参数验证](#参数验证)
  - [dialoguer - 交互输入](#dialoguer---交互输入)
    - [核心特性1](#核心特性1)
    - [基础用法：输入和选择](#基础用法输入和选择)
    - [高级用法：多选和确认](#高级用法多选和确认)
    - [自定义主题](#自定义主题)
  - [indicatif - 进度显示](#indicatif---进度显示)
    - [核心特性2](#核心特性2)
    - [基础用法：进度条](#基础用法进度条)
    - [高级用法：多进度条](#高级用法多进度条)
    - [自定义样式](#自定义样式)
  - [console - 终端控制](#console---终端控制)
    - [核心特性3](#核心特性3)
    - [颜色输出](#颜色输出)
    - [终端操作](#终端操作)
  - [实战场景](#实战场景)
    - [场景1: 文件处理工具](#场景1-文件处理工具)
    - [场景2: 交互式配置生成器](#场景2-交互式配置生成器)
    - [场景3: 下载管理器](#场景3-下载管理器)
  - [最佳实践](#最佳实践)
    - [1. 提供详细的帮助信息](#1-提供详细的帮助信息)
    - [2. 错误处理友好](#2-错误处理友好)
    - [3. 使用颜色突出重要信息](#3-使用颜色突出重要信息)
    - [4. 长时间操作显示进度](#4-长时间操作显示进度)
    - [5. 支持管道和重定向](#5-支持管道和重定向)
  - [常见陷阱](#常见陷阱)
    - [⚠️ 陷阱1: 忘记处理 Ctrl+C](#️-陷阱1-忘记处理-ctrlc)
    - [⚠️ 陷阱2: 进度条更新过于频繁](#️-陷阱2-进度条更新过于频繁)
    - [⚠️ 陷阱3: 不检查终端类型](#️-陷阱3-不检查终端类型)
    - [⚠️ 陷阱4: 硬编码颜色](#️-陷阱4-硬编码颜色)
  - [参考资源](#参考资源)
    - [官方文档](#官方文档)
    - [教程与文章](#教程与文章)
    - [示例项目](#示例项目)
    - [相关文档](#相关文档)

---

## 概述

### CLI 工具特点

**好的 CLI 工具应该具备**:

1. **直观的参数**: 清晰的命令行参数和帮助信息
2. **友好的错误**: 详细的错误提示和解决建议
3. **进度反馈**: 长时间操作显示进度
4. **交互性**: 必要时支持交互式输入
5. **跨平台**: Windows、macOS、Linux 一致体验
6. **性能**: 启动快、执行快

**典型 CLI 工具示例**:

- `cargo`: Rust 包管理器
- `git`: 版本控制工具
- `ripgrep`: 快速搜索工具
- `fd`: 现代文件查找工具

### Rust CLI 生态

**为什么选择 Rust**:

- ✅ **性能**: 接近 C/C++ 的性能
- ✅ **跨平台**: 一次编译，到处运行
- ✅ **错误处理**: 强大的类型系统
- ✅ **生态**: 丰富的 CLI 工具库
- ✅ **静态链接**: 单文件分发

**核心库**:

- **clap**: 参数解析（最流行）
- **dialoguer**: 交互式输入
- **indicatif**: 进度条和 spinner
- **console**: 终端控制和颜色
- **colored**: 简单的颜色输出
- **env_logger**: 日志输出

---

## 核心库对比

### 功能矩阵

| 库 | 用途 | 特点 | 学习曲线 | 推荐度 |
|-----|------|------|---------|--------|
| **clap** | 参数解析 | 功能全面、自动帮助 | 低 | ⭐⭐⭐⭐⭐ |
| **dialoguer** | 交互输入 | 易用、美观 | 低 | ⭐⭐⭐⭐⭐ |
| **indicatif** | 进度显示 | 多样式、多进度条 | 低 | ⭐⭐⭐⭐⭐ |
| **console** | 终端控制 | 跨平台、颜色支持 | 低 | ⭐⭐⭐⭐ |
| **colored** | 颜色输出 | 简单易用 | 极低 | ⭐⭐⭐⭐ |
| **tui** | TUI 界面 | 功能强大、复杂 | 高 | ⭐⭐⭐ |

### 选择指南

| 场景 | 推荐工具 | 理由 |
|------|---------|------|
| **简单命令行** | clap | 参数解析即可 |
| **交互式工具** | clap + dialoguer | 参数 + 交互输入 |
| **长时间任务** | clap + indicatif | 参数 + 进度显示 |
| **完整 CLI 工具** | clap + dialoguer + indicatif | 全功能 |
| **复杂 TUI** | tui (ratatui) | 全屏终端界面 |
| **简单颜色输出** | colored | 快速上手 |

---

## clap - 参数解析

### 核心特性

- ✅ **自动生成帮助**: `--help` 和 `--version`
- ✅ **参数验证**: 类型检查、范围检查
- ✅ **子命令**: 类似 `git commit`, `cargo build`
- ✅ **环境变量**: 从环境变量读取参数
- ✅ **配置文件**: 支持配置文件读取
- ✅ **Shell 补全**: 自动生成补全脚本

**安装**:

```toml
[dependencies]
clap = { version = "4.4", features = ["derive"] }
```

### 基础用法：Derive API

```rust
use clap::Parser;

/// Simple file processor
#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Input file path
    #[arg(short, long)]
    input: String,
    
    /// Output file path
    #[arg(short, long, default_value = "output.txt")]
    output: String,
    
    /// Verbose mode
    #[arg(short, long)]
    verbose: bool,
    
    /// Number of threads
    #[arg(short = 'j', long, default_value_t = 4)]
    threads: usize,
}

fn main() {
    let cli = Cli::parse();
    
    println!("Input: {}", cli.input);
    println!("Output: {}", cli.output);
    println!("Threads: {}", cli.threads);
    
    if cli.verbose {
        println!("Verbose mode enabled");
    }
}
```

**运行效果**:

```bash
$ myapp --help
Simple file processor

Usage: myapp [OPTIONS] --input <INPUT>

Options:
  -i, --input <INPUT>      Input file path
  -o, --output <OUTPUT>    Output file path [default: output.txt]
  -v, --verbose            Verbose mode
  -j, --threads <THREADS>  Number of threads [default: 4]
  -h, --help               Print help
  -V, --version            Print version

$ myapp -i input.txt -v
Input: input.txt
Output: output.txt
Threads: 4
Verbose mode enabled
```

### 高级用法：子命令

```rust
use clap::{Parser, Subcommand};

#[derive(Parser)]
#[command(author, version, about)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Add a new item
    Add {
        /// Item name
        #[arg(short, long)]
        name: String,
        
        /// Item description
        #[arg(short, long)]
        description: Option<String>,
    },
    
    /// List all items
    List {
        /// Filter by tag
        #[arg(short, long)]
        tag: Option<String>,
    },
    
    /// Remove an item
    Remove {
        /// Item ID
        id: u32,
    },
}

fn main() {
    let cli = Cli::parse();
    
    match &cli.command {
        Commands::Add { name, description } => {
            println!("Adding: {}", name);
            if let Some(desc) = description {
                println!("Description: {}", desc);
            }
        }
        Commands::List { tag } => {
            println!("Listing items");
            if let Some(t) = tag {
                println!("Filter by tag: {}", t);
            }
        }
        Commands::Remove { id } => {
            println!("Removing item ID: {}", id);
        }
    }
}
```

**运行效果**:

```bash
$ myapp add --name "Task 1" --description "Do something"
Adding: Task 1
Description: Do something

$ myapp list --tag "important"
Listing items
Filter by tag: important

$ myapp remove 42
Removing item ID: 42
```

### 参数验证

```rust
use clap::Parser;

fn validate_port(s: &str) -> Result<u16, String> {
    let port: u16 = s.parse().map_err(|_| format!("'{}' 不是有效的端口号", s))?;
    
    if port < 1024 {
        return Err("端口号必须 >= 1024".to_string());
    }
    
    Ok(port)
}

#[derive(Parser)]
struct Cli {
    /// Server port (must be >= 1024)
    #[arg(short, long, value_parser = validate_port)]
    port: u16,
    
    /// Server host
    #[arg(short = 'H', long, default_value = "localhost")]
    host: String,
}

fn main() {
    let cli = Cli::parse();
    println!("Server will run on {}:{}", cli.host, cli.port);
}
```

**运行效果**:

```bash
$ myapp --port 80
error: invalid value '80' for '--port <PORT>': 端口号必须 >= 1024

$ myapp --port 8080
Server will run on localhost:8080
```

---

## dialoguer - 交互输入

### 核心特性1

- ✅ **文本输入**: 单行、多行、密码
- ✅ **选择**: 单选、多选
- ✅ **确认**: Yes/No
- ✅ **编辑器**: 调用外部编辑器
- ✅ **主题**: 自定义颜色和样式

**安装**:

```toml
[dependencies]
dialoguer = "0.11"
```

### 基础用法：输入和选择

```rust
use dialoguer::{Input, Select, Password};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 文本输入
    let name: String = Input::new()
        .with_prompt("Your name")
        .default("Guest".to_string())
        .interact_text()?;
    
    // 密码输入（隐藏）
    let password: String = Password::new()
        .with_prompt("Password")
        .with_confirmation("Confirm password", "Passwords do not match")
        .interact()?;
    
    // 单选
    let colors = vec!["Red", "Green", "Blue", "Yellow"];
    let selection = Select::new()
        .with_prompt("Choose your favorite color")
        .items(&colors)
        .default(0)
        .interact()?;
    
    println!("Name: {}", name);
    println!("Selected color: {}", colors[selection]);
    
    Ok(())
}
```

**运行效果**:

```text
Your name [Guest]: Alice
Password: ********
Confirm password: ********
? Choose your favorite color
> Red
  Green
  Blue
  Yellow

Name: Alice
Selected color: Red
```

### 高级用法：多选和确认

```rust
use dialoguer::{MultiSelect, Confirm, theme::ColorfulTheme};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // 多选
    let options = vec![
        "Feature A",
        "Feature B",
        "Feature C",
        "Feature D",
    ];
    
    let selections = MultiSelect::with_theme(&ColorfulTheme::default())
        .with_prompt("Select features to enable")
        .items(&options)
        .interact()?;
    
    if selections.is_empty() {
        println!("No features selected");
    } else {
        println!("Selected features:");
        for &i in &selections {
            println!("  - {}", options[i]);
        }
    }
    
    // 确认
    let confirmed = Confirm::new()
        .with_prompt("Do you want to continue?")
        .default(true)
        .interact()?;
    
    if confirmed {
        println!("Continuing...");
    } else {
        println!("Aborted");
    }
    
    Ok(())
}
```

**运行效果**:

```text
? Select features to enable
  [x] Feature A
  [ ] Feature B
  [x] Feature C
  [ ] Feature D

Selected features:
  - Feature A
  - Feature C

? Do you want to continue? (Y/n) y
Continuing...
```

### 自定义主题

```rust
use dialoguer::{Input, theme::CustomPromptCharacterTheme};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let theme = CustomPromptCharacterTheme::new('🚀');
    
    let name: String = Input::with_theme(&theme)
        .with_prompt("Project name")
        .interact_text()?;
    
    println!("Creating project: {}", name);
    
    Ok(())
}
```

**运行效果**:

```text
🚀 Project name: my-awesome-app
Creating project: my-awesome-app
```

---

## indicatif - 进度显示

### 核心特性2

- ✅ **进度条**: 确定和不确定进度
- ✅ **Spinner**: 加载动画
- ✅ **多进度条**: 并发任务显示
- ✅ **自定义样式**: 模板和颜色
- ✅ **速率显示**: 处理速度、剩余时间

**安装**:

```toml
[dependencies]
indicatif = "0.17"
```

### 基础用法：进度条

```rust
use indicatif::{ProgressBar, ProgressStyle};
use std::time::Duration;
use std::thread;

fn main() {
    // 简单进度条
    let pb = ProgressBar::new(100);
    
    for _ in 0..100 {
        pb.inc(1);
        thread::sleep(Duration::from_millis(50));
    }
    pb.finish_with_message("Done!");
    
    println!("\n");
    
    // 自定义样式进度条
    let pb = ProgressBar::new(1024);
    pb.set_style(
        ProgressStyle::default_bar()
            .template("[{elapsed_precise}] {bar:40.cyan/blue} {pos:>7}/{len:7} {msg}")
            .unwrap()
            .progress_chars("##-")
    );
    
    for _ in 0..1024 {
        pb.inc(1);
        thread::sleep(Duration::from_millis(5));
    }
    pb.finish_with_message("Completed!");
}
```

**运行效果**:

```text
████████████████████████████████████████ 100/100 Done!

[00:00:05] ########################################   1024/1024 Completed!
```

### 高级用法：多进度条

```rust
use indicatif::{MultiProgress, ProgressBar, ProgressStyle};
use std::time::Duration;
use std::thread;

fn main() {
    let m = MultiProgress::new();
    let style = ProgressStyle::default_bar()
        .template("[{elapsed_precise}] {bar:40.cyan/blue} {pos:>7}/{len:7} {msg}")
        .unwrap();
    
    let pb1 = m.add(ProgressBar::new(128));
    pb1.set_style(style.clone());
    pb1.set_message("Task 1");
    
    let pb2 = m.add(ProgressBar::new(256));
    pb2.set_style(style.clone());
    pb2.set_message("Task 2");
    
    let pb3 = m.add(ProgressBar::new(512));
    pb3.set_style(style.clone());
    pb3.set_message("Task 3");
    
    // 模拟并发任务
    let h1 = {
        let pb = pb1.clone();
        thread::spawn(move || {
            for _ in 0..128 {
                pb.inc(1);
                thread::sleep(Duration::from_millis(30));
            }
            pb.finish_with_message("Task 1 done!");
        })
    };
    
    let h2 = {
        let pb = pb2.clone();
        thread::spawn(move || {
            for _ in 0..256 {
                pb.inc(1);
                thread::sleep(Duration::from_millis(20));
            }
            pb.finish_with_message("Task 2 done!");
        })
    };
    
    let h3 = {
        let pb = pb3.clone();
        thread::spawn(move || {
            for _ in 0..512 {
                pb.inc(1);
                thread::sleep(Duration::from_millis(10));
            }
            pb.finish_with_message("Task 3 done!");
        })
    };
    
    h1.join().unwrap();
    h2.join().unwrap();
    h3.join().unwrap();
}
```

**运行效果**:

```text
[00:00:03] ########################################     128/128 Task 1 done!
[00:00:05] ########################################     256/256 Task 2 done!
[00:00:05] ########################################     512/512 Task 3 done!
```

### 自定义样式

```rust
use indicatif::{ProgressBar, ProgressStyle};
use std::time::Duration;

fn main() {
    // Spinner（不确定进度）
    let pb = ProgressBar::new_spinner();
    pb.set_style(
        ProgressStyle::default_spinner()
            .template("{spinner:.green} [{elapsed_precise}] {msg}")
            .unwrap()
    );
    pb.set_message("Loading...");
    
    for _ in 0..50 {
        pb.tick();
        std::thread::sleep(Duration::from_millis(100));
    }
    pb.finish_with_message("Loaded!");
    
    println!("\n");
    
    // 下载进度条（显示速率）
    let pb = ProgressBar::new(1024 * 1024); // 1MB
    pb.set_style(
        ProgressStyle::default_bar()
            .template("[{elapsed_precise}] {bar:40} {bytes}/{total_bytes} ({bytes_per_sec}) {msg}")
            .unwrap()
    );
    
    pb.set_message("Downloading...");
    
    for _ in 0..1024 {
        pb.inc(1024); // 1KB per iteration
        std::thread::sleep(Duration::from_millis(10));
    }
    pb.finish_with_message("Download complete!");
}
```

**运行效果**:

```text
⠋ [00:00:05] Loading...
⠙ [00:00:05] Loaded!

[00:00:10] ████████████████████ 1024.00 KiB/1024.00 KiB (102.40 KiB/s) Download complete!
```

---

## console - 终端控制

### 核心特性3

- ✅ **跨平台**: Windows、macOS、Linux
- ✅ **颜色输出**: ANSI 颜色支持
- ✅ **终端检测**: 判断是否为 TTY
- ✅ **输入处理**: 读取按键
- ✅ **终端操作**: 清屏、光标移动

**安装**:

```toml
[dependencies]
console = "0.15"
```

### 颜色输出

```rust
use console::style;

fn main() {
    // 基础颜色
    println!("{}", style("Red text").red());
    println!("{}", style("Green text").green());
    println!("{}", style("Blue text").blue());
    
    // 背景色
    println!("{}", style("Red background").on_red());
    
    // 组合样式
    println!("{}", style("Bold red").red().bold());
    println!("{}", style("Underline green").green().underlined());
    
    // 自定义颜色
    println!("{}", style("Custom color").color256(208)); // Orange
    
    // 条件样式
    let is_error = true;
    println!("{}", 
        style("Message")
            .color256(if is_error { 9 } else { 10 })
    );
}
```

### 终端操作

```rust
use console::{Term, Key};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let term = Term::stdout();
    
    // 清屏
    term.clear_screen()?;
    
    // 写入并刷新
    term.write_line("Press any key...")?;
    
    // 读取按键
    let key = term.read_key()?;
    match key {
        Key::Char('q') => {
            term.write_line("Quitting...")?;
        }
        Key::Enter => {
            term.write_line("Enter pressed")?;
        }
        Key::ArrowUp => {
            term.write_line("Up arrow")?;
        }
        _ => {
            term.write_line(&format!("Key: {:?}", key))?;
        }
    }
    
    Ok(())
}
```

---

## 实战场景

### 场景1: 文件处理工具

**需求描述**: 创建一个批量文件处理工具，支持多线程、进度显示、详细日志。

**完整实现**:

```rust
use clap::Parser;
use indicatif::{ProgressBar, ProgressStyle};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

#[derive(Parser)]
#[command(author, version, about = "Batch file processor")]
struct Cli {
    /// Input directory
    #[arg(short, long)]
    input: PathBuf,
    
    /// Output directory
    #[arg(short, long)]
    output: PathBuf,
    
    /// File extension filter
    #[arg(short, long, default_value = "txt")]
    ext: String,
    
    /// Verbose output
    #[arg(short, long)]
    verbose: bool,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    
    // 检查输入目录
    if !cli.input.exists() {
        eprintln!("Error: Input directory does not exist");
        std::process::exit(1);
    }
    
    // 创建输出目录
    fs::create_dir_all(&cli.output)?;
    
    // 收集文件
    let files: Vec<PathBuf> = fs::read_dir(&cli.input)?
        .filter_map(|entry| entry.ok())
        .map(|entry| entry.path())
        .filter(|path| {
            path.extension()
                .and_then(|ext| ext.to_str())
                .map(|ext| ext == cli.ext)
                .unwrap_or(false)
        })
        .collect();
    
    if files.is_empty() {
        println!("No files found with extension .{}", cli.ext);
        return Ok(());
    }
    
    println!("Found {} files to process", files.len());
    
    // 创建进度条
    let pb = ProgressBar::new(files.len() as u64);
    pb.set_style(
        ProgressStyle::default_bar()
            .template("[{elapsed_precise}] {bar:40.cyan/blue} {pos}/{len} {msg}")
            .unwrap()
    );
    
    // 处理文件
    for file in &files {
        let file_name = file.file_name().unwrap().to_str().unwrap();
        
        if cli.verbose {
            pb.set_message(format!("Processing: {}", file_name));
        }
        
        // 模拟处理
        process_file(file, &cli.output)?;
        
        pb.inc(1);
        std::thread::sleep(Duration::from_millis(100));
    }
    
    pb.finish_with_message("All files processed!");
    
    println!("\nProcessed {} files", files.len());
    println!("Output directory: {}", cli.output.display());
    
    Ok(())
}

fn process_file(input: &Path, output_dir: &Path) -> Result<(), Box<dyn std::error::Error>> {
    let content = fs::read_to_string(input)?;
    
    // 简单处理：转大写
    let processed = content.to_uppercase();
    
    let output_path = output_dir.join(input.file_name().unwrap());
    fs::write(output_path, processed)?;
    
    Ok(())
}
```

**运行效果**:

```bash
$ file-processor -i ./input -o ./output -e txt -v
Found 10 files to process
[00:00:01] ████████████████████████ 10/10 All files processed!

Processed 10 files
Output directory: ./output
```

### 场景2: 交互式配置生成器

**需求描述**: 创建一个交互式工具，引导用户生成配置文件。

**完整实现**:

```rust
use dialoguer::{Input, Select, Confirm, MultiSelect, theme::ColorfulTheme};
use serde::{Serialize, Deserialize};
use std::fs;

#[derive(Serialize, Deserialize)]
struct Config {
    project_name: String,
    language: String,
    features: Vec<String>,
    database: Option<String>,
    enable_ci: bool,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("🚀 Interactive Project Configuration\n");
    
    let theme = ColorfulTheme::default();
    
    // 项目名称
    let project_name: String = Input::with_theme(&theme)
        .with_prompt("Project name")
        .validate_with(|input: &String| -> Result<(), &str> {
            if input.is_empty() {
                Err("Project name cannot be empty")
            } else {
                Ok(())
            }
        })
        .interact_text()?;
    
    // 编程语言
    let languages = vec!["Rust", "Python", "JavaScript", "Go"];
    let lang_idx = Select::with_theme(&theme)
        .with_prompt("Programming language")
        .items(&languages)
        .default(0)
        .interact()?;
    let language = languages[lang_idx].to_string();
    
    // 功能选择
    let feature_options = vec![
        "Web API",
        "CLI Tool",
        "Database Integration",
        "Caching",
        "Authentication",
    ];
    let feature_selections = MultiSelect::with_theme(&theme)
        .with_prompt("Select features (space to select, enter to confirm)")
        .items(&feature_options)
        .interact()?;
    
    let features: Vec<String> = feature_selections
        .iter()
        .map(|&i| feature_options[i].to_string())
        .collect();
    
    // 数据库选择（条件性）
    let database = if features.contains(&"Database Integration".to_string()) {
        let db_options = vec!["PostgreSQL", "MySQL", "SQLite", "None"];
        let db_idx = Select::with_theme(&theme)
            .with_prompt("Database type")
            .items(&db_options)
            .default(0)
            .interact()?;
        
        if db_options[db_idx] != "None" {
            Some(db_options[db_idx].to_string())
        } else {
            None
        }
    } else {
        None
    };
    
    // CI/CD
    let enable_ci = Confirm::with_theme(&theme)
        .with_prompt("Enable CI/CD?")
        .default(true)
        .interact()?;
    
    // 生成配置
    let config = Config {
        project_name: project_name.clone(),
        language,
        features,
        database,
        enable_ci,
    };
    
    // 显示摘要
    println!("\n📋 Configuration Summary:");
    println!("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━");
    println!("Project: {}", config.project_name);
    println!("Language: {}", config.language);
    println!("Features: {}", config.features.join(", "));
    if let Some(db) = &config.database {
        println!("Database: {}", db);
    }
    println!("CI/CD: {}", if config.enable_ci { "✓" } else { "✗" });
    
    // 确认保存
    let save = Confirm::with_theme(&theme)
        .with_prompt("Save configuration?")
        .default(true)
        .interact()?;
    
    if save {
        let config_json = serde_json::to_string_pretty(&config)?;
        let filename = format!("{}_config.json", config.project_name);
        fs::write(&filename, config_json)?;
        println!("\n✅ Configuration saved to: {}", filename);
    } else {
        println!("\n❌ Configuration not saved");
    }
    
    Ok(())
}
```

**运行效果**:

```text
🚀 Interactive Project Configuration

? Project name: my-awesome-app
? Programming language
> Rust
  Python
  JavaScript
  Go

? Select features (space to select, enter to confirm)
  [x] Web API
  [ ] CLI Tool
  [x] Database Integration
  [x] Caching
  [ ] Authentication

? Database type
> PostgreSQL
  MySQL
  SQLite
  None

? Enable CI/CD? (Y/n) y

📋 Configuration Summary:
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
Project: my-awesome-app
Language: Rust
Features: Web API, Database Integration, Caching
Database: PostgreSQL
CI/CD: ✓

? Save configuration? (Y/n) y

✅ Configuration saved to: my-awesome-app_config.json
```

### 场景3: 下载管理器

**需求描述**: 创建一个支持多线程下载、实时进度显示的下载管理器。

**完整实现**:

```rust
use clap::Parser;
use indicatif::{MultiProgress, ProgressBar, ProgressStyle};
use std::time::Duration;
use std::thread;

#[derive(Parser)]
#[command(author, version, about = "Download manager")]
struct Cli {
    /// URLs to download
    #[arg(short, long, num_args = 1..)]
    urls: Vec<String>,
    
    /// Number of concurrent downloads
    #[arg(short = 'j', long, default_value_t = 3)]
    jobs: usize,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    
    if cli.urls.is_empty() {
        eprintln!("Error: No URLs provided");
        std::process::exit(1);
    }
    
    println!("Starting {} downloads with {} concurrent jobs\n", 
        cli.urls.len(), cli.jobs);
    
    let m = MultiProgress::new();
    let style = ProgressStyle::default_bar()
        .template("[{elapsed_precise}] {bar:40.cyan/blue} {bytes}/{total_bytes} ({bytes_per_sec}) {msg}")
        .unwrap();
    
    let mut handles = vec![];
    
    for (i, url) in cli.urls.iter().enumerate() {
        let pb = m.add(ProgressBar::new(1024 * 1024)); // 1MB
        pb.set_style(style.clone());
        pb.set_message(format!("File {}", i + 1));
        
        let url = url.clone();
        let handle = thread::spawn(move || {
            download_file(&url, pb);
        });
        
        handles.push(handle);
        
        // 限制并发
        if handles.len() >= cli.jobs {
            for h in handles.drain(..) {
                h.join().unwrap();
            }
        }
    }
    
    // 等待剩余任务
    for h in handles {
        h.join().unwrap();
    }
    
    println!("\n✅ All downloads completed!");
    
    Ok(())
}

fn download_file(url: &str, pb: ProgressBar) {
    // 模拟下载
    let total_size = 1024 * 1024; // 1MB
    let chunk_size = 1024; // 1KB
    
    pb.set_length(total_size);
    
    for _ in 0..(total_size / chunk_size) {
        pb.inc(chunk_size);
        thread::sleep(Duration::from_millis(10));
    }
    
    pb.finish_with_message(format!("Downloaded: {}", url));
}
```

**运行效果**:

```bash
$ downloader -u https://example.com/file1.zip https://example.com/file2.zip -j 2
Starting 2 downloads with 2 concurrent jobs

[00:00:10] ████████████████████ 1.00 MiB/1.00 MiB (102.40 KiB/s) Downloaded: https://example.com/file1.zip
[00:00:10] ████████████████████ 1.00 MiB/1.00 MiB (102.40 KiB/s) Downloaded: https://example.com/file2.zip

✅ All downloads completed!
```

---

## 最佳实践

### 1. 提供详细的帮助信息

**描述**: 清晰的帮助文档是好 CLI 的标志。

```rust
#[derive(Parser)]
#[command(
    name = "myapp",
    version = "1.0.0",
    author = "Your Name <you@example.com>",
    about = "Does awesome things",
    long_about = "A longer description that explains what the tool does in detail.\n\n\
                  This can span multiple lines and provide examples."
)]
struct Cli {
    /// Input file to process
    /// 
    /// The input file should be in JSON format.
    /// Example: input.json
    #[arg(short, long, value_name = "FILE")]
    input: String,
}
```

### 2. 错误处理友好

**描述**: 提供清晰的错误信息和建议。

```rust
use std::fs;
use std::path::Path;

fn process_file(path: &Path) -> Result<(), String> {
    if !path.exists() {
        return Err(format!(
            "File not found: {}\n\nHint: Check if the file path is correct.",
            path.display()
        ));
    }
    
    let content = fs::read_to_string(path)
        .map_err(|e| format!("Failed to read file: {}", e))?;
    
    // 处理内容
    Ok(())
}
```

### 3. 使用颜色突出重要信息

**描述**: 颜色可以提高可读性。

```rust
use console::style;

fn print_status(success: bool, message: &str) {
    if success {
        println!("{} {}", style("✓").green().bold(), message);
    } else {
        println!("{} {}", style("✗").red().bold(), message);
    }
}

// 使用
print_status(true, "File processed successfully");
print_status(false, "Failed to process file");
```

### 4. 长时间操作显示进度

**描述**: 避免用户等待焦虑。

```rust
use indicatif::{ProgressBar, ProgressStyle};

fn process_large_dataset(items: &[String]) {
    let pb = ProgressBar::new(items.len() as u64);
    pb.set_style(ProgressStyle::default_bar());
    
    for item in items {
        // 处理
        pb.inc(1);
    }
    
    pb.finish_with_message("Done!");
}
```

### 5. 支持管道和重定向

**描述**: 检测输出目标，适配格式。

```rust
use console::Term;

fn main() {
    let term = Term::stdout();
    
    if term.is_term() {
        // 输出到终端：使用颜色和进度条
        println!("{}", console::style("Colored output").green());
    } else {
        // 输出到文件/管道：纯文本
        println!("Plain text output");
    }
}
```

---

## 常见陷阱

### ⚠️ 陷阱1: 忘记处理 Ctrl+C

**问题描述**: 长时间运行的程序应该优雅退出。

❌ **错误示例**:

```rust
fn main() {
    loop {
        // 长时间运行
        std::thread::sleep(Duration::from_secs(1));
    }
    // 无法优雅退出
}
```

✅ **正确做法**:

```rust
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

fn main() {
    let running = Arc::new(AtomicBool::new(true));
    let r = running.clone();
    
    ctrlc::set_handler(move || {
        r.store(false, Ordering::SeqCst);
        println!("\nShutting down gracefully...");
    }).expect("Error setting Ctrl-C handler");
    
    while running.load(Ordering::SeqCst) {
        // 工作
        std::thread::sleep(Duration::from_secs(1));
    }
    
    println!("Cleanup complete");
}
```

### ⚠️ 陷阱2: 进度条更新过于频繁

**问题描述**: 频繁更新进度条影响性能。

❌ **错误示例**:

```rust
let pb = ProgressBar::new(1_000_000);
for i in 0..1_000_000 {
    pb.set_position(i); // 每次都更新
    // 处理
}
```

✅ **正确做法**:

```rust
let pb = ProgressBar::new(1_000_000);
let update_interval = 1000;

for i in 0..1_000_000 {
    if i % update_interval == 0 {
        pb.set_position(i); // 每1000次更新一次
    }
    // 处理
}
pb.finish();
```

### ⚠️ 陷阱3: 不检查终端类型

**问题描述**: 在非 TTY 环境使用交互功能。

❌ **错误示例**:

```rust
// 在管道中运行会失败
let name: String = Input::new()
    .with_prompt("Name")
    .interact_text()
    .unwrap();
```

✅ **正确做法**:

```rust
use console::Term;

let term = Term::stdout();

let name = if term.is_term() {
    Input::new()
        .with_prompt("Name")
        .interact_text()
        .unwrap()
} else {
    // 从标准输入读取
    let mut input = String::new();
    std::io::stdin().read_line(&mut input).unwrap();
    input.trim().to_string()
};
```

### ⚠️ 陷阱4: 硬编码颜色

**问题描述**: 不支持 NO_COLOR 环境变量。

❌ **错误示例**:

```rust
println!("\x1b[31mError\x1b[0m"); // 硬编码 ANSI 颜色
```

✅ **正确做法**:

```rust
use console::style;

// console 库自动检测 NO_COLOR 环境变量
println!("{}", style("Error").red());
```

---

## 参考资源

### 官方文档

- 📚 [clap 文档](https://docs.rs/clap/latest/clap/)
- 📚 [dialoguer 文档](https://docs.rs/dialoguer/latest/dialoguer/)
- 📚 [indicatif 文档](https://docs.rs/indicatif/latest/indicatif/)
- 📚 [console 文档](https://docs.rs/console/latest/console/)

### 教程与文章

- 📖 [Command Line Applications in Rust](https://rust-cli.github.io/book/)
- 📖 [12 Factor CLI Apps](https://medium.com/@jdxcode/12-factor-cli-apps-dd3c227a0e46)
- 📖 [Unix 命令行艺术](https://github.com/jlevy/the-art-of-command-line)

### 示例项目

- 💻 [ripgrep](https://github.com/BurntSushi/ripgrep) - 快速搜索工具
- 💻 [fd](https://github.com/sharkdp/fd) - 现代文件查找
- 💻 [bat](https://github.com/sharkdp/bat) - 带语法高亮的 cat
- 💻 [exa](https://github.com/ogham/exa) - 现代 ls 替代

### 相关文档

- 🔗 [测试工具](../testing/README.md)
- 🔗 [日志系统](../../05_toolchain/logging/README.md)
- 🔗 [错误处理](../../02_system_programming/error_handling/README.md)

---

**文档版本**: 2.0.0  
**最后更新**: 2025-10-20  
**维护者**: Rust 学习社区
