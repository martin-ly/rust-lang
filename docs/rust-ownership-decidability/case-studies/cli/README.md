# Rust CLI 工具开发完整指南

> 从零开始构建高性能、跨平台的命令行工具

---

## 目录

- [Rust CLI 工具开发完整指南](#rust-cli-工具开发完整指南)
  - [目录](#目录)
  - [1. CLI 工具概述](#1-cli-工具概述)
    - [1.1 Rust 在 CLI 领域的优势](#11-rust-在-cli-领域的优势)
      - [**零成本抽象**](#零成本抽象)
      - [**内存安全与可靠性**](#内存安全与可靠性)
      - [**快速启动时间**](#快速启动时间)
      - [**小巧的二进制体积**](#小巧的二进制体积)
      - [**跨平台能力**](#跨平台能力)
    - [1.2 现有知名工具](#12-现有知名工具)
      - [**ripgrep (rg)**](#ripgrep-rg)
      - [**fd**](#fd)
      - [**exa (现为 eza)**](#exa-现为-eza)
      - [**bat**](#bat)
      - [**starship**](#starship)
      - [**tokei**](#tokei)
    - [1.3 性能与可靠性](#13-性能与可靠性)
      - [**性能优化策略**](#性能优化策略)
      - [**可靠性保证**](#可靠性保证)
  - [2. 参数解析](#2-参数解析)
    - [2.1 clap 库详解](#21-clap-库详解)
      - [**基础使用**](#基础使用)
    - [2.2 派生宏使用](#22-派生宏使用)
      - [**基本字段属性**](#基本字段属性)
      - [**自定义类型解析**](#自定义类型解析)
    - [2.3 子命令](#23-子命令)
    - [2.4 验证和默认值](#24-验证和默认值)
      - [**值验证**](#值验证)
      - [**复杂默认值**](#复杂默认值)
  - [3. 终端交互](#3-终端交互)
    - [3.1 crossterm 跨平台](#31-crossterm-跨平台)
      - [**基本终端操作**](#基本终端操作)
      - [**终端尺寸检测**](#终端尺寸检测)
    - [3.2 终端 UI（ratatui）](#32-终端-uiratatui)
    - [3.3 进度条（indicatif）](#33-进度条indicatif)
    - [3.4 彩色输出](#34-彩色输出)
      - [**ansi\_term（已归档）**](#ansi_term已归档)
      - [**检测终端能力**](#检测终端能力)
  - [4. 文件系统操作](#4-文件系统操作)
    - [4.1 高效遍历（walkdir、ignore）](#41-高效遍历walkdirignore)
      - [**walkdir**](#walkdir)
      - [**ignore（ripgrep 使用的库）**](#ignoreripgrep-使用的库)
    - [4.2 符号链接处理](#42-符号链接处理)
    - [4.3 权限管理](#43-权限管理)
    - [4.4 跨平台路径](#44-跨平台路径)
  - [5. 配置管理](#5-配置管理)
    - [5.1 配置文件格式（TOML、YAML、JSON）](#51-配置文件格式tomlyamljson)
      - [**TOML**](#toml)
      - [**YAML**](#yaml)
      - [**JSON**](#json)
    - [5.2 环境变量](#52-环境变量)
    - [5.3 XDG 规范](#53-xdg-规范)
    - [5.4 配置验证](#54-配置验证)
  - [6. 错误处理](#6-错误处理)
    - [6.1 anyhow/eyre](#61-anyhoweyre)
      - [**anyhow 基础使用**](#anyhow-基础使用)
      - [**自定义错误类型（与 anyhow 结合）**](#自定义错误类型与-anyhow-结合)
    - [6.2 人性化的错误信息](#62-人性化的错误信息)
    - [6.3 错误链](#63-错误链)
    - [6.4 退出码](#64-退出码)
  - [7. 日志与输出](#7-日志与输出)
    - [7.1 tracing 日志](#71-tracing-日志)
      - [**自定义日志输出格式**](#自定义日志输出格式)
    - [7.2 结构化输出](#72-结构化输出)
    - [7.3 日志级别](#73-日志级别)
    - [7.4 输出重定向](#74-输出重定向)
  - [8. 完整示例：文件搜索工具](#8-完整示例文件搜索工具)
  - [9. 打包与分发](#9-打包与分发)
    - [9.1 cargo-install](#91-cargo-install)
    - [9.2 静态链接](#92-静态链接)
      - [**Linux 静态链接（musl）**](#linux-静态链接musl)
      - [**Windows 静态链接**](#windows-静态链接)
      - [**macOS 静态链接**](#macos-静态链接)
    - [9.3 多平台构建](#93-多平台构建)
      - [**使用 cross 工具**](#使用-cross-工具)
      - [**GitHub Actions 自动构建**](#github-actions-自动构建)
    - [9.4 包管理器](#94-包管理器)
      - [**Homebrew（macOS/Linux）**](#homebrewmacoslinux)
      - [**Scoop（Windows）**](#scoopwindows)
      - [**AUR（Arch Linux）**](#aurarch-linux)
      - [**Cargo Binstall**](#cargo-binstall)
  - [10. Shell 集成](#10-shell-集成)
    - [10.1 自动补全（bash/zsh/fish）](#101-自动补全bashzshfish)
      - [**安装补全脚本**](#安装补全脚本)
    - [10.2 man page 生成](#102-man-page-生成)
      - [**man page 安装**](#man-page-安装)
    - [10.3 别名支持](#103-别名支持)
      - [**Shell 别名配置**](#shell-别名配置)
  - [附录：推荐 crates](#附录推荐-crates)
  - [总结](#总结)

---

## 1. CLI 工具概述

### 1.1 Rust 在 CLI 领域的优势

Rust 已成为构建命令行工具的首选语言之一，这并非偶然。以下是 Rust 在 CLI 开发中的核心优势：

#### **零成本抽象**

Rust 的抽象机制不会带来运行时开销。这意味着你可以编写高层次的、富有表现力的代码，同时获得与手写底层代码相当的性能。

```rust
// 高层次的迭代器链，编译为高效的机器码
let total_size: u64 = entries
    .iter()
    .filter(|e| e.is_file())
    .map(|e| e.metadata().map(|m| m.len()).unwrap_or(0))
    .sum();
```

#### **内存安全与可靠性**

Rust 的所有权系统在编译时消除内存错误，防止段错误、野指针和数据竞争。对于长时间运行的 CLI 工具，这意味着：

- 不会因内存泄漏而逐渐变慢
- 不会因使用未初始化内存而产生未定义行为
- 并发代码是安全的，无需担心数据竞争

#### **快速启动时间**

与需要虚拟机或运行时的语言不同，Rust 编译为本地机器码，启动时间极短：

| 工具 | 语言 | 冷启动时间 |
|------|------|-----------|
| ripgrep | Rust | ~10ms |
| ag (The Silver Searcher) | C | ~15ms |
| ack | Perl | ~100ms |

#### **小巧的二进制体积**

通过适当的编译选项，可以生成极小的二进制文件：

```bash
# 优化发布构建
cargo build --release

# 进一步优化二进制大小
RUSTFLAGS="-C opt-level=z -C lto=fat -C codegen-units=1" cargo build --release
```

#### **跨平台能力**

Rust 支持所有主流平台，包括 Windows、macOS、Linux，以及多种架构（x86_64、ARM、RISC-V 等）。

### 1.2 现有知名工具

Rust 生态系统中已经涌现了许多优秀的 CLI 工具，它们展示了 Rust 在实践中的威力：

#### **ripgrep (rg)**

极速的递归搜索工具，旨在替代 `grep`。

```bash
# 安装
cargo install ripgrep

# 使用：在当前目录递归搜索 "TODO"
rg TODO

# 搜索特定文件类型
rg "async fn" --type rust

# 显示统计信息
rg "pattern" --stats
```

**性能特点：**

- 默认忽略 `.gitignore` 中的文件和隐藏文件
- 支持并行搜索，充分利用多核 CPU
- 使用内存映射加速大文件搜索
- 基于 Rust 的正则表达式引擎 (regex crate)，性能卓越

#### **fd**

用户友好的 `find` 替代品。

```bash
# 安装
cargo install fd-find

# 查找所有 Rust 文件
fd "\.rs$"

# 查找并执行操作
fd "\.tmp$" -x rm {}

# 智能大小写搜索
fd readme
```

**特性：**

- 直观的语法（默认递归，无需指定路径）
- 支持正则表达式和 glob 模式
- 彩色输出
- 并行目录遍历

#### **exa (现为 eza)**

现代化的 `ls` 替代品。

```bash
# 安装
cargo install eza

# 显示 git 状态
eza --long --git

# 树状显示
eza --tree --level=2

# 图标支持
eza --icons
```

#### **bat**

带语法高亮的 `cat` 替代品。

```bash
# 安装
cargo install bat

# 查看文件（带语法高亮和行号）
bat src/main.rs

# 显示非打印字符
bat -A file.txt

# 指定主题
bat --theme="TwoDark" file.rs
```

#### **starship**

跨平台的极简 Shell 提示符。

```bash
# 安装
cargo install starship

# 评估提示符配置
eval "$(starship init bash)"
```

#### **tokei**

快速统计代码行数。

```bash
cargo install tokei
tokei
```

### 1.3 性能与可靠性

#### **性能优化策略**

Rust CLI 工具常用的性能优化技术：

```rust
use rayon::prelude::*;

// 并行处理文件
fn process_files_parallel(files: &[PathBuf]) -> Vec<Result<()>> {
    files
        .par_iter()  // 使用 Rayon 的并行迭代器
        .map(|file| process_file(file))
        .collect()
}

// 内存映射大文件
use memmap2::Mmap;

fn search_in_large_file(path: &Path, pattern: &str) -> io::Result<Vec<usize>> {
    let file = File::open(path)?;
    let mmap = unsafe { Mmap::map(&file)? };

    // 直接在内存映射上搜索，避免大内存分配
    Ok(memchr::memmem::find_iter(&mmap, pattern.as_bytes()).collect())
}
```

#### **可靠性保证**

Rust 的类型系统和错误处理机制确保 CLI 工具的健壮性：

```rust
use std::process;

fn main() {
    if let Err(e) = run() {
        eprintln!("Error: {}", e);

        // 根据错误类型返回不同的退出码
        let exit_code = match e.downcast_ref::<std::io::Error>() {
            Some(io_err) if io_err.kind() == std::io::ErrorKind::NotFound => 2,
            Some(io_err) if io_err.kind() == std::io::ErrorKind::PermissionDenied => 3,
            _ => 1,
        };

        process::exit(exit_code);
    }
}
```

---

## 2. 参数解析

### 2.1 clap 库详解

[clap](https://github.com/clap-rs/clap) 是 Rust 生态中最流行的命令行参数解析库。它提供了强大而灵活的 API，支持多种使用模式。

#### **基础使用**

```toml
# Cargo.toml
[dependencies]
clap = { version = "4.5", features = ["derive", "env", "cargo"] }
```

```rust
use clap::{Parser, Subcommand, ValueEnum};

#[derive(Parser)]
#[command(
    name = "myapp",
    version = "1.0.0",
    author = "Your Name <your.email@example.com>",
    about = "A powerful CLI tool",
    long_about = "This is a longer description of the tool..."
)]
struct Cli {
    /// 要处理的输入文件
    #[arg(short, long, value_name = "FILE")]
    input: PathBuf,

    /// 输出文件路径
    #[arg(short, long, default_value = "output.txt")]
    output: PathBuf,

    /// 详细输出模式
    #[arg(short, long, action = clap::ArgAction::Count)]
    verbose: u8,

    /// 线程数量
    #[arg(short, long, env = "MYAPP_THREADS", default_value_t = 4)]
    threads: usize,
}

fn main() {
    let cli = Cli::parse();

    println!("Input: {:?}", cli.input);
    println!("Output: {:?}", cli.output);
    println!("Verbosity level: {}", cli.verbose);
    println!("Threads: {}", cli.threads);
}
```

### 2.2 派生宏使用

clap 的派生宏 (derive macros) 提供了声明式的参数定义方式：

#### **基本字段属性**

```rust
use clap::Parser;
use std::path::PathBuf;

#[derive(Parser, Debug)]
struct Args {
    /// 位置参数（必需）
    target: String,

    /// 短参数和长参数
    #[arg(short = 'c', long = "config")]
    config_file: Option<PathBuf>,

    /// 多值参数
    #[arg(short, long, num_args = 1..)]
    include: Vec<String>,

    /// 布尔标志
    #[arg(long)]
    dry_run: bool,

    /// 带默认值的参数
    #[arg(long, default_value_t = 8080)]
    port: u16,

    /// 环境变量支持
    #[arg(long, env = "API_KEY")]
    api_key: String,

    /// 隐藏参数（不在帮助中显示）
    #[arg(long, hide = true)]
    debug_mode: bool,

    /// 互斥组
    #[arg(long, group = "format")]
    json: bool,

    #[arg(long, group = "format")]
    yaml: bool,

    /// 条件要求
    #[arg(long, requires = "api_key")]
    upload: bool,
}
```

#### **自定义类型解析**

```rust
use clap::Parser;
use std::str::FromStr;

#[derive(Debug, Clone)]
struct ByteSize(u64);

impl FromStr for ByteSize {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let num: u64 = s
            .trim_end_matches(|c: char| c.is_alphabetic())
            .parse()
            .map_err(|_| format!("Invalid number: {}", s))?;

        let multiplier = match s.chars().last() {
            Some('K') | Some('k') => 1024,
            Some('M') | Some('m') => 1024 * 1024,
            Some('G') | Some('g') => 1024 * 1024 * 1024,
            Some(c) if c.is_ascii_digit() => 1,
            _ => return Err(format!("Invalid suffix in: {}", s)),
        };

        Ok(ByteSize(num * multiplier))
    }
}

#[derive(Parser)]
struct Args {
    /// 最大文件大小（支持 K, M, G 后缀）
    #[arg(short, long, default_value = "10M")]
    max_size: ByteSize,
}
```

### 2.3 子命令

复杂的 CLI 工具通常需要子命令来组织功能：

```rust
use clap::{Parser, Subcommand};
use std::path::PathBuf;

#[derive(Parser)]
#[command(name = "git-clone")]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    /// 全局选项：配置文件路径
    #[arg(short, long, global = true)]
    config: Option<PathBuf>,
}

#[derive(Subcommand)]
enum Commands {
    /// 添加文件到暂存区
    Add {
        /// 文件路径
        paths: Vec<PathBuf>,

        /// 交互式添加
        #[arg(short, long)]
        interactive: bool,

        /// 更新已跟踪文件
        #[arg(short, long)]
        update: bool,
    },

    /// 提交更改
    Commit {
        /// 提交信息
        #[arg(short, long)]
        message: String,

        /// 修改上次提交
        #[arg(short, long)]
        amend: bool,

        /// 允许空提交
        #[arg(long)]
        allow_empty: bool,
    },

    /// 推送更改
    Push {
        /// 远程仓库名
        remote: Option<String>,

        /// 分支名
        branch: Option<String>,

        /// 强制推送
        #[arg(short, long)]
        force: bool,

        /// 设置上游分支
        #[arg(short, long)]
        set_upstream: bool,
    },
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Commands::Add { paths, interactive, update } => {
            println!("Adding files: {:?}", paths);
            println!("Interactive: {}, Update: {}", interactive, update);
        }
        Commands::Commit { message, amend, allow_empty } => {
            println!("Committing with message: {}", message);
        }
        Commands::Push { remote, branch, force, set_upstream } => {
            println!("Pushing to: {:?}/{:?}", remote, branch);
        }
    }
}
```

### 2.4 验证和默认值

#### **值验证**

```rust
use clap::{Parser, builder::PossibleValuesParser};

#[derive(Parser)]
struct Args {
    /// 日志级别（只能是特定值之一）
    #[arg(
        short,
        long,
        default_value = "info",
        value_parser = PossibleValuesParser::new(["trace", "debug", "info", "warn", "error"])
    )]
    log_level: String,

    /// 端口号（范围验证）
    #[arg(short, long, value_parser = clap::value_parser!(u16).range(1024..=65535))]
    port: u16,

    /// 超时时间（秒）
    #[arg(long, value_parser = parse_duration)]
    timeout: std::time::Duration,
}

fn parse_duration(s: &str) -> Result<std::time::Duration, String> {
    let secs: u64 = s.parse().map_err(|_| format!("`{}` isn't a valid number", s))?;
    Ok(std::time::Duration::from_secs(secs))
}
```

#### **复杂默认值**

```rust
use clap::Parser;
use std::path::PathBuf;

fn default_config_path() -> PathBuf {
    dirs::config_dir()
        .map(|d| d.join("myapp").join("config.toml"))
        .unwrap_or_else(|| PathBuf::from("config.toml"))
}

#[derive(Parser)]
struct Args {
    /// 配置文件路径
    #[arg(short, long, default_value_os_t = default_config_path())]
    config: PathBuf,

    /// 工作目录（默认为当前目录）
    #[arg(long, default_value = std::env::current_dir().unwrap().into_os_string())]
    work_dir: PathBuf,
}
```

---

## 3. 终端交互

### 3.1 crossterm 跨平台

[crossterm](https://github.com/crossterm-rs/crossterm) 是一个纯 Rust 实现的跨平台终端操作库。

#### **基本终端操作**

```toml
# Cargo.toml
[dependencies]
crossterm = "0.27"
```

```rust
use crossterm::{
    cursor,
    event::{self, Event, KeyCode, KeyEventKind},
    style::{self, Color, Print, ResetColor, SetForegroundColor},
    terminal::{self, ClearType},
    ExecutableCommand, QueueableCommand,
};
use std::io::{self, stdout, Write};

fn main() -> io::Result<()> {
    let mut stdout = stdout();

    // 启用原始模式（禁用行缓冲和回显）
    terminal::enable_raw_mode()?;

    // 清屏
    stdout.execute(terminal::Clear(ClearType::All))?;

    // 移动光标并设置颜色
    stdout
        .queue(cursor::MoveTo(5, 5))?
        .queue(SetForegroundColor(Color::Cyan))?
        .queue(Print("Hello, Crossterm!"))?
        .queue(ResetColor)?
        .queue(cursor::MoveToNextLine(2))?
        .queue(Print("Press 'q' to quit..."))?
        .flush()?;

    // 事件循环
    loop {
        if let Event::Key(key_event) = event::read()? {
            if key_event.kind == KeyEventKind::Press {
                match key_event.code {
                    KeyCode::Char('q') => break,
                    KeyCode::Char(c) => {
                        stdout
                            .queue(cursor::MoveTo(0, 10))?
                            .queue(terminal::Clear(ClearType::CurrentLine))?
                            .queue(Print(format!("You pressed: {}", c)))?
                            .flush()?;
                    }
                    _ => {}
                }
            }
        }
    }

    // 恢复终端状态
    terminal::disable_raw_mode()?;

    Ok(())
}
```

#### **终端尺寸检测**

```rust
use crossterm::terminal;

fn get_terminal_info() -> io::Result<()> {
    let (cols, rows) = terminal::size()?;
    println!("Terminal size: {} columns x {} rows", cols, rows);

    // 检查终端功能
    println!("Supports colors: {}", supports_color());

    Ok(())
}

fn supports_color() -> bool {
    terminal::supports_color(terminal::Color::Red).unwrap_or(false)
}
```

### 3.2 终端 UI（ratatui）

[ratatui](https://github.com/ratatui-org/ratatui) 是一个用于构建富文本终端用户界面的库（原 tui-rs 的分支）。

```toml
# Cargo.toml
[dependencies]
ratatui = "0.25"
crossterm = "0.27"
```

```rust
use crossterm::{
    event::{self, DisableMouseCapture, EnableMouseCapture, Event, KeyCode},
    execute,
    terminal::{disable_raw_mode, enable_raw_mode, EnterAlternateScreen, LeaveAlternateScreen},
};
use ratatui::{
    backend::{Backend, CrosstermBackend},
    layout::{Alignment, Constraint, Direction, Layout},
    style::{Color, Modifier, Style},
    text::{Line, Span, Text},
    widgets::{Block, Borders, List, ListItem, Paragraph, Wrap},
    Frame, Terminal,
};
use std::{error::Error, io};

struct App {
    items: Vec<String>,
    selected: usize,
    input: String,
}

impl App {
    fn new() -> Self {
        Self {
            items: vec![
                "Item 1".to_string(),
                "Item 2".to_string(),
                "Item 3".to_string(),
            ],
            selected: 0,
            input: String::new(),
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    // 设置终端
    enable_raw_mode()?;
    let mut stdout = io::stdout();
    execute!(stdout, EnterAlternateScreen, EnableMouseCapture)?;
    let backend = CrosstermBackend::new(stdout);
    let mut terminal = Terminal::new(backend)?;

    let app = App::new();
    let res = run_app(&mut terminal, app);

    // 恢复终端
    disable_raw_mode()?;
    execute!(
        terminal.backend_mut(),
        LeaveAlternateScreen,
        DisableMouseCapture
    )?;
    terminal.show_cursor()?;

    Ok(())
}

fn run_app<B: Backend>(terminal: &mut Terminal<B>, mut app: App) -> io::Result<()> {
    loop {
        terminal.draw(|f| ui(f, &app))?;

        if let Event::Key(key) = event::read()? {
            match key.code {
                KeyCode::Char('q') => return Ok(()),
                KeyCode::Down => {
                    app.selected = (app.selected + 1) % app.items.len();
                }
                KeyCode::Up => {
                    app.selected = if app.selected == 0 {
                        app.items.len() - 1
                    } else {
                        app.selected - 1
                    };
                }
                KeyCode::Char(c) => app.input.push(c),
                KeyCode::Backspace => {
                    app.input.pop();
                }
                _ => {}
            }
        }
    }
}

fn ui(f: &mut Frame, app: &App) {
    // 创建布局
    let chunks = Layout::default()
        .direction(Direction::Vertical)
        .margin(2)
        .constraints([Constraint::Length(3), Constraint::Min(0)])
        .split(f.size());

    // 输入框
    let input = Paragraph::new(app.input.as_str())
        .style(Style::default().fg(Color::Yellow))
        .block(Block::default().borders(Borders::ALL).title("Input"));
    f.render_widget(input, chunks[0]);

    // 列表
    let items: Vec<ListItem> = app
        .items
        .iter()
        .enumerate()
        .map(|(i, item)| {
            let style = if i == app.selected {
                Style::default()
                    .bg(Color::Blue)
                    .fg(Color::White)
                    .add_modifier(Modifier::BOLD)
            } else {
                Style::default()
            };
            ListItem::new(item.as_str()).style(style)
        })
        .collect();

    let list = List::new(items)
        .block(Block::default().borders(Borders::ALL).title("Items"));
    f.render_widget(list, chunks[1]);
}
```

### 3.3 进度条（indicatif）

[indicatif](https://github.com/console-rs/indicatif) 提供了美观的进度条和旋转指示器。

```toml
# Cargo.toml
[dependencies]
indicatif = "0.17"
```

```rust
use indicatif::{ProgressBar, ProgressStyle, MultiProgress};
use std::thread;
use std::time::Duration;

fn main() {
    // 简单进度条
    simple_progress();

    // 自定义样式的进度条
    styled_progress();

    // 多进度条
    multi_progress();
}

fn simple_progress() {
    let pb = ProgressBar::new(100);

    for i in 0..100 {
        thread::sleep(Duration::from_millis(50));
        pb.set_position(i + 1);
    }

    pb.finish_with_message("Done!");
}

fn styled_progress() {
    let pb = ProgressBar::new(1000);
    pb.set_style(
        ProgressStyle::with_template(
            "[{elapsed_precise}] {bar:40.cyan/blue} {pos:>7}/{len:7} {msg}"
        )
        .unwrap()
        .progress_chars("##-"),
    );

    for i in 0..1000 {
        pb.set_message(format!("Processing item #{}...", i));
        thread::sleep(Duration::from_millis(10));
        pb.inc(1);
    }

    pb.finish_with_message("Complete!");
}

fn multi_progress() {
    let m = MultiProgress::new();
    let sty = ProgressStyle::with_template(
        "{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos:>7}/{len:7} {msg}"
    )
    .unwrap()
    .progress_chars("#>-");

    let pb1 = m.add(ProgressBar::new(100));
    let pb2 = m.add(ProgressBar::new(100));
    let pb3 = m.add(ProgressBar::new(100));

    pb1.set_style(sty.clone());
    pb2.set_style(sty.clone());
    pb3.set_style(sty);

    pb1.set_message("Task 1");
    pb2.set_message("Task 2");
    pb3.set_message("Task 3");

    // 并发处理
    let handles: Vec<_> = vec![pb1, pb2, pb3]
        .into_iter()
        .map(|pb| {
            thread::spawn(move || {
                for _ in 0..100 {
                    thread::sleep(Duration::from_millis(50));
                    pb.inc(1);
                }
                pb.finish_with_message("Done");
            })
        })
        .collect();

    for h in handles {
        h.join().unwrap();
    }
}
```

### 3.4 彩色输出

#### **ansi_term（已归档）**

推荐使用 **owo-colors** 或 **colored**。

```toml
# Cargo.toml
[dependencies]
owo-colors = "4.0"
# 或
colored = "2.1"
```

```rust
// 使用 owo-colors
use owo_colors::OwoColorize;

fn main() {
    // 基本颜色
    println!("{}", "This is blue".blue());
    println!("{}", "This is red".red());
    println!("{}", "This is green".green());

    // 样式
    println!("{}", "Bold text".bold());
    println!("{}", "Underlined".underline());
    println!("{}", "Reversed".on_red());

    // 链式调用
    println!("{}", "Bold red on white".red().bold().on_white());

    // 条件着色
    let success = true;
    println!("{}", "Operation result".if_supports_color(owo_colors::Stream::Stdout, |text| {
        if success { text.green().bold() } else { text.red() }
    }));

    // 自定义 RGB 颜色
    println!("{}", "Custom color".color::<owo_colors::Rgb>(255, 100, 50));
}
```

```rust
// 使用 colored
use colored::Colorize;

fn main() {
    println!("{}", "Hello, World!".red());
    println!("{}", "Hello, World!".on_blue());
    println!("{}", "Hello, World!".bold().italic().underline());

    // 真彩色支持
    println!("{}", "True color".truecolor(255, 128, 64));
}
```

#### **检测终端能力**

```rust
use colored::control;

fn main() {
    // 手动控制颜色输出
    control::set_override(true);  // 强制启用
    control::set_override(false); // 强制禁用

    // 检查是否应该使用颜色（尊重 NO_COLOR 环境变量）
    if control::SHOULD_COLORIZE.should_colorize() {
        println!("{}", "This is colored".red());
    } else {
        println!("This is not colored");
    }
}
```

---

## 4. 文件系统操作

### 4.1 高效遍历（walkdir、ignore）

#### **walkdir**

[walkdir](https://github.com/BurntSushi/walkdir) 提供了递归目录遍历功能。

```toml
# Cargo.toml
[dependencies]
walkdir = "2.4"
```

```rust
use walkdir::WalkDir;
use std::path::Path;

fn main() {
    // 基本遍历
    for entry in WalkDir::new(".") {
        let entry = entry.unwrap();
        println!("{}", entry.path().display());
    }

    // 带深度限制的遍历
    limited_traversal(".", 3);

    // 过滤文件
    find_files_by_extension(".", "rs");
}

fn limited_traversal<P: AsRef<Path>>(path: P, max_depth: usize) {
    for entry in WalkDir::new(path).max_depth(max_depth) {
        let entry = entry.unwrap();
        let depth = entry.depth();
        let indent = "  ".repeat(depth);
        println!("{}{}", indent, entry.file_name().to_string_lossy());
    }
}

fn find_files_by_extension<P: AsRef<Path>>(path: P, ext: &str) {
    let entries: Vec<_> = WalkDir::new(path)
        .into_iter()
        .filter_map(|e| e.ok())
        .filter(|e| {
            e.file_type().is_file()
                && e.path()
                    .extension()
                    .map(|e| e == ext)
                    .unwrap_or(false)
        })
        .collect();

    for entry in entries {
        println!("Found: {}", entry.path().display());
    }
}
```

#### **ignore（ripgrep 使用的库）**

[ignore](https://github.com/BurntSushi/ripgrep/tree/master/crates/ignore) 自动遵循 `.gitignore` 规则。

```toml
# Cargo.toml
[dependencies]
ignore = "0.4"
```

```rust
use ignore::WalkBuilder;

fn main() {
    // 基本使用（自动遵循 .gitignore）
    for result in ignore::Walk::new(".") {
        let entry = result.unwrap();
        println!("{}", entry.path().display());
    }

    // 高级配置
    advanced_walk();
}

fn advanced_walk() {
    let walker = WalkBuilder::new(".")
        .hidden(false)              // 包含隐藏文件
        .ignore(true)               // 遵循 .ignore 文件
        .git_ignore(true)           // 遵循 .gitignore
        .git_global(true)           // 遵循全局 gitignore
        .git_exclude(true)          // 遵循 .git/info/exclude
        .parents(true)              // 读取父目录的 gitignore
        .follow_links(false)        // 不跟随符号链接
        .max_depth(Some(5))         // 最大深度
        .threads(4)                 // 并行线程数
        .build_parallel();

    walker.run(|| {
        Box::new(|result| {
            if let Ok(entry) = result {
                println!("{}", entry.path().display());
            }
            ignore::WalkState::Continue
        })
    });
}
```

### 4.2 符号链接处理

```rust
use std::fs;
use std::io;
use std::path::Path;

fn main() -> io::Result<()> {
    let path = Path::new("./some_link");

    // 检查是否是符号链接
    if path.is_symlink() {
        println!("{} is a symlink", path.display());

        // 读取链接目标
        let target = fs::read_link(path)?;
        println!("Points to: {}", target.display());
    }

    // 创建符号链接
    #[cfg(unix)]
    create_symlink_unix("target.txt", "link.txt")?;

    #[cfg(windows)]
    create_symlink_windows("target.txt", "link.txt")?;

    Ok(())
}

#[cfg(unix)]
fn create_symlink_unix(original: &str, link: &str) -> io::Result<()> {
    std::os::unix::fs::symlink(original, link)
}

#[cfg(windows)]
fn create_symlink_windows(original: &str, link: &str) -> io::Result<()> {
    use std::os::windows::fs;

    if Path::new(original).is_file() {
        fs::symlink_file(original, link)
    } else {
        fs::symlink_dir(original, link)
    }
}
```

### 4.3 权限管理

```rust
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::Path;

#[cfg(unix)]
fn manage_permissions_unix<P: AsRef<Path>>(path: P) -> std::io::Result<()> {
    let path = path.as_ref();

    // 获取当前权限
    let metadata = fs::metadata(path)?;
    let permissions = metadata.permissions();
    let mode = permissions.mode();

    println!("Current permissions: {:o}", mode);

    // 设置权限（例如：755）
    let mut new_permissions = permissions.clone();
    new_permissions.set_mode(0o755);
    fs::set_permissions(path, new_permissions)?;

    // 使用 libc 进行更精细的控制
    unsafe {
        let c_path = std::ffi::CString::new(path.to_string_lossy().as_bytes()).unwrap();
        libc::chmod(c_path.as_ptr(), 0o755);
    }

    Ok(())
}

#[cfg(windows)]
fn manage_permissions_windows<P: AsRef<Path>>(path: P) -> std::io::Result<()> {
    use std::process::Command;

    let path = path.as_ref();

    // Windows 使用 icacls 命令
    Command::new("icacls")
        .arg(path)
        .arg("/grant")
        .arg("Everyone:(RX)")  // 读取和执行
        .output()?;

    Ok(())
}
```

### 4.4 跨平台路径

```rust
use std::path::{Path, PathBuf, MAIN_SEPARATOR};

fn main() {
    // 使用 PathBuf 构建路径（自动处理分隔符）
    let mut path = PathBuf::new();
    path.push("home");
    path.push("user");
    path.push("documents");
    path.push("file.txt");

    println!("Path: {}", path.display());

    // 路径操作
    path_operations();

    // 标准化路径
    normalize_path("./foo/../bar/./baz");
}

fn path_operations() {
    let path = Path::new("/home/user/docs/file.txt");

    // 获取组件
    println!("Components:");
    for component in path.components() {
        println!("  {:?}", component);
    }

    // 文件名操作
    println!("File name: {:?}", path.file_name());
    println!("Extension: {:?}", path.extension());
    println!("Stem: {:?}", path.file_stem());
    println!("Parent: {:?}", path.parent());

    // 拼接路径
    let new_path = path.join("subdir").join("another.txt");
    println!("New path: {}", new_path.display());

    // 检查绝对/相对路径
    println!("Is absolute: {}", path.is_absolute());
    println!("Is relative: {}", path.is_relative());
}

fn normalize_path<P: AsRef<Path>>(path: P) -> PathBuf {
    use std::path::Component;

    let mut result = PathBuf::new();

    for component in path.as_ref().components() {
        match component {
            Component::Normal(c) => result.push(c),
            Component::ParentDir => {
                result.pop();
            }
            Component::RootDir | Component::Prefix(_) => {
                result.push(component);
            }
            Component::CurDir => {}
        }
    }

    result
}

// 处理不同平台的特殊路径
fn platform_specific_paths() {
    // 获取标准目录
    if let Some(home) = dirs::home_dir() {
        println!("Home: {}", home.display());
    }

    if let Some(config) = dirs::config_dir() {
        println!("Config: {}", config.display());
    }

    if let Some(cache) = dirs::cache_dir() {
        println!("Cache: {}", cache.display());
    }
}
```

---

## 5. 配置管理

### 5.1 配置文件格式（TOML、YAML、JSON）

#### **TOML**

```toml
# Cargo.toml
[dependencies]
serde = { version = "1.0", features = ["derive"] }
toml = "0.8"
```

```rust
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::Path;

#[derive(Debug, Serialize, Deserialize)]
#[serde(default)]
struct Config {
    app_name: String,
    version: String,

    #[serde(default)]
    database: DatabaseConfig,

    #[serde(default)]
    server: ServerConfig,

    #[serde(default)]
    features: Vec<String>,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(default)]
struct DatabaseConfig {
    url: String,
    max_connections: u32,
    timeout: u64,
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(default)]
struct ServerConfig {
    host: String,
    port: u16,
    workers: usize,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            app_name: "MyApp".to_string(),
            version: "1.0.0".to_string(),
            database: DatabaseConfig::default(),
            server: ServerConfig::default(),
            features: vec![],
        }
    }
}

impl Default for DatabaseConfig {
    fn default() -> Self {
        Self {
            url: "sqlite:data.db".to_string(),
            max_connections: 10,
            timeout: 30,
        }
    }
}

impl Default for ServerConfig {
    fn default() -> Self {
        Self {
            host: "127.0.0.1".to_string(),
            port: 8080,
            workers: 4,
        }
    }
}

fn load_config<P: AsRef<Path>>(path: P) -> anyhow::Result<Config> {
    let content = fs::read_to_string(path)?;
    let config: Config = toml::from_str(&content)?;
    Ok(config)
}

fn save_config<P: AsRef<Path>>(path: P, config: &Config) -> anyhow::Result<()> {
    let content = toml::to_string_pretty(config)?;
    fs::write(path, content)?;
    Ok(())
}
```

#### **YAML**

```toml
# Cargo.toml
[dependencies]
serde = { version = "1.0", features = ["derive"] }
serde_yaml = "0.9"
```

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct YamlConfig {
    name: String,
    environment: Environment,
    settings: serde_yaml::Value,  // 动态配置
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
enum Environment {
    Development,
    Staging,
    Production,
}

fn load_yaml_config(path: &str) -> anyhow::Result<YamlConfig> {
    let content = std::fs::read_to_string(path)?;
    let config: YamlConfig = serde_yaml::from_str(&content)?;
    Ok(config)
}
```

#### **JSON**

```toml
# Cargo.toml
[dependencies]
serde = { version = "1.0", features = ["derive"] }
serde_json = "1.0"
```

```rust
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
struct JsonConfig {
    name: String,
    enabled: bool,

    #[serde(skip_serializing_if = "Option::is_none")]
    optional_field: Option<String>,

    #[serde(flatten)]
    extra: serde_json::Value,
}
```

### 5.2 环境变量

```rust
use std::env;
use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct EnvConfig {
    #[serde(default = "default_port")]
    port: u16,

    #[serde(default)]
    host: String,

    #[serde(default)]
    debug: bool,

    #[serde(default)]
    database_url: String,
}

fn default_port() -> u16 {
    3000
}

impl EnvConfig {
    fn from_env() -> Self {
        envy::from_env().unwrap_or_else(|_| Self {
            port: default_port(),
            host: "localhost".to_string(),
            debug: false,
            database_url: String::new(),
        })
    }
}

fn main() {
    // 使用 envy crate
    let config: EnvConfig = EnvConfig::from_env();
    println!("{:?}", config);

    // 手动读取环境变量
    manual_env_reading();
}

fn manual_env_reading() {
    // 读取单个变量
    let home = env::var("HOME").expect("HOME not set");
    println!("Home: {}", home);

    // 带默认值
    let editor = env::var("EDITOR").unwrap_or_else(|_| "vi".to_string());
    println!("Editor: {}", editor);

    // 带前缀的环境变量
    for (key, value) in env::vars().filter(|(k, _)| k.starts_with("MYAPP_")) {
        println!("{} = {}", key, value);
    }

    // 设置环境变量（仅影响当前进程）
    env::set_var("MYAPP_TEST", "value");
}
```

### 5.3 XDG 规范

[XDG Base Directory Specification](https://specifications.freedesktop.org/basedir-spec/basedir-spec-latest.html) 定义了配置文件、数据文件等的标准位置。

```toml
# Cargo.toml
[dependencies]
dirs = "5.0"
```

```rust
use std::path::PathBuf;

struct XdgPaths {
    app_name: String,
}

impl XdgPaths {
    fn new(app_name: impl Into<String>) -> Self {
        Self {
            app_name: app_name.into(),
        }
    }

    /// 配置文件目录 ($XDG_CONFIG_HOME 或 ~/.config)
    fn config_dir(&self) -> Option<PathBuf> {
        dirs::config_dir().map(|d| d.join(&self.app_name))
    }

    /// 数据文件目录 ($XDG_DATA_HOME 或 ~/.local/share)
    fn data_dir(&self) -> Option<PathBuf> {
        dirs::data_dir().map(|d| d.join(&self.app_name))
    }

    /// 缓存目录 ($XDG_CACHE_HOME 或 ~/.cache)
    fn cache_dir(&self) -> Option<PathBuf> {
        dirs::cache_dir().map(|d| d.join(&self.app_name))
    }

    /// 状态目录 ($XDG_STATE_HOME 或 ~/.local/state)
    fn state_dir(&self) -> Option<PathBuf> {
        dirs::state_dir().map(|d| d.join(&self.app_name))
    }

    /// 运行时目录 ($XDG_RUNTIME_DIR)
    fn runtime_dir(&self) -> Option<PathBuf> {
        dirs::runtime_dir().map(|d| d.join(&self.app_name))
    }
}

fn setup_app_directories(app_name: &str) -> std::io::Result<()> {
    let xdg = XdgPaths::new(app_name);

    // 创建必要的目录
    if let Some(dir) = xdg.config_dir() {
        std::fs::create_dir_all(&dir)?;
        println!("Config dir: {}", dir.display());
    }

    if let Some(dir) = xdg.data_dir() {
        std::fs::create_dir_all(&dir)?;
        println!("Data dir: {}", dir.display());
    }

    if let Some(dir) = xdg.cache_dir() {
        std::fs::create_dir_all(&dir)?;
        println!("Cache dir: {}", dir.display());
    }

    Ok(())
}
```

### 5.4 配置验证

```rust
use serde::Deserialize;
use validator::{Validate, ValidationError};

#[derive(Debug, Deserialize, Validate)]
struct ValidatedConfig {
    #[validate(length(min = 1, max = 100))]
    name: String,

    #[validate(range(min = 1, max = 65535))]
    port: u16,

    #[validate(url)]
    endpoint: String,

    #[validate(email)]
    admin_email: String,

    #[validate(nested)]
    database: DatabaseSettings,

    #[validate(custom(function = "validate_log_level"))]
    log_level: String,
}

#[derive(Debug, Deserialize, Validate)]
struct DatabaseSettings {
    #[validate(length(min = 1))]
    host: String,

    #[validate(range(min = 1, max = 100))]
    max_connections: u32,

    #[validate(range(min = 1, max = 300))]
    timeout_seconds: u64,
}

fn validate_log_level(level: &str) -> Result<(), ValidationError> {
    let valid_levels = ["trace", "debug", "info", "warn", "error"];
    if valid_levels.contains(&level.to_lowercase().as_str()) {
        Ok(())
    } else {
        Err(ValidationError::new("invalid_log_level"))
    }
}

fn load_and_validate_config(path: &str) -> Result<ValidatedConfig, Box<dyn std::error::Error>> {
    let content = std::fs::read_to_string(path)?;
    let config: ValidatedConfig = toml::from_str(&content)?;
    config.validate()?;
    Ok(config)
}

// 带详细错误信息的验证
fn detailed_validation(config: &ValidatedConfig) -> Vec<String> {
    let mut errors = Vec::new();

    if config.name.is_empty() {
        errors.push("name cannot be empty".to_string());
    }

    if config.port == 0 {
        errors.push("port must be greater than 0".to_string());
    }

    if !config.endpoint.starts_with("http://") && !config.endpoint.starts_with("https://") {
        errors.push("endpoint must be a valid HTTP(S) URL".to_string());
    }

    errors
}
```

---

## 6. 错误处理

### 6.1 anyhow/eyre

[anyhow](https://github.com/dtolnay/anyhow) 和 [eyre](https://github.com/eyre-rs/eyre) 提供了易于使用的错误处理机制。

```toml
# Cargo.toml
[dependencies]
anyhow = { version = "1.0", features = ["backtrace"] }
# 或
eyre = "0.6"
```

#### **anyhow 基础使用**

```rust
use anyhow::{Context, Result, bail};
use std::fs;
use std::path::Path;

fn main() -> Result<()> {
    let config = read_config("config.toml")
        .context("Failed to read configuration")?;

    let data = process_data(&config)
        .context("Failed to process data")?;

    save_results(&data, "output.json")
        .context("Failed to save results")?;

    Ok(())
}

fn read_config<P: AsRef<Path>>(path: P) -> Result<String> {
    // anyhow::Error 自动实现了 From<std::io::Error>
    let content = fs::read_to_string(&path)
        .with_context(|| format!("Failed to read {}", path.as_ref().display()))?;

    if content.is_empty() {
        bail!("Configuration file is empty");
    }

    Ok(content)
}

fn process_data(config: &str) -> Result<Vec<Record>> {
    let records: Vec<Record> = serde_json::from_str(config)
        .context("Invalid JSON format in configuration")?;

    if records.is_empty() {
        bail!("No records found in configuration");
    }

    Ok(records)
}

fn save_results(data: &[Record], path: &str) -> Result<()> {
    let json = serde_json::to_string_pretty(data)
        .context("Failed to serialize results")?;

    fs::write(path, json)?;

    Ok(())
}

#[derive(serde::Deserialize, serde::Serialize)]
struct Record {
    id: u64,
    name: String,
}
```

#### **自定义错误类型（与 anyhow 结合）**

```rust
use anyhow::Result;
use thiserror::Error;

#[derive(Error, Debug)]
enum AppError {
    #[error("Invalid configuration: {0}")]
    InvalidConfig(String),

    #[error("Database connection failed: {message}")]
    DatabaseError { message: String },

    #[error("Authentication failed for user: {user}")]
    AuthenticationFailed { user: String },

    #[error(transparent)]
    IoError(#[from] std::io::Error),

    #[error(transparent)]
    ParseError(#[from] serde_json::Error),
}

fn authenticate(user: &str, password: &str) -> Result<(), AppError> {
    if user.is_empty() {
        return Err(AppError::AuthenticationFailed {
            user: user.to_string(),
        });
    }

    // 验证逻辑...
    if password != "secret" {
        return Err(AppError::AuthenticationFailed {
            user: user.to_string(),
        });
    }

    Ok(())
}

fn load_app_config() -> Result<Config, AppError> {
    let content = std::fs::read_to_string("config.json")?;  // 自动转换为 IoError
    let config: Config = serde_json::from_str(&content)?;    // 自动转换为 ParseError

    if config.version < 2 {
        return Err(AppError::InvalidConfig(
            "Configuration version must be >= 2".to_string()
        ));
    }

    Ok(config)
}

#[derive(serde::Deserialize)]
struct Config {
    version: u32,
}
```

### 6.2 人性化的错误信息

```rust
use anyhow::{Context, Result};
use std::fmt;

/// 用户友好的错误显示
#[derive(Debug)]
struct UserFriendlyError {
    brief: String,
    details: Option<String>,
    suggestion: Option<String>,
}

impl fmt::Display for UserFriendlyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Error: {}", self.brief)?;

        if let Some(details) = &self.details {
            writeln!(f, "\nDetails: {}", details)?;
        }

        if let Some(suggestion) = &self.suggestion {
            writeln!(f, "\nSuggestion: {}", suggestion)?;
        }

        Ok(())
    }
}

impl std::error::Error for UserFriendlyError {}

fn main() {
    if let Err(e) = run() {
        eprintln!("{}", format_error(&e));
        std::process::exit(1);
    }
}

fn run() -> Result<()> {
    // 应用程序逻辑
    read_file("/nonexistent/path.txt")
        .context("Failed to read required file")?;
    Ok(())
}

fn read_file(path: &str) -> Result<String> {
    std::fs::read_to_string(path)
        .map_err(|e| UserFriendlyError {
            brief: format!("Cannot access '{}'", path),
            details: Some(format!("System error: {}", e)),
            suggestion: Some(format!(
                "Please ensure:\n  1. The file exists\n  2. You have read permissions\n  3. The path is correct"
            )),
        })?
}

fn format_error(e: &anyhow::Error) -> String {
    use owo_colors::OwoColorize;

    let mut output = format!("{}: {}", "ERROR".red().bold(), e);

    // 遍历错误链
    if let Some(cause) = e.source() {
        output.push_str(&format!("\n\n{}: {}", "CAUSED BY".yellow(), cause));
    }

    output
}
```

### 6.3 错误链

```rust
use anyhow::{Context, Result, Chain};

fn complex_operation() -> Result<()> {
    step_one()
        .context("Step 1 failed")?
        .step_two()
        .context("Step 2 failed")?
        .step_three()
        .context("Step 3 failed")?;

    Ok(())
}

fn print_error_chain(error: &anyhow::Error) {
    eprintln!("Error: {}", error);

    // 遍历所有错误来源
    for (i, cause) in error.chain().enumerate().skip(1) {
        eprintln!("  Caused by ({}): {}", i, cause);
    }
}

fn collect_error_chain(error: &anyhow::Error) -> Vec<String> {
    error.chain()
        .map(|e| e.to_string())
        .collect()
}

// 使用跟踪日志记录完整错误
fn log_error_with_backtrace(error: &anyhow::Error) {
    log::error!("Operation failed: {:#}", error);

    if let Some(backtrace) = error.backtrace() {
        log::debug!("Backtrace: {}", backtrace);
    }
}
```

### 6.4 退出码

```rust
use std::process;

#[derive(Debug, Clone, Copy)]
#[repr(u8)]
enum ExitCode {
    Success = 0,
    GeneralError = 1,
    InvalidArguments = 2,
    FileNotFound = 3,
    PermissionDenied = 4,
    ConfigError = 5,
    NetworkError = 6,
    Timeout = 7,
}

impl From<ExitCode> for i32 {
    fn from(code: ExitCode) -> Self {
        code as i32
    }
}

fn main() {
    let code = match run() {
        Ok(()) => ExitCode::Success,
        Err(e) => {
            eprintln!("Error: {}", e);
            classify_error(&e)
        }
    };

    process::exit(code.into());
}

fn run() -> anyhow::Result<()> {
    // 应用程序逻辑
    Ok(())
}

fn classify_error(error: &anyhow::Error) -> ExitCode {
    let error_string = error.to_string();

    if error_string.contains("not found") {
        ExitCode::FileNotFound
    } else if error_string.contains("permission") {
        ExitCode::PermissionDenied
    } else if error_string.contains("configuration") {
        ExitCode::ConfigError
    } else if error_string.contains("network") {
        ExitCode::NetworkError
    } else {
        ExitCode::GeneralError
    }
}

// 使用 anyhow 的自定义退出
fn run_with_custom_exit() -> ! {
    let result = actual_run();

    match result {
        Ok(()) => process::exit(0),
        Err(e) => {
            eprintln!("Error: {:#}", e);
            process::exit(1);
        }
    }
}

fn actual_run() -> anyhow::Result<()> {
    Ok(())
}
```

---

## 7. 日志与输出

### 7.1 tracing 日志

[tracing](https://github.com/tokio-rs/tracing) 是 Rust 生态系统中的高级日志和诊断库。

```toml
# Cargo.toml
[dependencies]
tracing = "0.1"
tracing-subscriber = { version = "0.3", features = ["env-filter", "fmt"] }
```

```rust
use tracing::{info, debug, warn, error, span, Level};
use tracing_subscriber::{layer::SubscriberExt, util::SubscriberInitExt};

fn main() {
    // 初始化日志订阅者
    tracing_subscriber::registry()
        .with(
            tracing_subscriber::EnvFilter::try_from_default_env()
                .unwrap_or_else(|_| "info".into()),
        )
        .with(tracing_subscriber::fmt::layer())
        .init();

    // 基本日志
    info!("Application started");
    debug!("Debug information: {:?}", std::env::args());

    // 结构化日志
    process_file("data.txt", 42);

    // 带 Span 的上下文跟踪
    process_with_span();
}

#[tracing::instrument(skip(content), fields(size = content.len()))]
fn process_file(path: &str, id: u64) -> Result<(), std::io::Error> {
    info!("Processing file");

    // 模拟处理
    let content = std::fs::read_to_string(path)?;

    debug!(bytes_read = content.len(), "File read complete");

    Ok(())
}

fn process_with_span() {
    let root_span = span!(Level::INFO, "process_operation", op_id = %uuid::Uuid::new_v4());

    let _enter = root_span.enter();

    info!("Starting operation");

    {
        let inner_span = span!(Level::DEBUG, "inner_work", step = 1);
        let _inner_enter = inner_span.enter();

        debug!("Performing inner work");
        std::thread::sleep(std::time::Duration::from_millis(100));
    }

    info!("Operation complete");
}
```

#### **自定义日志输出格式**

```rust
use tracing_subscriber::fmt::{self, format::FmtSpan};
use tracing_subscriber::layer::SubscriberExt;

fn init_custom_logger() {
    let fmt_layer = fmt::layer()
        .with_target(true)
        .with_thread_ids(true)
        .with_thread_names(true)
        .with_file(true)
        .with_line_number(true)
        .with_span_events(FmtSpan::FULL)
        .with_timer(fmt::time::UtcTime::rfc_3339());

    tracing_subscriber::registry()
        .with(fmt_layer)
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .init();
}

// JSON 格式日志
fn init_json_logger() {
    let fmt_layer = fmt::layer()
        .json()
        .with_current_span(true)
        .with_span_list(true);

    tracing_subscriber::registry()
        .with(fmt_layer)
        .init();
}
```

### 7.2 结构化输出

```rust
use serde::Serialize;
use serde_json::json;

#[derive(Serialize)]
struct OutputRecord {
    timestamp: String,
    level: String,
    message: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    file: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    line: Option<u32>,
    #[serde(flatten)]
    extra: serde_json::Value,
}

fn output_json(records: &[OutputRecord]) {
    for record in records {
        println!("{}", serde_json::to_string(record).unwrap());
    }
}

fn output_ndjson(records: &[OutputRecord]) {
    // NDJSON (Newline Delimited JSON) 格式
    for record in records {
        println!("{}", serde_json::to_string(record).unwrap());
    }
}

// 结构化结果输出
fn print_results(results: &SearchResults) {
    let output = json!({
        "total_matches": results.total,
        "files_searched": results.files_searched,
        "duration_ms": results.duration.as_millis(),
        "matches": results.matches.iter().map(|m| {
            json!({
                "file": m.file,
                "line": m.line,
                "column": m.column,
                "text": m.text,
            })
        }).collect::<Vec<_>>(),
    });

    println!("{}", serde_json::to_string_pretty(&output).unwrap());
}

struct SearchResults {
    total: usize,
    files_searched: usize,
    duration: std::time::Duration,
    matches: Vec<Match>,
}

struct Match {
    file: String,
    line: usize,
    column: usize,
    text: String,
}
```

### 7.3 日志级别

```rust
use tracing::Level;

#[derive(Debug, Clone, Copy)]
enum LogLevel {
    Error = 1,
    Warn = 2,
    Info = 3,
    Debug = 4,
    Trace = 5,
}

impl From<LogLevel> for Level {
    fn from(level: LogLevel) -> Self {
        match level {
            LogLevel::Error => Level::ERROR,
            LogLevel::Warn => Level::WARN,
            LogLevel::Info => Level::INFO,
            LogLevel::Debug => Level::DEBUG,
            LogLevel::Trace => Level::TRACE,
        }
    }
}

fn init_logging(level: LogLevel) {
    let filter = match level {
        LogLevel::Error => "error",
        LogLevel::Warn => "warn",
        LogLevel::Info => "info",
        LogLevel::Debug => "debug",
        LogLevel::Trace => "trace",
    };

    tracing_subscriber::fmt()
        .with_max_level(level.into())
        .with_env_filter(filter)
        .init();
}

// 动态日志级别调整
use tracing_subscriber::reload::Handle;
use tracing_subscriber::EnvFilter;

static LOG_LEVEL_HANDLE: OnceLock<Handle<EnvFilter, tracing_subscriber::Registry>> = OnceLock::new();

fn init_reloadable_logging() {
    let filter = EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("info"));

    let (filter, reload_handle) = tracing_subscriber::reload::Layer::new(filter);

    tracing_subscriber::registry()
        .with(filter)
        .with(tracing_subscriber::fmt::layer())
        .init();

    LOG_LEVEL_HANDLE.set(reload_handle).ok();
}

fn set_log_level(level: &str) -> Result<(), String> {
    let handle = LOG_LEVEL_HANDLE.get().ok_or("Logging not initialized")?;
    let filter = EnvFilter::try_new(level).map_err(|e| e.to_string())?;
    handle.reload(filter).map_err(|e| e.to_string())?;
    Ok(())
}
```

### 7.4 输出重定向

```rust
use std::fs::File;
use std::io::{self, Write};

struct OutputManager {
    stdout: Box<dyn Write>,
    stderr: Box<dyn Write>,
    quiet: bool,
}

impl OutputManager {
    fn new() -> Self {
        Self {
            stdout: Box::new(io::stdout()),
            stderr: Box::new(io::stderr()),
            quiet: false,
        }
    }

    fn redirect_stdout<P: AsRef<std::path::Path>>(mut self, path: P) -> io::Result<Self> {
        let file = File::create(path)?;
        self.stdout = Box::new(file);
        Ok(self)
    }

    fn redirect_stderr<P: AsRef<std::path::Path>>(mut self, path: P) -> io::Result<Self> {
        let file = File::create(path)?;
        self.stderr = Box::new(file);
        Ok(self)
    }

    fn set_quiet(mut self, quiet: bool) -> Self {
        self.quiet = quiet;
        self
    }

    fn println(&mut self, msg: &str) -> io::Result<()> {
        if !self.quiet {
            writeln!(self.stdout, "{}", msg)?;
        }
        Ok(())
    }

    fn eprintln(&mut self, msg: &str) -> io::Result<()> {
        if !self.quiet {
            writeln!(self.stderr, "{}", msg)?;
        }
        Ok(())
    }
}

// 检测输出是否为 TTY
fn setup_output() -> OutputMode {
    use atty::Stream;

    let stdout_is_tty = atty::is(Stream::Stdout);
    let stderr_is_tty = atty::is(Stream::Stderr);

    if stdout_is_tty {
        OutputMode::Terminal
    } else {
        OutputMode::Piped
    }
}

enum OutputMode {
    Terminal,  // 可以输出颜色、进度条等
    Piped,     // 纯文本输出，无颜色
}

fn print_with_mode(msg: &str, mode: &OutputMode) {
    match mode {
        OutputMode::Terminal => {
            println!("{}", msg.green());
        }
        OutputMode::Piped => {
            println!("{}", msg);  // 无颜色
        }
    }
}
```

---

## 8. 完整示例：文件搜索工具

下面是一个功能完整的文件搜索工具，整合了前面讨论的所有概念：

```rust
//! fsearch - 一个高性能的文件搜索工具
//!
//! 功能特点：
//! - 递归目录遍历
//! - 正则表达式匹配
//! - 并行处理
//! - 结果格式化
//! - 配置文件支持
//! - 彩色输出

use anyhow::{Context, Result, bail};
use clap::Parser;
use ignore::WalkBuilder;
use indicatif::{ParallelProgressIterator, ProgressBar, ProgressStyle};
use owo_colors::OwoColorize;
use rayon::prelude::*;
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::fs;
use std::io::{self, BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use tracing::{debug, info, warn};

/// 命令行参数
#[derive(Parser, Debug)]
#[command(name = "fsearch")]
#[command(about = "A fast file search tool written in Rust")]
#[command(version)]
struct Args {
    /// 搜索模式（正则表达式）
    pattern: String,

    /// 搜索路径（默认为当前目录）
    #[arg(default_value = ".")]
    path: PathBuf,

    /// 配置文件路径
    #[arg(short, long)]
    config: Option<PathBuf>,

    /// 文件类型过滤（扩展名，如: rs,txt,md）
    #[arg(short, long, value_delimiter = ',')]
    file_types: Vec<String>,

    /// 最大搜索深度
    #[arg(short, long)]
    max_depth: Option<usize>,

    /// 忽略大小写
    #[arg(short, long)]
    ignore_case: bool,

    /// 只显示匹配的文件名，不显示具体行
    #[arg(short = 'l', long)]
    files_with_matches: bool,

    /// 显示行号
    #[arg(short = 'n', long, default_value_t = true)]
    line_number: bool,

    /// 显示匹配上下文（前后行数）
    #[arg(short = 'C', long, default_value_t = 0)]
    context: usize,

    /// 最大并发线程数
    #[arg(short = 'j', long)]
    threads: Option<usize>,

    /// 输出格式（pretty, json, simple）
    #[arg(short, long, default_value = "pretty")]
    format: OutputFormat,

    /// 禁用彩色输出
    #[arg(long)]
    no_color: bool,

    /// 包括隐藏文件
    #[arg(long)]
    hidden: bool,

    /// 显示统计信息
    #[arg(long)]
    stats: bool,

    /// 静默模式（只输出结果）
    #[arg(short, long)]
    quiet: bool,
}

#[derive(Debug, Clone, Copy, Default, clap::ValueEnum)]
enum OutputFormat {
    #[default]
    Pretty,
    Json,
    Simple,
}

/// 配置文件结构
#[derive(Debug, Deserialize, Serialize)]
#[serde(default)]
struct Config {
    ignore_case: bool,
    max_depth: Option<usize>,
    file_types: Vec<String>,
    hidden: bool,
    threads: usize,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            ignore_case: false,
            max_depth: None,
            file_types: vec![],
            hidden: false,
            threads: num_cpus::get(),
        }
    }
}

/// 匹配结果
#[derive(Debug, Clone)]
struct Match {
    file: PathBuf,
    line_number: usize,
    column_start: usize,
    column_end: usize,
    text: String,
    context_before: Vec<String>,
    context_after: Vec<String>,
}

/// 搜索结果
#[derive(Debug, Clone)]
struct SearchResults {
    pattern: String,
    total_matches: usize,
    files_searched: usize,
    files_matched: usize,
    duration: Duration,
    matches: Vec<Match>,
}

fn main() -> Result<()> {
    let start = Instant::now();
    let args = Args::parse();

    // 初始化日志
    init_tracing(&args)?;

    // 加载配置
    let config = load_config(&args)?;

    // 合并命令行参数和配置文件
    let settings = merge_settings(args, config);

    // 执行搜索
    let results = search(&settings)?;

    // 格式化输出
    print_results(&results, &settings)?;

    if settings.stats {
        print_stats(&results, start.elapsed());
    }

    Ok(())
}

fn init_tracing(args: &Args) -> Result<()> {
    use tracing_subscriber::{fmt, EnvFilter};

    let filter = if args.quiet {
        "error"
    } else {
        "info"
    };

    fmt::fmt()
        .with_env_filter(EnvFilter::try_from_default_env().unwrap_or_else(|_| filter.into()))
        .init();

    Ok(())
}

fn load_config(args: &Args) -> Result<Config> {
    let config_path = match &args.config {
        Some(p) => p.clone(),
        None => {
            // 尝试从标准位置加载
            dirs::config_dir()
                .map(|d| d.join("fsearch").join("config.toml"))
                .context("Could not determine config directory")?
        }
    };

    if !config_path.exists() {
        debug!("Config file not found: {:?}", config_path);
        return Ok(Config::default());
    }

    let content = fs::read_to_string(&config_path)
        .with_context(|| format!("Failed to read config from {:?}", config_path))?;

    let config: Config = toml::from_str(&content)
        .with_context(|| format!("Failed to parse config from {:?}", config_path))?;

    info!("Loaded config from {:?}", config_path);
    Ok(config)
}

fn merge_settings(args: Args, config: Config) -> Settings {
    Settings {
        pattern: args.pattern,
        path: args.path,
        file_types: if args.file_types.is_empty() {
            config.file_types
        } else {
            args.file_types
        },
        max_depth: args.max_depth.or(config.max_depth),
        ignore_case: args.ignore_case || config.ignore_case,
        files_with_matches: args.files_with_matches,
        line_number: args.line_number,
        context: args.context,
        threads: args.threads.unwrap_or(config.threads),
        format: args.format,
        no_color: args.no_color,
        hidden: args.hidden || config.hidden,
        quiet: args.quiet,
    }
}

struct Settings {
    pattern: String,
    path: PathBuf,
    file_types: Vec<String>,
    max_depth: Option<usize>,
    ignore_case: bool,
    files_with_matches: bool,
    line_number: bool,
    context: usize,
    threads: usize,
    format: OutputFormat,
    no_color: bool,
    hidden: bool,
    quiet: bool,
}

fn search(settings: &Settings) -> Result<SearchResults> {
    let start = Instant::now();

    // 编译正则表达式
    let regex = build_regex(&settings.pattern, settings.ignore_case)?;

    // 构建文件遍历器
    let walker = build_walker(settings)?;

    // 收集所有文件
    let files: Vec<_> = walker
        .filter_map(|e| e.ok())
        .filter(|e| e.file_type().map(|ft| ft.is_file()).unwrap_or(false))
        .map(|e| e.path().to_path_buf())
        .collect();

    info!("Found {} files to search", files.len());

    // 设置线程池
    let pool = rayon::ThreadPoolBuilder::new()
        .num_threads(settings.threads)
        .build()
        .context("Failed to build thread pool")?;

    let files_searched = Arc::new(Mutex::new(0usize));
    let matches = Arc::new(Mutex::new(Vec::new()));

    // 并行搜索
    let progress = if settings.quiet {
        None
    } else {
        Some(ProgressBar::new(files.len() as u64).with_style(
            ProgressStyle::default_bar()
                .template("{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} ({eta})")
                .unwrap()
                .progress_chars("#>-"),
        ))
    };

    pool.install(|| {
        let file_matches: Vec<_> = files
            .par_iter()
            .progress_with(progress.unwrap_or_else(|| ProgressBar::hidden()))
            .filter_map(|file| {
                let result = search_file(file, &regex, settings).ok()?;

                {
                    let mut count = files_searched.lock().unwrap();
                    *count += 1;
                }

                if !result.is_empty() {
                    Some((file.clone(), result))
                } else {
                    None
                }
            })
            .collect();

        let mut all_matches = matches.lock().unwrap();
        let mut files_matched = 0;

        for (file, file_matches) in file_matches {
            files_matched += 1;
            all_matches.extend(file_matches);
        }

        SearchResults {
            pattern: settings.pattern.clone(),
            total_matches: all_matches.len(),
            files_searched: *files_searched.lock().unwrap(),
            files_matched,
            duration: start.elapsed(),
            matches: all_matches.clone(),
        }
    })
}

fn build_regex(pattern: &str, ignore_case: bool) -> Result<Regex> {
    let mut builder = regex::RegexBuilder::new(pattern);

    if ignore_case {
        builder.case_insensitive(true);
    }

    builder.build().context("Invalid regex pattern")
}

fn build_walker(settings: &Settings) -> ignore::Walk {
    let mut builder = WalkBuilder::new(&settings.path);

    builder
        .hidden(!settings.hidden)
        .git_ignore(true)
        .git_global(true)
        .parents(true);

    if let Some(depth) = settings.max_depth {
        builder.max_depth(Some(depth));
    }

    if !settings.file_types.is_empty() {
        let types = settings.file_types.clone();
        builder.filter_entry(move |entry| {
            if entry.file_type().map(|ft| ft.is_dir()).unwrap_or(false) {
                return true;
            }

            entry.path()
                .extension()
                .and_then(|ext| ext.to_str())
                .map(|ext| types.iter().any(|t| t.eq_ignore_ascii_case(ext)))
                .unwrap_or(true)
        });
    }

    builder.build()
}

fn search_file(path: &Path, regex: &Regex, settings: &Settings) -> Result<Vec<Match>> {
    let file = fs::File::open(path)
        .with_context(|| format!("Failed to open {}", path.display()))?;

    let reader = BufReader::new(file);
    let mut matches = Vec::new();
    let mut lines: Vec<String> = Vec::new();

    // 读取所有行以支持上下文
    for line in reader.lines() {
        lines.push(line?);
    }

    for (i, line) in lines.iter().enumerate() {
        if let Some(mat) = regex.find(line) {
            let context_before = if settings.context > 0 {
                lines[i.saturating_sub(settings.context)..i]
                    .iter()
                    .cloned()
                    .collect()
            } else {
                vec![]
            };

            let context_after = if settings.context > 0 {
                lines[i + 1..(i + 1 + settings.context).min(lines.len())]
                    .iter()
                    .cloned()
                    .collect()
            } else {
                vec![]
            };

            matches.push(Match {
                file: path.to_path_buf(),
                line_number: i + 1,
                column_start: mat.start(),
                column_end: mat.end(),
                text: line.clone(),
                context_before,
                context_after,
            });
        }
    }

    Ok(matches)
}

fn print_results(results: &SearchResults, settings: &Settings) -> Result<()> {
    if results.total_matches == 0 {
        return Ok(());
    }

    match settings.format {
        OutputFormat::Pretty => print_pretty(results, settings),
        OutputFormat::Json => print_json(results)?,
        OutputFormat::Simple => print_simple(results, settings),
    }

    Ok(())
}

fn print_pretty(results: &SearchResults, settings: &Settings) {
    if settings.no_color {
        print_simple(results, settings);
        return;
    }

    let mut current_file: Option<&Path> = None;

    for mat in &results.matches {
        // 如果是 files_with_matches 模式，只打印文件名一次
        if settings.files_with_matches {
            if current_file != Some(&mat.file) {
                println!("{}", mat.file.display().to_string().cyan());
                current_file = Some(&mat.file);
            }
            continue;
        }

        // 打印文件名头
        if current_file != Some(&mat.file) {
            println!("\n{}", mat.file.display().to_string().cyan().underline());
            current_file = Some(&mat.file);
        }

        // 打印上下文
        for (i, ctx) in mat.context_before.iter().enumerate() {
            let line_num = mat.line_number - mat.context_before.len() + i;
            println!("{} {}",
                format!("{:>6}", line_num).dimmed(),
                ctx.dimmed()
            );
        }

        // 打印匹配行
        let before = &mat.text[..mat.column_start];
        let matched = &mat.text[mat.column_start..mat.column_end];
        let after = &mat.text[mat.column_end..];

        if settings.line_number {
            print!("{} ", format!("{:>6}", mat.line_number).yellow());
        }
        println!("{}{}{}", before, matched.red().bold(), after);

        // 打印后续上下文
        for (i, ctx) in mat.context_after.iter().enumerate() {
            let line_num = mat.line_number + 1 + i;
            println!("{} {}",
                format!("{:>6}", line_num).dimmed(),
                ctx.dimmed()
            );
        }
    }
}

fn print_simple(results: &SearchResults, settings: &Settings) {
    let mut current_file: Option<&Path> = None;

    for mat in &results.matches {
        if settings.files_with_matches {
            if current_file != Some(&mat.file) {
                println!("{}", mat.file.display());
                current_file = Some(&mat.file);
            }
            continue;
        }

        if settings.line_number {
            println!("{}:{}: {}", mat.file.display(), mat.line_number, mat.text);
        } else {
            println!("{}: {}", mat.file.display(), mat.text);
        }
    }
}

fn print_json(results: &SearchResults) -> Result<()> {
    use serde_json::json;

    let json_results: Vec<_> = results.matches.iter().map(|m| {
        json!({
            "file": m.file,
            "line_number": m.line_number,
            "column_start": m.column_start,
            "column_end": m.column_end,
            "text": m.text,
        })
    }).collect();

    println!("{}", serde_json::to_string_pretty(&json_results)?);
    Ok(())
}

fn print_stats(results: &SearchResults, total_duration: Duration) {
    eprintln!("\n{}:", "Statistics".bold());
    eprintln!("  Pattern: {}", results.pattern);
    eprintln!("  Total matches: {}", results.total_matches);
    eprintln!("  Files searched: {}", results.files_searched);
    eprintln!("  Files matched: {}", results.files_matched);
    eprintln!("  Search time: {:?}", results.duration);
    eprintln!("  Total time: {:?}", total_duration);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_regex_building() {
        let regex = build_regex("test", false).unwrap();
        assert!(regex.is_match("test"));
        assert!(!regex.is_match("TEST"));

        let regex = build_regex("test", true).unwrap();
        assert!(regex.is_match("TEST"));
    }

    #[test]
    fn test_config_loading() {
        let config: Config = toml::from_str(r#"
            ignore_case = true
            max_depth = 5
            threads = 4
        "#).unwrap();

        assert!(config.ignore_case);
        assert_eq!(config.max_depth, Some(5));
        assert_eq!(config.threads, 4);
    }
}
```

---

## 9. 打包与分发

### 9.1 cargo-install

```bash
# 从 crates.io 安装
cargo install ripgrep
cargo install fd-find

# 安装特定版本
cargo install ripgrep@13.0.0

# 从 Git 仓库安装
cargo install --git https://github.com/BurntSushi/ripgrep

# 从本地路径安装
cargo install --path ./my-cli-tool

# 安装到自定义目录
cargo install --root ~/.local ripgrep
```

### 9.2 静态链接

#### **Linux 静态链接（musl）**

```toml
# .cargo/config.toml
[target.x86_64-unknown-linux-musl]
linker = "rust-lld"
```

```bash
# 添加 musl 目标
rustup target add x86_64-unknown-linux-musl

# 使用 musl 构建（完全静态链接）
cargo build --release --target x86_64-unknown-linux-musl

# 验证链接
cargo install cargo-bloat
cargo bloat --release --target x86_64-unknown-linux-musl
```

#### **Windows 静态链接**

```bash
# 使用 MSVC 静态运行时
RUSTFLAGS="-C target-feature=+crt-static" cargo build --release

# 或使用 GNU 工具链
rustup target add x86_64-pc-windows-gnu
cargo build --release --target x86_64-pc-windows-gnu
```

#### **macOS 静态链接**

```bash
# macOS 不支持完全静态链接，但可以优化链接
RUSTFLAGS="-C link-arg=-Wl,-undefined,dynamic_lookup" cargo build --release
```

### 9.3 多平台构建

#### **使用 cross 工具**

```bash
# 安装 cross
cargo install cross

# 使用 Docker 进行跨平台构建
cross build --release --target x86_64-pc-windows-gnu
cross build --release --target aarch64-unknown-linux-gnu
cross build --release --target aarch64-apple-darwin

# 支持的常用目标
# x86_64-unknown-linux-gnu      # Linux x86_64
# x86_64-unknown-linux-musl     # Linux x86_64 (静态)
# aarch64-unknown-linux-gnu     # Linux ARM64
# x86_64-pc-windows-msvc        # Windows x86_64
# x86_64-apple-darwin           # macOS x86_64
# aarch64-apple-darwin          # macOS ARM64
```

#### **GitHub Actions 自动构建**

```yaml
# .github/workflows/release.yml
name: Release

on:
  push:
    tags:
      - 'v*'

jobs:
  build:
    runs-on: ${{ matrix.os }}
    strategy:
      matrix:
        include:
          - os: ubuntu-latest
            target: x86_64-unknown-linux-gnu
            artifact_name: myapp
            asset_name: myapp-linux-amd64
          - os: ubuntu-latest
            target: x86_64-unknown-linux-musl
            artifact_name: myapp
            asset_name: myapp-linux-amd64-musl
          - os: windows-latest
            target: x86_64-pc-windows-msvc
            artifact_name: myapp.exe
            asset_name: myapp-windows-amd64.exe
          - os: macos-latest
            target: x86_64-apple-darwin
            artifact_name: myapp
            asset_name: myapp-macos-amd64
          - os: macos-latest
            target: aarch64-apple-darwin
            artifact_name: myapp
            asset_name: myapp-macos-arm64

    steps:
    - uses: actions/checkout@v4

    - name: Install Rust
      uses: dtolnay/rust-action@stable
      with:
        targets: ${{ matrix.target }}

    - name: Install cross
      if: matrix.target == 'x86_64-unknown-linux-musl'
      run: cargo install cross

    - name: Build
      run: |
        if [ "${{ matrix.target }}" = "x86_64-unknown-linux-musl" ]; then
          cross build --release --target ${{ matrix.target }}
        else
          cargo build --release --target ${{ matrix.target }}
        fi
      shell: bash

    - name: Upload artifact
      uses: actions/upload-artifact@v4
      with:
        name: ${{ matrix.asset_name }}
        path: target/${{ matrix.target }}/release/${{ matrix.artifact_name }}

  release:
    needs: build
    runs-on: ubuntu-latest
    steps:
    - uses: actions/download-artifact@v4

    - name: Create Release
      uses: softprops/action-gh-release@v1
      with:
        files: '**/*'
```

### 9.4 包管理器

#### **Homebrew（macOS/Linux）**

创建 `Formula/myapp.rb`：

```ruby
class Myapp < Formula
  desc "Description of my CLI tool"
  homepage "https://github.com/username/myapp"
  url "https://github.com/username/myapp/archive/v1.0.0.tar.gz"
  sha256 "SHA256_OF_TARBALL"
  license "MIT"

  depends_on "rust" => :build

  def install
    system "cargo", "install", *std_cargo_args
  end

  test do
    assert_match "version", shell_output("#{bin}/myapp --version")
  end
end
```

```bash
# 本地测试
brew install --build-from-source ./Formula/myapp.rb

# 提交到 Homebrew
brew create https://github.com/username/myapp/archive/v1.0.0.tar.gz
brew install myapp
```

#### **Scoop（Windows）**

创建 `myapp.json`：

```json
{
  "version": "1.0.0",
  "description": "Description of my CLI tool",
  "homepage": "https://github.com/username/myapp",
  "license": "MIT",
  "architecture": {
    "64bit": {
      "url": "https://github.com/username/myapp/releases/download/v1.0.0/myapp-windows-amd64.exe",
      "hash": "SHA256_HASH"
    }
  },
  "bin": [
    ["myapp-windows-amd64.exe", "myapp"]
  ],
  "checkver": {
    "github": "https://github.com/username/myapp"
  },
  "autoupdate": {
    "architecture": {
      "64bit": {
        "url": "https://github.com/username/myapp/releases/download/v$version/myapp-windows-amd64.exe"
      }
    }
  }
}
```

```bash
# 安装
scoop bucket add mybucket https://github.com/username/scoop-bucket
scoop install mybucket/myapp
```

#### **AUR（Arch Linux）**

创建 `PKGBUILD`：

```bash
# Maintainer: Your Name <email@example.com>
pkgname=myapp
pkgver=1.0.0
pkgrel=1
pkgdesc="Description of my CLI tool"
arch=('x86_64')
url="https://github.com/username/myapp"
license=('MIT')
depends=()
makedepends=('rust' 'cargo')
source=("$pkgname-$pkgver.tar.gz::$url/archive/v$pkgver.tar.gz")
sha256sums=('SKIP')

build() {
  cd "$pkgname-$pkgver"
  cargo build --release --locked
}

package() {
  cd "$pkgname-$pkgver"
  install -Dm755 "target/release/$pkgname" "$pkgdir/usr/bin/$pkgname"
  install -Dm644 "LICENSE" "$pkgdir/usr/share/licenses/$pkgname/LICENSE"
}
```

#### **Cargo Binstall**

```bash
# 安装 cargo-binstall
cargo install cargo-binstall

# 快速安装预编译二进制
cargo binstall ripgrep
cargo binstall fd-find
```

---

## 10. Shell 集成

### 10.1 自动补全（bash/zsh/fish）

```rust
use clap::{Command, CommandFactory, Parser};
use clap_complete::{generate, Generator, Shell};
use std::io;

#[derive(Parser)]
#[command(name = "myapp")]
struct Cli {
    /// 生成 shell 补全脚本
    #[arg(long = "generate", value_enum)]
    generator: Option<Shell>,

    // ... 其他参数
}

fn main() {
    let cli = Cli::parse();

    if let Some(generator) = cli.generator {
        let mut cmd = Cli::command();
        print_completions(generator, &mut cmd);
        return;
    }

    // 应用程序逻辑
}

fn print_completions<G: Generator>(gen: G, cmd: &mut Command) {
    generate(gen, cmd, cmd.get_name().to_string(), &mut io::stdout());
}
```

#### **安装补全脚本**

```bash
# Bash（Linux）
myapp --generate bash > /etc/bash_completion.d/myapp
# 或
myapp --generate bash > ~/.local/share/bash-completion/completions/myapp

# Zsh
myapp --generate zsh > /usr/share/zsh/site-functions/_myapp
# 或
myapp --generate zsh > ~/.zfunc/_myapp

# Fish
myapp --generate fish > ~/.config/fish/completions/myapp.fish

# PowerShell
myapp --generate powershell > $PROFILE.CurrentUserAllHosts
```

### 10.2 man page 生成

```rust
use clap::Command;
use clap_mangen::Man;
use std::fs;

fn generate_man_page() -> std::io::Result<()> {
    let cmd = Cli::command();
    let man = Man::new(cmd);

    let mut buffer: Vec<u8> = Default::default();
    man.render(&mut buffer)?;

    fs::write("myapp.1", buffer)?;
    Ok(())
}
```

#### **man page 安装**

```bash
# Linux
sudo cp myapp.1 /usr/share/man/man1/
sudo mandb

# macOS
sudo cp myapp.1 /usr/local/share/man/man1/
```

### 10.3 别名支持

```rust
#[derive(Parser)]
#[command(name = "myapp")]
#[command(alias = "ma")]  // 命令别名
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// 列出项目
    #[command(alias = "ls")]
    List {
        #[arg(short, long, alias = "a")]  // 参数别名
        all: bool,
    },

    /// 显示详情
    #[command(alias = "show")]
    Detail {
        #[arg(value_name = "ID", alias = "i")]
        id: String,
    },
}
```

#### **Shell 别名配置**

```bash
# Bash / Zsh（添加到 ~/.bashrc 或 ~/.zshrc）
alias ma='myapp'
alias mal='myapp list'
alias mas='myapp search'

# 启用补全别名
complete -F _myapp ma
complete -F _myapp mal

# Fish（~/.config/fish/config.fish）
alias ma myapp
alias mal "myapp list"

# PowerShell（$PROFILE）
Set-Alias -Name ma -Value myapp
function mal { myapp list @args }
```

---

## 附录：推荐 crates

| 类别 | crate | 描述 |
|------|-------|------|
| 参数解析 | `clap` | 功能强大的命令行参数解析 |
| 错误处理 | `anyhow` | 简单的错误处理 |
| 错误定义 | `thiserror` | 定义自定义错误类型 |
| 文件遍历 | `walkdir` | 递归目录遍历 |
| Git 感知遍历 | `ignore` | 遵循 .gitignore 的遍历 |
| 正则表达式 | `regex` | 高性能正则表达式 |
| 并行处理 | `rayon` | 数据并行处理 |
| 终端 UI | `ratatui` | 富文本终端用户界面 |
| 终端控制 | `crossterm` | 跨平台终端操作 |
| 进度条 | `indicatif` | 美观的进度条 |
| 颜色输出 | `owo-colors` / `colored` | 终端彩色输出 |
| 日志 | `tracing` | 结构化日志 |
| 序列化 | `serde` | 序列化/反序列化 |
| TOML | `toml` | TOML 处理 |
| 配置目录 | `dirs` | 获取标准目录路径 |
| HTTP 客户端 | `reqwest` | HTTP 请求 |
| 异步运行时 | `tokio` | 异步运行时 |
| 数据库 | `sqlx` | 异步 SQL |
| 测试 | `assert_cmd` / `predicates` | CLI 测试工具 |

---

## 总结

本指南涵盖了使用 Rust 开发 CLI 工具的完整流程：

1. **基础架构**：了解 Rust 在 CLI 开发中的优势，选择合适的 crate
2. **参数解析**：使用 clap 定义命令行接口
3. **终端交互**：实现丰富的终端交互体验
4. **文件系统**：高效处理文件和目录操作
5. **配置管理**：支持多种配置来源
6. **错误处理**：提供清晰的错误信息
7. **日志输出**：实现结构化的日志记录
8. **实际示例**：通过文件搜索工具整合所有概念
9. **分发部署**：打包并发布到各平台
10. **Shell 集成**：提供完善的 Shell 支持

Rust 的强类型系统、零成本抽象和优秀的工具链使其成为 CLI 开发的理想选择。希望本指南能帮助你构建出高性能、可靠且用户友好的命令行工具。

---

*文档版本: 1.0.0*
*最后更新: 2024年*
