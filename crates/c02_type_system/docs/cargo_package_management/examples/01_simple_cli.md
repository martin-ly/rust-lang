# 实战示例：简单 CLI 工具

## 📊 目录

- [实战示例：简单 CLI 工具](#实战示例简单-cli-工具)
  - [📊 目录](#-目录)
  - [📋 项目概述](#-项目概述)
  - [📁 项目结构](#-项目结构)
  - [📝 完整代码](#-完整代码)
    - [Cargo.toml](#cargotoml)
    - [src/main.rs](#srcmainrs)
    - [README.md](#readmemd)
    - [.gitignore](#gitignore)
  - [🚀 构建和运行](#-构建和运行)
    - [开发构建](#开发构建)
    - [发布构建](#发布构建)
  - [🧪 测试](#-测试)
  - [📊 性能分析](#-性能分析)
    - [二进制大小](#二进制大小)
    - [编译时间](#编译时间)
  - [🎯 学习要点](#-学习要点)
    - [1. 依赖选择](#1-依赖选择)
    - [2. Profile 优化](#2-profile-优化)
    - [3. 错误处理](#3-错误处理)
    - [4. 用户体验](#4-用户体验)
  - [🔧 扩展建议](#-扩展建议)
    - [添加配置文件支持](#添加配置文件支持)
    - [添加日志](#添加日志)
    - [添加进度条](#添加进度条)
  - [📚 相关资源](#-相关资源)

**难度**: ⭐⭐
**类型**: 单包应用
**创建日期**: 2025-10-19

---

## 📋 项目概述

这是一个简单的命令行工具示例，展示了：

- 基本项目结构
- 依赖管理
- 命令行参数解析
- 错误处理
- 配置优化

---

## 📁 项目结构

```text
simple-cli/
├── Cargo.toml
├── src/
│   └── main.rs
├── README.md
└── .gitignore
```

---

## 📝 完整代码

### Cargo.toml

```toml
[package]
name = "simple-cli"
version = "0.1.0"
edition = "2024"
rust-version = "1.90"

# 包元数据
description = "A simple CLI tool example"
license = "MIT"
authors = ["Your Name <you@example.com>"]

[[bin]]
name = "scli"
path = "src/main.rs"

[dependencies]
# CLI 参数解析
clap = { version = "4.5", features = ["derive"] }
# 错误处理
anyhow = "1.0"
# 彩色输出
colored = "2.1"

[profile.dev]
opt-level = 1           # 适度优化
incremental = true      # 增量编译

[profile.release]
opt-level = 3           # 最大优化
lto = "fat"             # 全局 LTO
codegen-units = 1       # 单编译单元
strip = true            # 去除符号
panic = "abort"         # Panic 中止

# 优化依赖编译
[profile.dev.package."*"]
opt-level = 2
```

### src/main.rs

```rust
use anyhow::{Context, Result};
use clap::{Parser, Subcommand};
use colored::*;
use std::fs;
use std::path::PathBuf;

/// 简单 CLI 工具 - 文件操作示例
#[derive(Parser)]
#[command(name = "scli")]
#[command(version = "0.1.0")]
#[command(about = "A simple CLI tool", long_about = None)]
struct Cli {
    /// 详细输出
    #[arg(short, long)]
    verbose: bool,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// 读取文件内容
    Read {
        /// 文件路径
        #[arg(value_name = "FILE")]
        path: PathBuf,
    },

    /// 写入文件内容
    Write {
        /// 文件路径
        #[arg(value_name = "FILE")]
        path: PathBuf,

        /// 要写入的内容
        #[arg(value_name = "CONTENT")]
        content: String,
    },

    /// 列出目录内容
    List {
        /// 目录路径
        #[arg(value_name = "DIR", default_value = ".")]
        path: PathBuf,
    },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    if cli.verbose {
        println!("{}", "Running in verbose mode".green());
    }

    match &cli.command {
        Commands::Read { path } => read_file(path, cli.verbose)?,
        Commands::Write { path, content } => write_file(path, content, cli.verbose)?,
        Commands::List { path } => list_directory(path, cli.verbose)?,
    }

    Ok(())
}

/// 读取文件
fn read_file(path: &PathBuf, verbose: bool) -> Result<()> {
    if verbose {
        println!("{} {:?}", "Reading file:".cyan(), path);
    }

    let content = fs::read_to_string(path)
        .with_context(|| format!("Failed to read file: {:?}", path))?;

    println!("{}", "File content:".green().bold());
    println!("{}", content);

    if verbose {
        println!(
            "{} {} bytes",
            "File size:".cyan(),
            content.len()
        );
    }

    Ok(())
}

/// 写入文件
fn write_file(path: &PathBuf, content: &str, verbose: bool) -> Result<()> {
    if verbose {
        println!("{} {:?}", "Writing to file:".cyan(), path);
    }

    fs::write(path, content)
        .with_context(|| format!("Failed to write file: {:?}", path))?;

    println!(
        "{} {}",
        "✓".green().bold(),
        format!("Successfully wrote to {:?}", path).green()
    );

    if verbose {
        println!("{} {} bytes", "Wrote:".cyan(), content.len());
    }

    Ok(())
}

/// 列出目录
fn list_directory(path: &PathBuf, verbose: bool) -> Result<()> {
    if verbose {
        println!("{} {:?}", "Listing directory:".cyan(), path);
    }

    let entries = fs::read_dir(path)
        .with_context(|| format!("Failed to read directory: {:?}", path))?;

    println!("{}", "Directory contents:".green().bold());

    let mut count = 0;
    for entry in entries {
        let entry = entry?;
        let file_type = if entry.file_type()?.is_dir() {
            "[DIR] ".blue()
        } else {
            "[FILE]".normal()
        };

        println!("{} {}", file_type, entry.file_name().to_string_lossy());
        count += 1;
    }

    if verbose {
        println!("\n{} {} items", "Total:".cyan(), count);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_read_file() {
        let mut temp_file = NamedTempFile::new().unwrap();
        writeln!(temp_file, "test content").unwrap();

        let result = read_file(&temp_file.path().to_path_buf(), false);
        assert!(result.is_ok());
    }

    #[test]
    fn test_write_file() {
        let temp_file = NamedTempFile::new().unwrap();
        let path = temp_file.path().to_path_buf();

        let result = write_file(&path, "test content", false);
        assert!(result.is_ok());

        let content = fs::read_to_string(&path).unwrap();
        assert_eq!(content, "test content");
    }
}
```

### README.md

```markdown
# Simple CLI Tool

一个简单的命令行工具示例。

## 功能

- 读取文件
- 写入文件
- 列出目录

## 安装

\`\`\`bash
cargo build --release
\`\`\`

## 使用

### 读取文件
\`\`\`bash
scli read file.txt
scli read file.txt --verbose
\`\`\`

### 写入文件
\`\`\`bash
scli write output.txt "Hello, World!"
\`\`\`

### 列出目录
\`\`\`bash
scli list
scli list /path/to/dir
\`\`\`

## 选项

- `-v, --verbose`: 详细输出
- `-h, --help`: 显示帮助
- `-V, --version`: 显示版本
```

### .gitignore

```text
/target/
Cargo.lock
*.swp
*.swo
*~
.DS_Store
```

---

## 🚀 构建和运行

### 开发构建

```bash
# 构建
cargo build

# 运行
cargo run -- read README.md
cargo run -- list .
cargo run -- write test.txt "Hello, Cargo!"
```

### 发布构建

```bash
# 优化构建
cargo build --release

# 运行优化版本
./target/release/scli --help
./target/release/scli read Cargo.toml
```

---

## 🧪 测试

```bash
# 运行测试（需要添加 tempfile 到 dev-dependencies）
cargo test

# 详细测试输出
cargo test -- --nocapture
```

添加测试依赖：

```toml
[dev-dependencies]
tempfile = "3.12"
```

---

## 📊 性能分析

### 二进制大小

```bash
# 查看大小
ls -lh target/release/scli

# 分析大小构成
cargo install cargo-bloat
cargo bloat --release
```

**预期结果**:

```text
无优化:   ~5.2 MB
优化后:   ~2.8 MB (strip + LTO)
```

### 编译时间

```bash
# 分析编译时间
cargo build --release --timings

# 查看 cargo-timing.html 报告
```

---

## 🎯 学习要点

### 1. 依赖选择

```toml
[dependencies]
clap = { version = "4.5", features = ["derive"] }
# ✓ 使用 derive 特性，简化 CLI 定义
# ✓ 固定主版本，确保兼容性

anyhow = "1.0"
# ✓ 简单错误处理，适合应用程序

colored = "2.1"
# ✓ 彩色输出，提升用户体验
```

### 2. Profile 优化

**开发配置**:

```toml
[profile.dev]
opt-level = 1        # 快速编译 + 适度性能
incremental = true   # 增量编译
```

**发布配置**:

```toml
[profile.release]
opt-level = 3        # 最大优化
lto = "fat"          # 全局优化
strip = true         # 减小体积
```

### 3. 错误处理

```rust
use anyhow::{Context, Result};

fn read_file(path: &PathBuf) -> Result<()> {
    let content = fs::read_to_string(path)
        .with_context(|| format!("Failed to read: {:?}", path))?;
    // ✓ 提供详细错误上下文
    Ok(())
}
```

### 4. 用户体验

```rust
use colored::*;

println!("{}", "Success".green());
println!("{}", "Error".red());
println!("{}", "[DIR]".blue());
// ✓ 彩色输出，提升可读性
```

---

## 🔧 扩展建议

### 添加配置文件支持

```toml
[dependencies]
serde = { version = "1.0", features = ["derive"] }
toml = "0.8"
```

```rust
use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
struct Config {
    default_path: String,
    verbose: bool,
}
```

### 添加日志

```toml
[dependencies]
env_logger = "0.11"
log = "0.4"
```

```rust
use log::{info, error, debug};

fn main() {
    env_logger::init();
    info!("Starting application");
}
```

### 添加进度条

```toml
[dependencies]
indicatif = "0.17"
```

```rust
use indicatif::{ProgressBar, ProgressStyle};

let pb = ProgressBar::new(100);
pb.set_style(ProgressStyle::default_bar()
    .template("[{elapsed_precise}] {bar:40} {pos}/{len}")
    .unwrap());
```

---

## 📚 相关资源

- [clap 文档](https://docs.rs/clap/)
- [anyhow 文档](https://docs.rs/anyhow/)
- [Rust 错误处理](https://doc.rust-lang.org/book/ch09-00-error-handling.html)
- [CLI 最佳实践](../08_最佳实践指南.md)

---

**项目类型**: 单包应用
**适用场景**: CLI 工具、命令行应用
**难度等级**: ⭐⭐ 初级

*这是一个完整可运行的示例，可以直接复制使用！* 🦀🔧
