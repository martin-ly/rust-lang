# CLI 与开发工具场景

> **Bloom 层级**: 应用
> **来源: [Rust CLI Working Group](https://rust-lang.github.io/wg-cli/)** · **[来源: clap crate]** · **来源: [ripgrep](https://github.com/BurntSushi/ripgrep)** · **[来源: hyperfine]** ✅

---

## 场景 1：现代化 CLI 工具

**背景**: 替代传统 Unix 工具（grep/find/ls），提供现代 UX。

**约束**:

- 启动: < 50ms
- 输出: 彩色 + 进度条 + 结构化（JSON）
- 跨平台: Windows PowerShell / macOS zsh / Linux bash

**Rust 方案**:

```rust
use clap::{Parser, Subcommand, ValueEnum};
use anyhow::Result;
use indicatif::{ProgressBar, ProgressStyle};
use comfy_table::{Table, ContentArrangement};

#[derive(Parser)]
#[command(name = "mytool")]
#[command(about = "A modern CLI tool", long_about = None)]
struct Cli {
    #[arg(short, long, value_enum, default_value_t = OutputFormat::Table)]
    format: OutputFormat,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum OutputFormat {
    Table,
    Json,
    Csv,
}

#[derive(Subcommand)]
enum Commands {
    List { pattern: Option<String> },
    Search { query: String, path: String },
}

fn main() -> Result<()> {
    let cli = Cli::parse();

    match cli.command {
        Commands::List { pattern } => {
            let pb = ProgressBar::new(100);
            pb.set_style(ProgressStyle::default_bar()
                .template("{spinner:.green} [{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} {msg}")?);

            // 处理...
            pb.finish_with_message("Done");
        }
        Commands::Search { query, path } => {
            let results = search(&query, &path)?;
            match cli.format {
                OutputFormat::Table => print_table(&results),
                OutputFormat::Json => println!("{}", serde_json::to_string_pretty(&results)?),
                OutputFormat::Csv => print_csv(&results)?,
            }
        }
    }

    Ok(())
}
```
**关键决策**:

- CLI: `clap` v4（derive 宏，自动 help/completion）
- 错误: `anyhow`（用户友好）+ `thiserror`（库开发）
- 输出: `comfy-table` + `indicatif` + `owo-colors`
- 配置: `serde` + `toml` / `dirs`（跨平台配置目录）

---

## 场景 2：代码分析工具（AST 遍历）

**背景**: 自定义 linter，检查团队编码规范。

**Rust 方案**:

```rust
use syn::{visit::Visit, File, ItemFn, ReturnType};
use quote::quote;

struct FnVisitor {
    errors: Vec<String>,
}

impl<'ast> Visit<'ast> for FnVisitor {
    fn visit_item_fn(&mut self, node: &'ast ItemFn) {
        // 规则：公开函数必须有文档注释
        if node.vis.to_token_stream().to_string().contains("pub") {
            let has_doc = node.attrs.iter().any(|attr| attr.path().is_ident("doc"));
            if !has_doc {
                self.errors.push(format!(
                    "{}: 公开函数缺少文档注释",
                    node.sig.ident
                ));
            }
        }

        // 规则：返回 Result 的函数应使用 #[must_use]
        if let ReturnType::Type(_, ty) = &node.sig.output {
            let ty_str = quote!(#ty).to_string();
            if ty_str.contains("Result") {
                let has_must_use = node.attrs.iter().any(|attr| attr.path().is_ident("must_use"));
                if !has_must_use {
                    self.errors.push(format!(
                        "{}: Result 返回类型缺少 #[must_use]",
                        node.sig.ident
                    ));
                }
            }
        }
    }
}

fn lint_file(source: &str) -> Vec<String> {
    let syntax: File = syn::parse_str(source).unwrap();
    let mut visitor = FnVisitor { errors: vec![] };
    visitor.visit_file(&syntax);
    visitor.errors
}
```
**关键决策**:

- AST 解析: `syn`（Rust 官方 proc-macro 生态）
- 代码生成: `quote`
- 遍历: `syn::visit` trait

---

## 场景 3：性能基准测试框架

**背景**: 替代 `time` 命令，提供统计显著的性能对比。

**Rust 方案**:

```rust
use std::time::{Duration, Instant};
use statrs::statistics::Statistics;

fn benchmark<F>(name: &str, f: F, iterations: usize)
where
    F: Fn(),
{
    let mut times = Vec::with_capacity(iterations);

    // 预热
    for _ in 0..10 { f(); }

    // 正式测试
    for _ in 0..iterations {
        let start = Instant::now();
        f();
        times.push(start.elapsed().as_secs_f64() * 1000.0); // ms
    }

    let mean = times.mean();
    let std_dev = times.std_dev();
    let min = times.iter().cloned().fold(f64::INFINITY, f64::min);
    let max = times.iter().cloned().fold(f64::NEG_INFINITY, f64::max);

    println!(
        "{}: {:.3} ms ± {:.3} ms (min: {:.3}, max: {:.3})",
        name, mean, std_dev, min, max
    );
}
```
**关键决策**:

- 工具: `hyperfine`（命令行）或 `criterion`（库）
- 统计: `statrs` 或内置统计
- 报告: JSON 输出供 CI 趋势分析

---

## 推荐工具箱

| 功能 | Crate | 说明 |
|:---|:---|:---|
| CLI 解析 | `clap` | 最强大的 derive 宏 CLI |
| 错误处理 | `anyhow` / `thiserror` |  ergonomic 错误链 |
| 输出颜色 | `owo-colors` / `console` | 跨平台 ANSI |
| 进度条 | `indicatif` | 多进度、速率显示 |
| 表格 | `comfy-table` / `tabled` | 自适应列宽 |
| 交互式 | `dialoguer` / `inquire` | 提示、选择、确认 |
| 日志 | `tracing` / `env_logger` | 结构化日志 |
| 配置 | `serde` + `toml` | 类型安全配置 |
| 文件系统 | `walkdir` / `ignore` | 递归遍历、gitignore 支持 |
| 正则 | `regex` | 高性能正则 |

---

> **文档版本**: 1.0
> **最后更新**: 2026-05-21
> **状态**: ✅ 初版完成
