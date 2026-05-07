#![allow(unused)]

//! # Cargo Script 单文件脚本演示
//!
//! **版本 attribution**: Rust 1.79+ 稳定化，Rust 1.95+ 持续增强
//!
//! Cargo Script 允许在单个 `.rs` 文件中编写完整 Rust 程序并直接嵌入依赖，
//! 无需 `Cargo.toml` 或完整项目目录结构。
//!
//! ## 核心概念
//!
//! - **单文件可执行**: 将源码、依赖清单、元数据合并到一个文件。
//! - **嵌入式 manifest**: 使用 frontmatter 或代码块声明 `dependencies`。
//! - **即时运行**: 通过 `cargo` 或 `rust-script` 直接执行，享受自动缓存。
//!
//! ## 运行方式概览
//!
//! ```bash
//! # 方式 A: cargo 原生支持 (Rust 1.79+)
//! cargo run --manifest-path script.rs
//!
//! # 方式 B: nightly 实验标志 (旧习惯)
//! cargo +nightly -Zscript script.rs
//!
//! # 方式 C: 第三方 rust-script 工具
//! cargo install rust-script
//! rust-script script.rs
//! ```
//!
//! ## 文件格式对比
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │  cargo-script (原生)        │  rust-script (社区)            │
//! ├─────────────────────────────────────────────────────────────┤
//! │  #!/usr/bin/env cargo        │  #!/usr/bin/env rust-script    │
//! │  ```cargo                     │  ---                           │
//! │  [dependencies]               │  dependencies:                 │
//! │  serde = "1"                  │    serde = "1"                 │
//! │  ```                          │  ---                           │
//! └─────────────────────────────────────────────────────────────┘
//! ```
//!
//! > 注：本文件为**教学文档**，所有 cargo-script 特有语法均使用 `//` 注释展示，
//! > 以保证在 stable toolchain 下可通过 `cargo check --examples` 编译。

// ============================================================================
// 1. Shebang 语法
// ============================================================================

// 在 Unix/Linux/macOS 上，可在文件首行添加 shebang，使其可直接执行：
//
//     #!/usr/bin/env cargo
//
// 添加执行权限后：
//     chmod +x cargo_script_demo.rs
//     ./cargo_script_demo.rs
//
// Windows 不支持 shebang，请使用：
//     cargo run --manifest-path cargo_script_demo.rs

// ============================================================================
// 2. Frontmatter 语法（--- 块）
// ============================================================================

// `rust-script` 风格的 frontmatter 使用 `---` 包裹 YAML 格式的包元数据：
//
//     ---
//     [package]
//     name = "quick-cli"
//     version = "0.1.0"
//     edition = "2021"
//
//     [dependencies]
//     clap = { version = "4", features = ["derive"] }
//     serde = { version = "1", features = ["derive"] }
//     serde_json = "1"
//     ---
//
// 原生 cargo-script 则使用 Markdown 代码块 `` ```cargo `` 包裹 TOML：
//
//     ```cargo
//     [dependencies]
//     clap = "4"
//     chrono = "0.4"
//     ```
//
// 两种写法都无需额外的 Cargo.toml 文件。

// ============================================================================
// 3. 实践示例 A：快速 CLI 工具
// ============================================================================

// 以下是一个概念性的 quick CLI 工具示例（注释展示）：
//
//     ```cargo
//     [dependencies]
//     clap = { version = "4", features = ["derive"] }
//     ```
//
//     use clap::Parser;
//
//     #[derive(Parser)]
//     struct Args {
//         #[arg(short, long)]
//         name: String,
//     }
//
//     fn main() {
//         let args = Args::parse();
//         println!("Hello, {}!", args.name);
//     }

/// 占位：quick CLI 概念函数
fn _quick_cli_concept() {
    // 实际使用时，上述代码可直接放入单文件并运行。
}

// ============================================================================
// 4. 实践示例 B：数据处理脚本
// ============================================================================

// 读取 JSON Lines，过滤并输出统计信息：
//
//     ```cargo
//     [dependencies]
//     serde = { version = "1", features = ["derive"] }
//     serde_json = "1"
//     ```
//
//     use serde::Deserialize;
//
//     #[derive(Deserialize)]
//     struct Record { age: u32, city: String }
//
//     fn main() {
//         let stdin = std::io::read_to_string(std::io::stdin()).unwrap();
//         let mut total = 0;
//         for line in stdin.lines() {
//             if let Ok(r) = serde_json::from_str::<Record>(line) {
//                 if r.city == "Beijing" {
//                     total += r.age;
//                 }
//             }
//         }
//         println!("Total age in Beijing: {}", total);
//     }

/// 占位：data processing 概念函数
fn _data_processing_concept() {}

// ============================================================================
// 5. 实践示例 C：API 测试脚本
// ============================================================================

// 使用 reqwest 发送 GET 请求并断言状态码：
//
//     ```cargo
//     [dependencies]
//     reqwest = { version = "0.12", features = ["blocking"] }
//     ```
//
//     fn main() -> Result<(), Box<dyn std::error::Error>> {
//         let resp = reqwest::blocking::get("https://api.github.com/users/rust-lang")?;
//         println!("Status: {}", resp.status());
//         assert!(resp.status().is_success());
//         Ok(())
//     }

/// 占位：API test 概念函数
fn _api_test_concept() {}

// ============================================================================
// 6. 与传统 `cargo new` 的对比
// ============================================================================

// | 维度               | cargo new 项目            | cargo-script 单文件         |
// |--------------------|--------------------------|----------------------------|
// | 启动成本            | 需要创建目录 + Cargo.toml | 单文件即可                  |
// | 依赖管理            | 集中式 Cargo.toml         | 嵌入式 frontmatter          |
// | 版本控制            | 适合 Git 管理多文件        | 适合 gist / 快速分享         |
// | 缓存/编译           | 完整的 target/ 目录        | 自动缓存到 ~/.cargo/        |
// | 适用场景            | 大型项目、库开发            | 脚本、原型、CI 辅助           |
// | 多文件模块          | ✅ 支持 `mod foo;`         | ❌ 仅单文件（截至 1.95）     |

// Mermaid 流程图：选择工作流
//
// ```mermaid
// flowchart TD
//     A[需要写 Rust 代码?] --> B{任务规模}
//     B -->|大型项目 / 库| C[cargo new my_project]
//     B -->|脚本 / 原型 / 单文件工具| D[cargo script / rust-script]
//     C --> E[完整目录结构<br/>Cargo.toml + src/]
//     D --> F[单 .rs 文件<br/>嵌入依赖与元数据]
// ```

// ============================================================================
// 7. 当前限制与最佳实践
// ============================================================================

// - **单文件限制**: 截至 Rust 1.95，cargo-script 不支持 `mod foo;` 多文件拆分。
// - **工作区依赖**: 不支持 `workspace = true`，需显式声明版本或 path。
// - **构建脚本**: 不支持 `build.rs`，需要 build script 时请使用传统项目。
// - **缓存**: 首次运行会下载依赖并编译，后续运行直接命中缓存。
// - **CI 集成**: 可在 GitHub Actions 中直接 `cargo run --manifest-path script.rs`。

fn main() {
    println!("🦀 这是一个 cargo-script 教学文件。");
    println!("请阅读源码中的注释以了解 cargo-script 的完整用法。");
    println!("版本: Rust 1.95+ (cargo-script 自 1.79 起稳定化)");
}
