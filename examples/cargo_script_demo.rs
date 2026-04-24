#!/usr/bin/env cargo
```cargo
[dependencies]
clap = { version = "4", features = ["derive"] }
chrono = "0.4"
```
//! # Cargo Script 单文件脚本演示
//!
//! 本文件演示 Rust 的 `cargo script` 功能（自 Rust 1.79 起稳定化）。
//! 允许在单个 `.rs` 文件中直接嵌入 Cargo 依赖清单，无需创建完整项目。
//!
//! ## 运行方式
//!
//! ```bash
//! # 方式 1: 直接执行 (需要 Rust 1.79+)
//! cargo +nightly -Zscript cargo_script_demo.rs
//!
//! # 方式 2: 作为可执行脚本 (Unix/Linux/macOS)
//! chmod +x cargo_script_demo.rs
//! ./cargo_script_demo.rs
//!
//! # 方式 3: 使用 cargo-run-script (第三方工具)
//! cargo install cargo-run-script
//! cargo run-script cargo_script_demo.rs
//! ```
//!
//! ## 文件格式说明
//!
//! 1. 首行必须是 shebang: `#!/usr/bin/env cargo`
//! 2. 紧接着是 cargo 清单块，用 ` ```cargo ` 包裹
//! 3. 清单块内使用标准 Cargo.toml 语法
//! 4. 之后是正常的 Rust 代码

use clap::Parser;
use chrono::Local;

/// 命令行参数定义
#[derive(Parser, Debug)]
#[command(name = "cargo-script-demo")]
#[command(about = "Cargo Script 功能演示")]
#[command(version = "1.0.0")]
struct Args {
    /// 要问候的名字
    #[arg(short, long, default_value = "World")]
    name: String,

    /// 重复次数
    #[arg(short, long, default_value_t = 1)]
    count: u32,

    /// 是否显示时间
    #[arg(long, default_value_t = true)]
    time: bool,
}

fn main() {
    let args = Args::parse();

    println!("╔══════════════════════════════════════╗");
    println!("║      🦀 Cargo Script 演示程序        ║");
    println!("╚══════════════════════════════════════╝");
    println!();

    if args.time {
        let now = Local::now();
        println!("📅 当前时间: {}", now.format("%Y-%m-%d %H:%M:%S"));
        println!();
    }

    for i in 1..=args.count {
        println!("{}. Hello, {}! 🎉", i, args.name);
    }

    println!();
    println!("✅ Cargo Script 运行成功!");
    println!();
    println!("💡 提示: cargo script 适合以下场景:");
    println!("   • 快速原型验证");
    println!("   • 一次性数据处理脚本");
    println!("   • 系统管理工具");
    println!("   • 学习/教学示例");
}

/// 演示模块: 展示 cargo script 中也可以定义普通函数和测试
fn add(a: i32, b: i32) -> i32 {
    a + b
}

/// 计算斐波那契数列第 n 项 (简单递归实现，仅用于演示)
fn fibonacci(n: u32) -> u64 {
    match n {
        0 => 0,
        1 => 1,
        _ => fibonacci(n - 1) + fibonacci(n - 2),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add() {
        assert_eq!(add(2, 3), 5);
        assert_eq!(add(-1, 1), 0);
    }

    #[test]
    fn test_fibonacci() {
        assert_eq!(fibonacci(0), 0);
        assert_eq!(fibonacci(1), 1);
        assert_eq!(fibonacci(10), 55);
    }
}
