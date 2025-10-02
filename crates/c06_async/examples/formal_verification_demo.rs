//! 形式化验证演示
//!
//! 展示异步编程中的形式化验证技术
//!
//! 用法:
//! ```bash
//! cargo run --example formal_verification_demo
//! ```

use c06_async::formal_verification;

#[tokio::main]
async fn main() {
    println!("\n");
    println!("╔════════════════════════════════════════════════════════════════╗");
    println!("║                                                                ║");
    println!("║       Rust 异步编程形式化验证演示                              ║");
    println!("║       Formal Verification for Async Rust                      ║");
    println!("║                                                                ║");
    println!("╚════════════════════════════════════════════════════════════════╝");
    println!("\n");

    // 运行所有验证示例
    formal_verification::run_all_verifications().await;

    println!("\n形式化验证演示完成！\n");
    println!("学习要点:");
    println!("  1. 不变式 (Invariants) - 程序执行过程中保持的性质");
    println!("  2. 前后条件 (Pre/Post-conditions) - Hoare 逻辑");
    println!("  3. 终止性 (Termination) - 度量函数证明");
    println!("  4. 死锁检测 (Deadlock Detection) - 资源分配图");
    println!();
}

