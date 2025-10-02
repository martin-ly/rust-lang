//! 异步理论综合示例
//!
//! 运行所有理论分析模块的完整演示
//!
//! 用法:
//! ```bash
//! cargo run --example async_theory_comprehensive
//! ```

use c06_async::{
    async_semantics_theory, async_recursion_analysis, actor_reactor_patterns, csp_model_comparison,
};

#[tokio::main]
async fn main() {
    println!("\n");
    println!("╔════════════════════════════════════════════════════════════════╗");
    println!("║                                                                ║");
    println!("║       Rust 异步编程理论与实践 - 全面综合示例                  ║");
    println!("║       Comprehensive Rust Async Theory & Practice              ║");
    println!("║                                                                ║");
    println!("║       Rust 1.90 Edition - 2025                                 ║");
    println!("║                                                                ║");
    println!("╚════════════════════════════════════════════════════════════════╝");
    println!("\n");

    println!("本示例将依次演示：");
    println!("  1. 异步语义理论 (Async Semantics Theory)");
    println!("  2. 异步递归分析 (Async Recursion Analysis)");
    println!("  3. Actor/Reactor 模式 (Actor & Reactor Patterns)");
    println!("  4. CSP 模型对比 (CSP Model Comparison)");
    println!("\n按 Enter 继续...");

    let mut input = String::new();
    std::io::stdin().read_line(&mut input).unwrap();

    // ========================================================================
    // 第一部分: 异步语义理论
    // ========================================================================
    async_semantics_theory::run_all_examples().await;

    println!("\n第一部分完成。按 Enter 继续...");
    let mut input = String::new();
    std::io::stdin().read_line(&mut input).unwrap();

    // ========================================================================
    // 第二部分: 异步递归分析
    // ========================================================================
    async_recursion_analysis::run_all_examples().await;

    println!("\n第二部分完成。按 Enter 继续...");
    let mut input = String::new();
    std::io::stdin().read_line(&mut input).unwrap();

    // ========================================================================
    // 第三部分: Actor/Reactor 模式
    // ========================================================================
    actor_reactor_patterns::run_all_examples().await;

    println!("\n第三部分完成。按 Enter 继续...");
    let mut input = String::new();
    std::io::stdin().read_line(&mut input).unwrap();

    // ========================================================================
    // 第四部分: CSP 模型对比
    // ========================================================================
    csp_model_comparison::run_all_examples().await;

    // ========================================================================
    // 总结
    // ========================================================================
    println!("\n");
    println!("╔════════════════════════════════════════════════════════════════╗");
    println!("║                   全部示例执行完成！                           ║");
    println!("╚════════════════════════════════════════════════════════════════╝");
    println!("\n");

    println!("您已完成以下学习内容：\n");

    println!("✓ 异步语义理论");
    println!("  - Future 状态机的形式化定义");
    println!("  - Monad 法则验证");
    println!("  - 同步与异步的等价关系");
    println!("  - CPS 变换");
    println!("  - 控制流分析\n");

    println!("✓ 异步递归分析");
    println!("  - 异步递归的实现技术");
    println!("  - 尾递归优化");
    println!("  - 递归与迭代的等价转换");
    println!("  - 树遍历算法");
    println!("  - 互递归模式\n");

    println!("✓ Actor/Reactor 模式");
    println!("  - Actor 模型的形式化");
    println!("  - Reactor 事件循环");
    println!("  - Tokio 架构分析");
    println!("  - Actix 框架特性");
    println!("  - 两种模式的对比\n");

    println!("✓ CSP 模型对比");
    println!("  - Rust vs Golang 并发模型");
    println!("  - Channel 语义对比");
    println!("  - 生产者-消费者模式");
    println!("  - Worker Pool 模式");
    println!("  - Pipeline 模式\n");

    println!("建议下一步学习：");
    println!("  1. 阅读各模块的源代码注释");
    println!("  2. 运行单独的示例: cargo run --example <name>");
    println!("  3. 查看 src/ 目录中的实现细节");
    println!("  4. 尝试修改示例并观察结果");
    println!("\n");
}

