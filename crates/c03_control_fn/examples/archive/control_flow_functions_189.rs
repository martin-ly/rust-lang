//! Rust 1.89 控制流与函数：综合示例

use c03_control_fn::async_control_flow as acf;
use c03_control_fn::rust_189_enhanced_features::{
    cfg_boolean_literals_189, dangerous_implicit_autorefs_189, invalid_null_arguments_189,
    let_chains_189, naked_functions_189,
};

#[allow(dead_code)]
#[tokio::main]
async fn main() {
    println!("==== Rust 1.89 控制流与函数：综合示例 ====");

    // 基础：项目初始化信息
    c03_control_fn::init();

    // 1) let_chains：用更扁平的条件链替代多层 if let
    let_chains_189::demonstrate_let_chains();
    let_chains_189::demonstrate_nested_let_chains();

    // 2) cfg_boolean_literals：条件编译使用 true/false
    cfg_boolean_literals_189::demonstrate_cfg_boolean_literals();

    // 3) 指针相关安全实践
    dangerous_implicit_autorefs_189::demonstrate_dangerous_implicit_autorefs();
    dangerous_implicit_autorefs_189::demonstrate_safe_pointer_usage();
    invalid_null_arguments_189::demonstrate_invalid_null_arguments();
    invalid_null_arguments_189::demonstrate_safe_pointer_arguments();

    // 4) 裸函数演示（nightly gated，安全打印）
    naked_functions_189::demonstrate_naked_functions();

    // 5) 异步控制流：if/loop/for + 组合器
    let exec = acf::AsyncControlFlowExecutor;
    let value = exec.async_if_else(true, async { 10 }, async { 0 }).await;
    println!("async_if_else -> {}", value);

    let counter = std::rc::Rc::new(std::cell::Cell::new(0));
    let remaining = std::cell::Cell::new(3);
    let counter_c = counter.clone();
    exec.async_loop(
        move || {
            let r = remaining.get();
            if r > 0 {
                // 在条件检查时自增计数并递减剩余次数
                counter_c.set(counter_c.get() + 1);
                remaining.set(r - 1);
                true
            } else {
                false
            }
        },
        std::future::ready(()),
    )
    .await;
    println!("async_loop counter -> {}", counter.get());

    let items = vec![1, 2, 3, 4, 5];
    let processed = exec.async_for(items.clone(), |x| async move { x }).await;
    let sum: i32 = processed.iter().copied().sum();
    println!("async_for sum -> {}", sum);
}
