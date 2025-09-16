//! 同步原语演示程序
//!
//! 本程序展示Rust中各种同步原语的使用，包括：
//! - Mutex 互斥锁
//! - 条件变量
//! - 原子操作
//! - 读写锁

use c05_threads::synchronization::mutex::*;

fn main() {
    println!("🔒 Rust 同步原语演示");
    println!("========================\n");

    // 1. 基本Mutex使用
    println!("📋 1. 基本Mutex使用");
    println!("----------------------");
    basic_mutex_usage();
    println!();

    // 2. 共享复杂数据结构
    println!("📋 2. 共享复杂数据结构");
    println!("----------------------");
    shared_complex_data();
    println!();

    // 3. 死锁预防
    println!("📋 3. 死锁预防");
    println!("----------------------");
    deadlock_prevention();
    println!();

    // 4. try_lock示例
    println!("📋 4. try_lock示例");
    println!("----------------------");
    try_lock_example();
    println!();

    // 5. Mutex与条件变量
    println!("📋 5. Mutex与条件变量");
    println!("----------------------");
    mutex_with_condition();
    println!();

    // 6. 锁优化
    println!("📋 6. 锁优化");
    println!("----------------------");
    lock_optimization();
    println!();

    // 7. 自定义Mutex包装器
    println!("📋 7. 自定义Mutex包装器");
    println!("----------------------");
    custom_mutex_wrapper();
    println!();

    println!("✅ 同步原语演示完成！");
}
