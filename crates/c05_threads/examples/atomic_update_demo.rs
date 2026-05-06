//! Rust 1.95.0 `Atomic*::update` / `try_update` 专题示例
//!
//! Rust 1.95.0 稳定化了原子类型的 `update` 和 `try_update` 方法，
//! 封装了 CAS（Compare-And-Swap）循环，让无锁并发代码更安全、更易读。
//!
//! 权威来源: https://releases.rs/docs/1.95.0/
//!
//! 运行方式:
//! ```bash
//! cargo run --example atomic_update_demo -p c05_threads
//! ```

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicI32, AtomicPtr, AtomicUsize, Ordering};
use std::thread;

// ==================== 示例 1: AtomicUsize::update ====================

/// 使用 `update` 原子递增计数器
///
/// `update` 会重试 CAS 直到成功，内部是一个自旋循环。
fn demo_atomic_usize_update() {
    println!("--- AtomicUsize::update ---");

    let counter = AtomicUsize::new(5);

    // update: 重试直到成功，返回旧值
    let old = counter.update(Ordering::Relaxed, Ordering::Relaxed, |current| current + 1);

    println!("  旧值: {}, 新值: {}", old, counter.load(Ordering::Relaxed));
    assert_eq!(old, 5);
    assert_eq!(counter.load(Ordering::Relaxed), 6);
}

// ==================== 示例 2: AtomicUsize::try_update ====================

/// 使用 `try_update` 条件性原子更新
///
/// `try_update` 只尝试一次 CAS，如果条件不满足或并发冲突则返回 Err。
fn demo_atomic_usize_try_update() {
    println!("\n--- AtomicUsize::try_update ---");

    let counter = AtomicUsize::new(5);

    // try_update: 尝试一次，成功返回 Ok(旧值)
    let result = counter.try_update(Ordering::Relaxed, Ordering::Relaxed, |current| {
        if current < 10 {
            Some(current + 1)
        } else {
            None // 条件不满足，放弃更新
        }
    });
    println!("  第一次 try_update: {:?}", result);
    assert!(result.is_ok());

    // 再次尝试，仍然满足条件
    let result2 = counter.try_update(Ordering::Relaxed, Ordering::Relaxed, |current| {
        if current < 10 {
            Some(current + 1)
        } else {
            None
        }
    });
    println!("  第二次 try_update: {:?}", result2);
    assert!(result2.is_ok());
    assert_eq!(counter.load(Ordering::Relaxed), 7);
}

// ==================== 示例 3: AtomicBool::update / try_update ====================

/// 原子布尔翻转
fn demo_atomic_bool_update() {
    println!("\n--- AtomicBool::update / try_update ---");

    let flag = AtomicBool::new(false);

    // 原子翻转
    let old = flag.update(Ordering::SeqCst, Ordering::SeqCst, |current| !current);
    println!("  翻转前: {}, 翻转后: {}", old, flag.load(Ordering::SeqCst));
    assert_eq!(old, false);
    assert!(flag.load(Ordering::SeqCst));

    // try_update: 仅在当前为 true 时设为 false
    let result = flag.try_update(Ordering::SeqCst, Ordering::SeqCst, |current| {
        if current { Some(false) } else { None }
    });
    println!("  尝试清零: {:?}", result);
    assert!(result.is_ok());
    assert!(!flag.load(Ordering::SeqCst));
}

// ==================== 示例 4: AtomicI32::update — 有界累加 ====================

/// 使用 `update` 实现有界累加器（饱和语义）
fn demo_atomic_i32_saturating() {
    println!("\n--- AtomicI32::update (饱和累加) ---");

    let value = AtomicI32::new(90);
    const MAX: i32 = 100;

    // 尝试加 20，但饱和到 MAX
    let old = value.update(Ordering::Relaxed, Ordering::Relaxed, |current| {
        current.saturating_add(20).min(MAX)
    });

    println!(
        "  旧值: {}, 新值: {} (上限 {})",
        old,
        value.load(Ordering::Relaxed),
        MAX
    );
    assert_eq!(old, 90);
    assert_eq!(value.load(Ordering::Relaxed), 100);
}

// ==================== 示例 5: AtomicPtr::update / try_update ====================

/// 原子指针更新：实现无锁栈节点推进
fn demo_atomic_ptr_update() {
    println!("\n--- AtomicPtr::update / try_update ---");

    let mut node_b = Box::new(2);
    let mut node_a = Box::new(1);

    let ptr_b: *mut i32 = &mut *node_b;
    let ptr_a: *mut i32 = &mut *node_a;

    let head = AtomicPtr::new(ptr_a);

    // 将 head 从 node_a 更新为 node_b
    let old = head.update(Ordering::SeqCst, Ordering::SeqCst, |_current| ptr_b);

    println!(
        "  旧指针: {:p}, 新指针: {:p}",
        old,
        head.load(Ordering::SeqCst)
    );
    assert_eq!(old, ptr_a);
    assert_eq!(head.load(Ordering::SeqCst), ptr_b);

    // try_update: 尝试再次替换（仅用于演示语义）
    let result = head.try_update(Ordering::SeqCst, Ordering::SeqCst, |_current| {
        Some(ptr_a) // 无条件替换回 ptr_a
    });
    println!("  尝试替换回旧指针: {:?}", result);
    assert!(result.is_ok());

    // 安全：我们知道这些指针来自 Box，且在此作用域内有效
    unsafe {
        assert_eq!(*head.load(Ordering::SeqCst), 1);
    }
}

// ==================== 示例 6: 多线程竞争 — update vs 手动 CAS ====================

/// 对比 `update` 与手动 CAS 循环的等价性
fn demo_multi_thread_update() {
    println!("\n--- 多线程 AtomicUsize::update ---");

    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let c = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            for _ in 0..1000 {
                // update 内部自动处理 CAS 重试
                c.update(Ordering::Relaxed, Ordering::Relaxed, |v| v + 1);
            }
        });
        handles.push(handle);
    }

    for h in handles {
        h.join().unwrap();
    }

    println!(
        "  10 线程 × 1000 次递增 = {}",
        counter.load(Ordering::Relaxed)
    );
    assert_eq!(counter.load(Ordering::Relaxed), 10_000);
}

// ==================== 示例 7: try_update 的失败处理 ====================

/// 演示 `try_update` 在并发场景下的失败情况
fn demo_try_update_race_condition() {
    println!("\n--- AtomicUsize::try_update 并发竞争 ---");

    let counter = Arc::new(AtomicUsize::new(0));
    let mut handles = vec![];

    for _ in 0..4 {
        let c = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut successes = 0;
            let mut failures = 0;
            for _ in 0..100 {
                match c.try_update(Ordering::Relaxed, Ordering::Relaxed, |v| Some(v + 1)) {
                    Ok(_) => successes += 1,
                    Err(_) => failures += 1,
                }
            }
            (successes, failures)
        });
        handles.push(handle);
    }

    let mut total_successes = 0;
    let mut total_failures = 0;
    for h in handles {
        let (s, f) = h.join().unwrap();
        total_successes += s;
        total_failures += f;
    }

    println!(
        "  总尝试: {}, 成功: {}, 失败: {}",
        total_successes + total_failures,
        total_successes,
        total_failures
    );
    // 最终计数应等于成功次数
    assert_eq!(counter.load(Ordering::Relaxed), total_successes);
}

// ==================== 主演示函数 ====================

fn main() {
    println!("🦀 Rust 1.95.0 `Atomic*::update` / `try_update` 专题演示\n");
    println!("说明: update = 自动重试 CAS; try_update = 只试一次\n");

    demo_atomic_usize_update();
    demo_atomic_usize_try_update();
    demo_atomic_bool_update();
    demo_atomic_i32_saturating();
    demo_atomic_ptr_update();
    demo_multi_thread_update();
    demo_try_update_race_condition();

    println!("\n✅ `Atomic*::update` / `try_update` 演示完成！");
    println!("   关键要点:");
    println!("   - update:   封装 CAS 循环，自动重试直到成功，返回旧值");
    println!("   - try_update: 只尝试一次 CAS，成功返回 Ok(旧值)，失败返回 Err(当前值)");
    println!("   - 两者都比手动 load + compare_exchange 循环更安全、更易读");
}
