//!
//! 权威来源: https://releases.rs/docs/1.95.0/
//! 权威source: https://releases.rs/docs/1.95.0/
//! 运行方式:
//! Run way :
//! cargo run --example collections_mut_ref_demo -p c08_algorithms
//! ```

use std::collections::{LinkedList, VecDeque};

// ==================== 示例 1: VecDeque::push_front_mut / push_back_mut ====================

/// 双端队列两端插入并立即修改
/// and
fn demo_vecdeque_push_mut() {
    println!("--- VecDeque::push_front_mut / push_back_mut ---");

    let mut deque: VecDeque<String> = VecDeque::new();

    // 前端插入并获取可变引用
    let front = deque.push_front_mut("hello".to_string());
    front.push_str(" world");
    println!("  push_front_mut 后: {:?}", deque);

    // 后端插入并获取可变引用
    let back = deque.push_back_mut("rust".to_string());
    back.push_str(" 1.95");
    println!("  push_back_mut 后: {:?}", deque);

    assert_eq!(deque[0], "hello world");
    assert_eq!(deque[1], "rust 1.95");
}

// ==================== 示例 2: VecDeque::insert_mut ====================

/// 在双端队列指定位置插入并修改
/// in position and
fn demo_vecdeque_insert_mut() {
    println!("\n--- VecDeque::insert_mut ---");

    let mut deque: VecDeque<i32> = VecDeque::from([1, 3, 4]);

    // 在索引 1 处插入占位符并修改
    let elem = deque.insert_mut(1, 0);
    *elem = 2; // 修正为正确值

    println!("  insert_mut 后: {:?}", deque);
    assert_eq!(deque.into_iter().collect::<Vec<_>>(), [1, 2, 3, 4]);
}

// ==================== 示例 3: VecDeque 作为滑动窗口缓存 ====================

fn demo_vecdeque_cache() {
    println!("\n--- VecDeque::push_back_mut 滑动窗口缓存 ---");

    #[derive(Debug)]
    struct CacheEntry {
        key: u64,
        value: String,
        hits: u32,
    }

    let mut cache: VecDeque<CacheEntry> = VecDeque::with_capacity(5);

    for i in 1..=4 {
        let entry = cache.push_back_mut(CacheEntry {
            key: i,
            value: format!("data-{}", i),
            hits: 0,
        });
        // 模拟首次访问即命中
        entry.hits = 1;
    }

    println!("  缓存条目:");
    for e in &cache {
        println!("    key={}, value={}, hits={}", e.key, e.value, e.hits);
    }

    assert_eq!(cache.iter().map(|e| e.hits).sum::<u32>(), 4);
}

// ==================== 示例 4: LinkedList::push_front_mut / push_back_mut ====================

/// 链表两端插入并立即修改
/// and
fn demo_linkedlist_push_mut() {
    println!("\n--- LinkedList::push_front_mut / push_back_mut ---");

    let mut list: LinkedList<Vec<u8>> = LinkedList::new();

    // 前端插入空 Vec 并填充
    let front = list.push_front_mut(Vec::with_capacity(4));
    front.extend_from_slice(&[0xDE, 0xAD]);
    println!("  push_front_mut 后: {:?}", front);

    // 后端插入空 Vec 并填充
    let back = list.push_back_mut(Vec::with_capacity(4));
    back.extend_from_slice(&[0xBE, 0xEF]);
    println!("  push_back_mut 后: {:?}", back);

    // 验证链表内容
    let collected: Vec<_> = list.iter().cloned().collect();
    println!("  链表内容: {:?}", collected);
    assert_eq!(collected, vec![vec![0xDE, 0xAD], vec![0xBE, 0xEF]]);
}

// ==================== 示例 5: LinkedList 构建日志缓冲区 ====================

/// 使用 `push_back_mut` 构建结构化日志链表
/// `push_back_mut` structure
fn demo_linkedlist_log_buffer() {
    println!("\n--- LinkedList::push_back_mut 日志缓冲区 ---");

    #[derive(Debug, PartialEq)]
    struct LogEntry {
        timestamp: u64,
        level: &'static str,
        message: String,
    }

    let mut logs: LinkedList<LogEntry> = LinkedList::new();

    // 插入并立即完善日志条目
    let entry = logs.push_back_mut(LogEntry {
        timestamp: 0,
        level: "INFO",
        message: String::new(),
    });
    entry.timestamp = 1_700_000_000;
    entry.message.push_str("System initialized");

    let entry = logs.push_back_mut(LogEntry {
        timestamp: 0,
        level: "WARN",
        message: String::new(),
    });
    entry.timestamp = 1_700_000_001;
    entry.message.push_str("High memory usage detected");

    println!("  日志条目:");
    for log in &logs {
        println!("    [{}] {}: {}", log.timestamp, log.level, log.message);
    }

    assert_eq!(logs.len(), 2);
}

// ==================== 示例 6: 对比 VecDeque 与 LinkedList 的 push_mut ====================

fn demo_comparison() {
    println!("\n--- VecDeque vs LinkedList push_*_mut 对比 ---");

    let mut vd: VecDeque<i32> = VecDeque::new();
    let mut ll: LinkedList<i32> = LinkedList::new();

    // VecDeque
    let r1 = vd.push_front_mut(10);
    *r1 += 1;
    let r2 = vd.push_back_mut(20);
    *r2 += 1;
    let vd_result: Vec<_> = vd.iter().copied().collect();
    println!("  VecDeque: {:?}", vd_result);

    // LinkedList
    let r1 = ll.push_front_mut(10);
    *r1 += 1;
    let r2 = ll.push_back_mut(20);
    *r2 += 1;
    let ll_result: Vec<_> = ll.iter().copied().collect();
    println!("  LinkedList: {:?}", ll_result);

    // 两者结果一致
    assert_eq!(vd_result, ll_result);
}

// ==================== 主演示函数 ====================

fn main() {
    println!("🦀 Rust 1.95.0 `VecDeque` / `LinkedList` `push_*_mut` 专题演示\n");

    demo_vecdeque_push_mut();
    demo_vecdeque_insert_mut();
    demo_vecdeque_cache();
    demo_linkedlist_push_mut();
    demo_linkedlist_log_buffer();
    demo_comparison();

    println!("\n✅ `VecDeque` / `LinkedList` `push_*_mut` 演示完成！");
    println!("   关键要点:");
    println!("   - VecDeque::push_front_mut / push_back_mut: 两端插入并返回 &mut T");
    println!("   - VecDeque::insert_mut(index, value): 指定位置插入并返回 &mut T");
    println!("   - LinkedList::push_front_mut / push_back_mut: 链表两端插入并返回 &mut T");
    println!("   - 所有方法都避免了两阶段操作（插入 + 查找）的性能和 ergonomics 损失");
}
