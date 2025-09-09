//! Arc 主题
//! - 强/弱引用：`Arc` 与 `Weak`
//! - 循环引用与打破
//! - `Arc<Mutex<T>>` vs `Arc<RwLock<T>>`

pub mod count;

use std::sync::{Arc, Mutex, RwLock, Weak};

/// 强/弱引用：当强引用计数归零后资源被释放，弱引用不会保持资源存活
pub fn strong_weak_demo() -> (usize, usize) {
    let a = Arc::new(10);
    let w1: Weak<i32> = Arc::downgrade(&a);
    let strong_cnt_before = Arc::strong_count(&a);
    drop(a);
    let upgraded = w1.upgrade();
    let strong_cnt_after = upgraded.as_ref().map(Arc::strong_count).unwrap_or(0);
    (strong_cnt_before, strong_cnt_after)
}

/// 循环引用与打破：使用 `Weak` 避免 `Arc` 形成环
pub fn break_cycle_demo() -> String {
    #[derive(Debug)]
    struct Node {
        #[allow(dead_code)]
        name: String,
        // 父指针使用 Weak 避免环
        parent: Mutex<Weak<Node>>,
        // 子节点使用强引用，保证其存活
        _children: Mutex<Vec<Arc<Node>>>,
    }

    let root = Arc::new(Node { name: "root".into(), parent: Mutex::new(Weak::new()), _children: Mutex::new(vec![]) });
    let child = Arc::new(Node { name: "child".into(), parent: Mutex::new(Weak::new()), _children: Mutex::new(vec![]) });

    // 关联父子
    *child.parent.lock().unwrap() = Arc::downgrade(&root);
    root._children.lock().unwrap().push(Arc::clone(&child));

    // 如果 parent 用 Arc<Node> 将形成环而无法回收
    // 使用 Weak 可以在 root 释放后，使 child.parent 升级失败
    drop(root);
    let up = child.parent.lock().unwrap().upgrade();
    if up.is_none() { "broken".into() } else { "leak".into() }
}

/// 对比：Arc<Mutex<T>> 与 Arc<RwLock<T>>
pub fn mutex_vs_rwlock(readers: usize, writers: usize, iters: usize) -> (usize, usize) {
    let m = Arc::new(Mutex::new(0usize));
    let r = Arc::new(RwLock::new(0usize));

    let mut h = Vec::new();
    // 读线程
    for _ in 0..readers {
        let m1 = Arc::clone(&m);
        let r1 = Arc::clone(&r);
        h.push(std::thread::spawn(move || {
            let mut sum = 0usize;
            for _ in 0..iters {
                sum += *m1.lock().unwrap();
                sum += *r1.read().unwrap();
            }
            sum
        }));
    }

    // 写线程
    for _ in 0..writers {
        let m1 = Arc::clone(&m);
        let r1 = Arc::clone(&r);
        h.push(std::thread::spawn(move || {
            for _ in 0..iters {
                *m1.lock().unwrap() += 1;
                *r1.write().unwrap() += 1;
            }
            0usize
        }));
    }

    let mut total = 0usize;
    for t in h { total += t.join().unwrap(); }
    (total, *m.lock().unwrap() + *r.read().unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_strong_weak_demo() {
        let (before, after) = strong_weak_demo();
        assert!(before >= 1);
        assert_eq!(after, 0);
    }

    #[test]
    fn test_break_cycle_demo() {
        assert_eq!(break_cycle_demo(), "broken");
    }

    #[test]
    fn test_mutex_vs_rwlock() {
        let (_reads, final_sum) = mutex_vs_rwlock(2, 2, 1000);
        assert!(final_sum > 0);
    }
}
