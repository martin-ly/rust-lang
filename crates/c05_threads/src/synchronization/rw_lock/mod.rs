//! 读写锁（RwLock）示例
//! - 读多写少场景
//! - 尝试升级/降级（通过数据拷贝/重取锁实现，Rust 标准库不支持原地升级）

use std::sync::{Arc, RwLock};
use std::thread;

/// 读多写少：多个读者可以并发，写者独占
pub fn read_heavy_demo(readers: usize, writers: usize, iters: usize) -> usize {
    let data = Arc::new(RwLock::new(0usize));
    let mut handles = Vec::new();

    for _ in 0..readers {
        let d = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            let mut sum = 0usize;
            for _ in 0..iters {
                let v = *d.read().unwrap();
                sum += v;
            }
            sum
        }));
    }

    for _ in 0..writers {
        let d = Arc::clone(&data);
        handles.push(thread::spawn(move || {
            for _ in 0..iters {
                let mut v = d.write().unwrap();
                *v += 1;
            }
            0usize
        }));
    }

    let mut total_reads = 0usize;
    for h in handles { total_reads += h.join().unwrap(); }
    total_reads
}

/// 模拟“升级/降级”：先读后写（释放读锁再取写锁）、写后读（释放写锁再取读锁）
pub fn emulate_upgrade_downgrade() -> (usize, usize) {
    let data = Arc::new(RwLock::new(1usize));

    // 升级：先读再写（需释放读锁后重新获取写锁）
    {
        let v = *data.read().unwrap();
        let mut w = data.write().unwrap();
        *w = v + 1;
    }

    // 降级：持有写锁时复制数据，释放写锁后再读
    let after_upgrade = *data.read().unwrap();
    {
        let w = data.write().unwrap();
        let copy = *w;
        drop(w);
        let _r = data.read().unwrap();
        // 使用 copy 做只读计算
        let _calc = copy * 2;
    }
    let after_downgrade = *data.read().unwrap();
    (after_upgrade, after_downgrade)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_read_heavy_demo() {
        let _reads = read_heavy_demo(4, 2, 1_000);
    }

    #[test]
    fn test_emulate_upgrade_downgrade() {
        let (a, b) = emulate_upgrade_downgrade();
        assert!(a >= 2 - 1); // 简单校验流程
        assert!(b >= a);
    }
}