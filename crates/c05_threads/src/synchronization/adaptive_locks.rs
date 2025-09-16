//! 自适应锁实现
//!
//! 本模块提供了多种自适应锁实现：
//! - 自适应互斥锁
//! - 自适应读写锁
//! - 自适应自旋锁
//! - 混合锁策略

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, RwLock};
use std::thread;
use std::time::{Duration, Instant};

/// 锁性能统计
#[derive(Debug)]
pub struct LockStats {
    pub total_acquires: AtomicUsize,
    pub total_waits: AtomicUsize,
    pub total_spins: AtomicUsize,
    pub average_wait_time: AtomicUsize, // 微秒
    pub contention_count: AtomicUsize,
}

impl LockStats {
    pub fn new() -> Self {
        Self {
            total_acquires: AtomicUsize::new(0),
            total_waits: AtomicUsize::new(0),
            total_spins: AtomicUsize::new(0),
            average_wait_time: AtomicUsize::new(0),
            contention_count: AtomicUsize::new(0),
        }
    }

    pub fn record_acquire(&self) {
        self.total_acquires.fetch_add(1, Ordering::Relaxed);
    }

    pub fn record_wait(&self, wait_time: Duration) {
        self.total_waits.fetch_add(1, Ordering::Relaxed);
        let wait_micros = wait_time.as_micros() as usize;
        self.average_wait_time.store(wait_micros, Ordering::Relaxed);
    }

    pub fn record_spin(&self) {
        self.total_spins.fetch_add(1, Ordering::Relaxed);
    }

    pub fn record_contention(&self) {
        self.contention_count.fetch_add(1, Ordering::Relaxed);
    }

    pub fn get_contention_ratio(&self) -> f64 {
        let acquires = self.total_acquires.load(Ordering::Relaxed);
        let contentions = self.contention_count.load(Ordering::Relaxed);

        if acquires == 0 {
            0.0
        } else {
            contentions as f64 / acquires as f64
        }
    }
}

/// 自适应互斥锁
///
/// 根据锁的竞争情况自动调整策略
pub struct AdaptiveMutex<T> {
    data: Arc<Mutex<T>>,
    stats: Arc<LockStats>,
    spin_threshold: AtomicUsize,
    max_spins: AtomicUsize,
    adaptive_enabled: AtomicBool,
}

impl<T> AdaptiveMutex<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(Mutex::new(data)),
            stats: Arc::new(LockStats::new()),
            spin_threshold: AtomicUsize::new(100), // 默认100次自旋
            max_spins: AtomicUsize::new(1000),     // 最大1000次自旋
            adaptive_enabled: AtomicBool::new(true),
        }
    }

    pub fn lock<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let _start_time = Instant::now();
        let mut spin_count = 0;
        let max_spins = self.max_spins.load(Ordering::Relaxed);

        // 尝试自旋
        while spin_count < max_spins {
            if let Ok(mut guard) = self.data.try_lock() {
                self.stats.record_acquire();
                if spin_count > 0 {
                    self.stats.record_spin();
                }
                return f(&mut guard);
            }

            spin_count += 1;
            self.stats.record_spin();

            // 自适应调整自旋次数
            if self.adaptive_enabled.load(Ordering::Relaxed) {
                self.adapt_spin_threshold();
            }
        }

        // 自旋失败，使用阻塞锁
        self.stats.record_contention();
        let wait_start = Instant::now();
        let mut guard = self.data.lock().unwrap();
        let wait_time = wait_start.elapsed();
        self.stats.record_wait(wait_time);
        self.stats.record_acquire();

        f(&mut guard)
    }

    fn adapt_spin_threshold(&self) {
        let contention_ratio = self.stats.get_contention_ratio();
        let current_threshold = self.spin_threshold.load(Ordering::Relaxed);

        if contention_ratio > 0.5 {
            // 高竞争，减少自旋
            let new_threshold = (current_threshold as f32 * 0.8) as usize;
            self.spin_threshold
                .store(new_threshold.max(10), Ordering::Relaxed);
        } else if contention_ratio < 0.1 {
            // 低竞争，增加自旋
            let new_threshold = (current_threshold as f32 * 1.2) as usize;
            self.spin_threshold
                .store(new_threshold.min(1000), Ordering::Relaxed);
        }
    }

    pub fn get_stats(&self) -> &LockStats {
        &self.stats
    }

    pub fn enable_adaptive(&self, enabled: bool) {
        self.adaptive_enabled.store(enabled, Ordering::Relaxed);
    }

    pub fn set_spin_threshold(&self, threshold: usize) {
        self.spin_threshold.store(threshold, Ordering::Relaxed);
    }
}

/// 自适应读写锁
///
/// 根据读写模式自动调整策略
pub struct AdaptiveRwLock<T> {
    data: Arc<RwLock<T>>,
    stats: Arc<LockStats>,
    read_optimized: AtomicBool,
    write_optimized: AtomicBool,
}

impl<T> AdaptiveRwLock<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(RwLock::new(data)),
            stats: Arc::new(LockStats::new()),
            read_optimized: AtomicBool::new(true),
            write_optimized: AtomicBool::new(false),
        }
    }

    pub fn read<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&T) -> R,
    {
        let _start_time = Instant::now();

        if self.read_optimized.load(Ordering::Relaxed) {
            // 读优化模式
            let guard = self.data.read().unwrap();
            self.stats.record_acquire();
            f(&*guard)
        } else {
            // 写优化模式，读操作也使用写锁
            let guard = self.data.write().unwrap();
            self.stats.record_acquire();
            f(&*guard)
        }
    }

    pub fn write<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let _start_time = Instant::now();

        if self.write_optimized.load(Ordering::Relaxed) {
            // 写优化模式
            let mut guard = self.data.write().unwrap();
            self.stats.record_acquire();
            f(&mut *guard)
        } else {
            // 读优化模式
            let mut guard = self.data.write().unwrap();
            self.stats.record_acquire();
            f(&mut *guard)
        }
    }

    pub fn adapt_strategy(&self) {
        let contention_ratio = self.stats.get_contention_ratio();

        if contention_ratio > 0.7 {
            // 高竞争，优化写操作
            self.write_optimized.store(true, Ordering::Relaxed);
            self.read_optimized.store(false, Ordering::Relaxed);
        } else if contention_ratio < 0.3 {
            // 低竞争，优化读操作
            self.read_optimized.store(true, Ordering::Relaxed);
            self.write_optimized.store(false, Ordering::Relaxed);
        }
    }

    pub fn get_stats(&self) -> &LockStats {
        &self.stats
    }
}

/// 自适应自旋锁
///
/// 根据等待时间自动调整自旋策略
pub struct AdaptiveSpinLock<T> {
    data: Arc<Mutex<T>>,
    stats: Arc<LockStats>,
    spin_duration: AtomicUsize, // 微秒
    backoff_factor: AtomicUsize,
}

impl<T> AdaptiveSpinLock<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(Mutex::new(data)),
            stats: Arc::new(LockStats::new()),
            spin_duration: AtomicUsize::new(1000), // 1毫秒
            backoff_factor: AtomicUsize::new(2),
        }
    }

    pub fn lock<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let _start_time = Instant::now();
        let spin_duration = self.spin_duration.load(Ordering::Relaxed);
        let _backoff_factor = self.backoff_factor.load(Ordering::Relaxed);

        loop {
            // 尝试获取锁
            if let Ok(mut guard) = self.data.try_lock() {
                self.stats.record_acquire();
                return f(&mut guard);
            }

            // 自旋等待
            let spin_start = Instant::now();
            while spin_start.elapsed().as_micros() < spin_duration as u128 {
                if let Ok(mut guard) = self.data.try_lock() {
                    self.stats.record_acquire();
                    return f(&mut guard);
                }
                self.stats.record_spin();
            }

            // 自旋失败，使用阻塞锁
            self.stats.record_contention();
            let wait_start = Instant::now();
            let mut guard = self.data.lock().unwrap();
            let wait_time = wait_start.elapsed();
            self.stats.record_wait(wait_time);
            self.stats.record_acquire();

            // 自适应调整自旋时间
            self.adapt_spin_duration(wait_time);

            return f(&mut guard);
        }
    }

    fn adapt_spin_duration(&self, wait_time: Duration) {
        let wait_micros = wait_time.as_micros() as usize;
        let current_duration = self.spin_duration.load(Ordering::Relaxed);
        let backoff_factor = self.backoff_factor.load(Ordering::Relaxed);

        if wait_micros > current_duration * 2 {
            // 等待时间过长，增加自旋时间
            let new_duration = current_duration * backoff_factor;
            self.spin_duration
                .store(new_duration.min(10000), Ordering::Relaxed); // 最大10毫秒
        } else if wait_micros < current_duration / 2 {
            // 等待时间较短，减少自旋时间
            let new_duration = current_duration / backoff_factor;
            self.spin_duration
                .store(new_duration.max(100), Ordering::Relaxed); // 最小100微秒
        }
    }

    pub fn get_stats(&self) -> &LockStats {
        &self.stats
    }
}

/// 混合锁策略
///
/// 根据锁的使用模式自动选择最佳策略
#[allow(dead_code)]
pub struct HybridLock<T> {
    data: Arc<Mutex<T>>,
    stats: Arc<LockStats>,
    strategy: AtomicUsize, // 0: 自旋, 1: 阻塞, 2: 混合
    spin_count: AtomicUsize,
    max_spins: AtomicUsize,
}

impl<T> HybridLock<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(Mutex::new(data)),
            stats: Arc::new(LockStats::new()),
            strategy: AtomicUsize::new(2), // 默认混合策略
            spin_count: AtomicUsize::new(0),
            max_spins: AtomicUsize::new(100),
        }
    }

    pub fn lock<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let strategy = self.strategy.load(Ordering::Relaxed);

        match strategy {
            0 => self.spin_lock(f),
            1 => self.blocking_lock(f),
            2 => self.hybrid_lock(f),
            _ => self.hybrid_lock(f),
        }
    }

    fn spin_lock<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let max_spins = self.max_spins.load(Ordering::Relaxed);
        let mut spin_count = 0;

        while spin_count < max_spins {
            if let Ok(mut guard) = self.data.try_lock() {
                self.stats.record_acquire();
                return f(&mut guard);
            }

            spin_count += 1;
            self.stats.record_spin();
        }

        // 自旋失败，回退到阻塞锁
        self.stats.record_contention();
        let mut guard = self.data.lock().unwrap();
        self.stats.record_acquire();
        f(&mut guard)
    }

    fn blocking_lock<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let start_time = Instant::now();
        let mut guard = self.data.lock().unwrap();
        let wait_time = start_time.elapsed();
        self.stats.record_wait(wait_time);
        self.stats.record_acquire();
        f(&mut guard)
    }

    fn hybrid_lock<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        let max_spins = self.max_spins.load(Ordering::Relaxed);
        let mut spin_count = 0;

        // 先尝试自旋
        while spin_count < max_spins {
            if let Ok(mut guard) = self.data.try_lock() {
                self.stats.record_acquire();
                if spin_count > 0 {
                    self.stats.record_spin();
                }
                return f(&mut guard);
            }

            spin_count += 1;
            self.stats.record_spin();
        }

        // 自旋失败，使用阻塞锁
        self.stats.record_contention();
        let start_time = Instant::now();
        let mut guard = self.data.lock().unwrap();
        let wait_time = start_time.elapsed();
        self.stats.record_wait(wait_time);
        self.stats.record_acquire();

        // 根据等待时间调整策略
        self.adapt_strategy(wait_time);

        f(&mut guard)
    }

    fn adapt_strategy(&self, wait_time: Duration) {
        let _wait_micros = wait_time.as_micros() as usize;
        let contention_ratio = self.stats.get_contention_ratio();

        if contention_ratio > 0.8 {
            // 高竞争，使用阻塞策略
            self.strategy.store(1, Ordering::Relaxed);
        } else if contention_ratio < 0.2 {
            // 低竞争，使用自旋策略
            self.strategy.store(0, Ordering::Relaxed);
        } else {
            // 中等竞争，使用混合策略
            self.strategy.store(2, Ordering::Relaxed);
        }
    }

    pub fn get_stats(&self) -> &LockStats {
        &self.stats
    }

    pub fn set_strategy(&self, strategy: usize) {
        self.strategy.store(strategy, Ordering::Relaxed);
    }
}

/// 运行所有自适应锁示例
pub fn demonstrate_adaptive_locks() {
    println!("=== 自适应锁演示 ===");

    // 测试自适应互斥锁
    let adaptive_mutex = Arc::new(AdaptiveMutex::new(0));
    let handles: Vec<_> = (0..4)
        .map(|_i| {
            let mutex = adaptive_mutex.clone();
            thread::spawn(move || {
                for _ in 0..1000 {
                    mutex.lock(|data| {
                        *data += 1;
                    });
                }
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    let stats = adaptive_mutex.get_stats();
    println!("自适应互斥锁统计:");
    println!(
        "  总获取次数: {}",
        stats.total_acquires.load(Ordering::Relaxed)
    );
    println!(
        "  总等待次数: {}",
        stats.total_waits.load(Ordering::Relaxed)
    );
    println!(
        "  总自旋次数: {}",
        stats.total_spins.load(Ordering::Relaxed)
    );
    println!("  竞争比例: {:.2}", stats.get_contention_ratio());

    // 测试自适应读写锁
    let adaptive_rwlock = Arc::new(AdaptiveRwLock::new(0));
    let read_handles: Vec<_> = (0..4)
        .map(|_i| {
            let rwlock = adaptive_rwlock.clone();
            thread::spawn(move || {
                for _ in 0..1000 {
                    rwlock.read(|data| {
                        let _ = *data;
                    });
                }
            })
        })
        .collect();

    let write_handles: Vec<_> = (0..2)
        .map(|_i| {
            let rwlock = adaptive_rwlock.clone();
            thread::spawn(move || {
                for _ in 0..500 {
                    rwlock.write(|data| {
                        *data += 1;
                    });
                }
            })
        })
        .collect();

    for handle in read_handles {
        handle.join().unwrap();
    }

    for handle in write_handles {
        handle.join().unwrap();
    }

    let stats = adaptive_rwlock.get_stats();
    println!("自适应读写锁统计:");
    println!(
        "  总获取次数: {}",
        stats.total_acquires.load(Ordering::Relaxed)
    );
    println!("  竞争比例: {:.2}", stats.get_contention_ratio());

    // 测试混合锁
    let hybrid_lock = Arc::new(HybridLock::new(0));
    let handles: Vec<_> = (0..4)
        .map(|_i| {
            let lock = hybrid_lock.clone();
            thread::spawn(move || {
                for _ in 0..1000 {
                    lock.lock(|data| {
                        *data += 1;
                    });
                }
            })
        })
        .collect();

    for handle in handles {
        handle.join().unwrap();
    }

    let stats = hybrid_lock.get_stats();
    println!("混合锁统计:");
    println!(
        "  总获取次数: {}",
        stats.total_acquires.load(Ordering::Relaxed)
    );
    println!(
        "  总自旋次数: {}",
        stats.total_spins.load(Ordering::Relaxed)
    );
    println!("  竞争比例: {:.2}", stats.get_contention_ratio());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_adaptive_mutex() {
        let mutex = AdaptiveMutex::new(0);

        mutex.lock(|data| {
            *data = 42;
        });

        let value = mutex.lock(|data| *data);
        assert_eq!(value, 42);
    }

    #[test]
    fn test_adaptive_rwlock() {
        let rwlock = AdaptiveRwLock::new(0);

        rwlock.write(|data| {
            *data = 42;
        });

        let value: i32 = rwlock.read(|data| *data);
        assert_eq!(value, 42);
    }

    #[test]
    fn test_adaptive_spinlock() {
        let spinlock = AdaptiveSpinLock::new(0);

        spinlock.lock(|data| {
            *data = 42;
        });

        let value = spinlock.lock(|data| *data);
        assert_eq!(value, 42);
    }

    #[test]
    fn test_hybrid_lock() {
        let lock = HybridLock::new(0);

        lock.lock(|data| {
            *data = 42;
        });

        let value = lock.lock(|data| *data);
        assert_eq!(value, 42);
    }
}
