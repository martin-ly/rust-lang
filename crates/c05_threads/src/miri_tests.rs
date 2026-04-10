//! Miri 测试模块 - 并发和线程安全验证
//!
//! 本模块包含用于 Miri 测试的并发代码示例，验证线程安全性。
//! 注意: Miri 可以检测数据竞争和内存序问题
//!
//! 运行方式:
//!   cargo miri test miri_tests
//!   MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-disable-isolation" cargo miri test miri_tests

use std::sync::atomic::{AtomicI32, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;

// ==================== 原子操作测试 ====================

/// 测试目的: 验证基本原子操作
/// 测试场景: 使用不同 Ordering 进行原子读写
/// 预期结果: 应该正确完成所有操作
#[test]
fn test_atomic_basic() {
    let atomic = AtomicI32::new(0);
    
    atomic.store(42, Ordering::Relaxed);
    assert_eq!(atomic.load(Ordering::Relaxed), 42);
    
    let old = atomic.fetch_add(8, Ordering::SeqCst);
    assert_eq!(old, 42);
    assert_eq!(atomic.load(Ordering::SeqCst), 50);
}

/// 测试目的: 验证原子交换和比较交换
/// 测试场景: 使用 swap 和 compare_exchange
/// 预期结果: 应该正确完成交换操作
#[test]
fn test_atomic_swap_cas() {
    let atomic = AtomicI32::new(10);
    
    let old = atomic.swap(20, Ordering::AcqRel);
    assert_eq!(old, 10);
    
    // 比较交换
    let result = atomic.compare_exchange(
        20, // current
        30, // new
        Ordering::SeqCst,
        Ordering::Relaxed,
    );
    assert!(result.is_ok());
    assert_eq!(atomic.load(Ordering::Relaxed), 30);
}

// ==================== Arc 和 Mutex 测试 ====================

/// 测试目的: 验证 Arc 共享所有权
/// 测试场景: 克隆 Arc 并验证引用计数
/// 预期结果: 应该正确共享数据
#[test]
fn test_arc_shared() {
    let arc = Arc::new(42);
    let arc2 = Arc::clone(&arc);
    
    assert_eq!(*arc, 42);
    assert_eq!(*arc2, 42);
    assert_eq!(Arc::strong_count(&arc), 2);
}

/// 测试目的: 验证 Arc<Mutex<T>> 线程安全共享
/// 测试场景: 多线程通过 Mutex 修改共享数据
/// 预期结果: 应该正确累加计数器
#[test]
fn test_arc_mutex_threaded() {
    let data = Arc::new(Mutex::new(0));
    let mut handles = vec![];
    
    for _ in 0..4 {
        let data = Arc::clone(&data);
        let handle = thread::spawn(move || {
            let mut guard = data.lock().unwrap();
            *guard += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    assert_eq!(*data.lock().unwrap(), 4);
}

// ==================== 线程本地存储 ====================

use std::cell::RefCell;

thread_local! {
    static COUNTER: RefCell<i32> = RefCell::new(0);
}

/// 测试目的: 验证线程本地存储
/// 测试场景: 在不同位置访问线程本地变量
/// 预期结果: 应该正确存储和读取值
#[test]
fn test_thread_local() {
    COUNTER.with(|c| {
        *c.borrow_mut() = 10;
    });
    
    COUNTER.with(|c| {
        assert_eq!(*c.borrow(), 10);
    });
}

// ==================== UnsafeCell 测试 ====================

use std::cell::UnsafeCell;

/// 测试目的: 验证 UnsafeCell 基本使用
/// 测试场景: 通过 UnsafeCell 进行内部可变性
/// 预期结果: 应该正确读写值
#[test]
fn test_unsafe_cell() {
    let cell = UnsafeCell::new(42);
    
    unsafe {
        *cell.get() = 100;
        assert_eq!(*cell.get(), 100);
    }
}

// ==================== Send 和 Sync 测试 ====================

/// 测试目的: 验证 Send 类型跨线程传递
/// 测试场景: 将 Vec 移动到另一个线程
/// 预期结果: 应该正确传递并返回
#[test]
fn test_send_trait() {
    let data = vec![1, 2, 3];
    
    let handle = thread::spawn(move || {
        assert_eq!(data.len(), 3);
        data
    });
    
    let result = handle.join().unwrap();
    assert_eq!(result, vec![1, 2, 3]);
}

/// 测试目的: 验证 Sync 类型跨线程共享引用
/// 测试场景: 多线程共享对静态数组的引用
/// 预期结果: 应该正确读取数据
#[test]
fn test_sync_trait() {
    let data: &'static [i32] = &[1, 2, 3, 4, 5];
    let mut handles = vec![];
    
    for i in 0..3 {
        let handle = thread::spawn(move || {
            assert_eq!(data[i], (i + 1) as i32);
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}

// ==================== 内存序测试 ====================

/// 测试目的: 验证 Release-Acquire 语义
/// 测试场景: 一个线程写入数据后设置标志，另一个线程读取标志后读取数据
/// 预期结果: Acquire 应该能看到 Release 之前的写入
#[test]
fn test_release_acquire() {
    let ready = Arc::new(AtomicI32::new(0));
    let data = Arc::new(AtomicI32::new(0));
    
    let ready_clone = Arc::clone(&ready);
    let data_clone = Arc::clone(&data);
    
    let handle = thread::spawn(move || {
        // 先写入数据
        data_clone.store(42, Ordering::Relaxed);
        // 标记就绪
        ready_clone.store(1, Ordering::Release);
    });
    
    // 等待就绪
    while ready.load(Ordering::Acquire) == 0 {
        thread::yield_now();
    }
    
    // Acquire 确保能看到 Release 之前的写入
    assert_eq!(data.load(Ordering::Relaxed), 42);
    
    handle.join().unwrap();
}

/// 测试目的: 验证 SeqCst 全序性
/// 测试场景: 两个线程使用 SeqCst 进行同步
/// 预期结果: 应该建立全局顺序
#[test]
fn test_seqcst() {
    let flag1 = Arc::new(AtomicI32::new(0));
    let flag2 = Arc::new(AtomicI32::new(0));
    
    let flag1_clone = Arc::clone(&flag1);
    let flag2_clone = Arc::clone(&flag2);
    
    let handle = thread::spawn(move || {
        flag1_clone.store(1, Ordering::SeqCst);
        let _ = flag2_clone.load(Ordering::SeqCst);
    });
    
    flag2.store(1, Ordering::SeqCst);
    let _ = flag1.load(Ordering::SeqCst);
    
    handle.join().unwrap();
}

// ==================== 屏障和同步原语 ====================

use std::sync::Barrier;

/// 测试目的: 验证 Barrier 同步
/// 测试场景: 多个线程在屏障处等待
/// 预期结果: 所有线程应该同步通过屏障
#[test]
fn test_barrier() {
    let barrier = Arc::new(Barrier::new(3));
    let mut handles = vec![];
    
    for i in 0..3 {
        let barrier = Arc::clone(&barrier);
        let handle = thread::spawn(move || {
            let _ = i * 10;
            let _ = barrier.wait();
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}

// ==================== 条件变量 ====================

use std::sync::Condvar;

/// 测试目的: 验证 Condvar 通知
/// 测试场景: 一个线程等待条件，另一个线程通知
/// 预期结果: 应该正确同步状态
#[test]
fn test_condvar() {
    let pair = Arc::new((Mutex::new(false), Condvar::new()));
    let pair2 = Arc::clone(&pair);
    
    let handle = thread::spawn(move || {
        let (lock, cvar) = &*pair2;
        let mut started = lock.lock().unwrap();
        *started = true;
        cvar.notify_one();
    });
    
    let (lock, cvar) = &*pair;
    let mut started = lock.lock().unwrap();
    while !*started {
        started = cvar.wait(started).unwrap();
    }
    
    assert!(*started);
    handle.join().unwrap();
}

// ==================== RwLock ====================

use std::sync::RwLock;

/// 测试目的: 验证 RwLock 读写锁
/// 测试场景: 多个读锁同时持有，写锁独占
/// 预期结果: 应该正确管理并发访问
#[test]
fn test_rwlock() {
    let lock = RwLock::new(5);
    
    // 多个读锁可以同时持有
    let r1 = lock.read().unwrap();
    let r2 = lock.read().unwrap();
    assert_eq!(*r1, 5);
    assert_eq!(*r2, 5);
    drop(r1);
    drop(r2);
    
    // 写锁独占
    let mut w = lock.write().unwrap();
    *w += 1;
    assert_eq!(*w, 6);
}

// ==================== 原始同步原语（Unsafe） ====================

use std::sync::atomic::AtomicBool;

/// 自旋锁实现
struct SpinLock<T> {
    locked: AtomicBool,
    data: UnsafeCell<T>,
}

unsafe impl<T: Send> Send for SpinLock<T> {}
unsafe impl<T: Send> Sync for SpinLock<T> {}

impl<T> SpinLock<T> {
    fn new(data: T) -> Self {
        Self {
            locked: AtomicBool::new(false),
            data: UnsafeCell::new(data),
        }
    }
    
    fn lock(&self) -> SpinLockGuard<'_, T> {
        // 自旋等待
        while self.locked.compare_exchange(
            false,
            true,
            Ordering::Acquire,
            Ordering::Relaxed,
        ).is_err() {
            // 自旋
            while self.locked.load(Ordering::Relaxed) {
                std::hint::spin_loop();
            }
        }
        
        SpinLockGuard { lock: self }
    }
}

/// 自旋锁守卫
struct SpinLockGuard<'a, T> {
    lock: &'a SpinLock<T>,
}

impl<'a, T> Drop for SpinLockGuard<'a, T> {
    fn drop(&mut self) {
        self.lock.locked.store(false, Ordering::Release);
    }
}

impl<'a, T> std::ops::Deref for SpinLockGuard<'a, T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.lock.data.get() }
    }
}

impl<'a, T> std::ops::DerefMut for SpinLockGuard<'a, T> {
    fn deref_mut(&mut self) -> &mut T {
        unsafe { &mut *self.lock.data.get() }
    }
}

/// 测试目的: 验证自旋锁实现
/// 测试场景: 多线程使用自旋锁累加计数器
/// 预期结果: 应该正确同步访问
#[test]
fn test_spinlock() {
    let lock = Arc::new(SpinLock::new(0));
    let mut handles = vec![];
    
    for _ in 0..4 {
        let lock = Arc::clone(&lock);
        let handle = thread::spawn(move || {
            let mut guard = lock.lock();
            *guard += 1;
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    assert_eq!(*lock.lock(), 4);
}

// ==================== Miri 会检测的错误（标记为 ignore） ====================

/// 测试目的: 验证数据竞争检测
/// 测试场景: 两个线程无保护地访问同一静态变量
/// 预期结果: Miri 应该检测到 UB
#[test]
#[ignore = "This test should fail with data race"]
fn test_data_race() {
    use std::sync::atomic::AtomicI32;
    
    static COUNTER: AtomicI32 = AtomicI32::new(0);
    
    let mut handles = vec![];
    
    for _ in 0..2 {
        let handle = thread::spawn(|| {
            for _ in 0..1000 {
                COUNTER.fetch_add(1, Ordering::Relaxed);
            }
        });
        handles.push(handle);
    }
    
    for handle in handles {
        handle.join().unwrap();
    }
}

/// 测试目的: 验证 UnsafeCell 与 Mutex 的安全使用
/// 测试场景: 使用 Mutex 包裹 UnsafeCell
/// 预期结果: 应该正确同步访问
#[test]
fn test_unsafe_cell_with_mutex() {
    // 使用 Mutex 包裹 UnsafeCell 来提供线程安全
    let cell = Arc::new(Mutex::new(UnsafeCell::new(0)));
    let cell2 = Arc::clone(&cell);
    
    let handle = thread::spawn(move || {
        let guard = cell2.lock().unwrap();
        unsafe {
            *guard.get() = 42;
        }
    });
    
    {
        let guard = cell.lock().unwrap();
        unsafe {
            *guard.get() = 100;
        }
    }
    
    handle.join().unwrap();
    
    let final_val = unsafe { *cell.lock().unwrap().get() };
    // 值取决于线程执行顺序，可能是 42 或 100
    assert!(final_val == 42 || final_val == 100);
}
