//! L3 高级系统主题嵌入式测验 — 可运行验证
//!
//! 本文件提取自 concept/03_advanced/ 中以下文件的嵌入式测验：
//! - 11_atomics_and_memory_ordering.md
//! - 13_inline_assembly.md
//! - 16_lock_free.md
//!
//! 运行: cargo test --test l3_advanced_systems

use std::sync::Arc;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::thread;

#[cfg(target_arch = "x86_64")]
use std::arch::asm;

// ========== 11_atomics.md 测验验证 ==========

/// 测验1: fetch_add 是原子的，load+store 不是
#[test]
fn test_atomic_fetch_add_vs_load_store() {
    let counter = AtomicUsize::new(0);
    let c = &counter;

    thread::scope(|s| {
        for _ in 0..10 {
            s.spawn(|| {
                for _ in 0..1000 {
                    c.fetch_add(1, Ordering::Relaxed);
                }
            });
        }
    });

    // 10 线程 × 1000 次 = 10000，原子操作保证精确
    assert_eq!(counter.load(Ordering::Relaxed), 10_000);
}

/// 测验2: Release/Acquire 配对保证可见性
#[test]
fn test_release_acquire_visibility() {
    static READY: AtomicBool = AtomicBool::new(false);
    static DATA: AtomicUsize = AtomicUsize::new(0);

    thread::scope(|s| {
        s.spawn(|| {
            DATA.store(42, Ordering::Relaxed);
            READY.store(true, Ordering::Release);
        });

        s.spawn(|| {
            while !READY.load(Ordering::Acquire) {
                thread::yield_now();
            }
            // Acquire 保证看到 DATA = 42
            assert_eq!(DATA.load(Ordering::Relaxed), 42);
        });
    });
}

/// 测验3: 自旋锁 CAS 实现
#[test]
fn test_spinlock_cas() {
    struct SpinLock {
        locked: AtomicBool,
        data: std::cell::UnsafeCell<usize>,
    }

    unsafe impl Sync for SpinLock {}

    impl SpinLock {
        fn lock(&self) {
            while self
                .locked
                .compare_exchange_weak(false, true, Ordering::Acquire, Ordering::Relaxed)
                .is_err()
            {
                std::hint::spin_loop();
            }
        }

        fn unlock(&self) {
            self.locked.store(false, Ordering::Release);
        }
    }

    let lock = Arc::new(SpinLock {
        locked: AtomicBool::new(false),
        data: std::cell::UnsafeCell::new(0),
    });

    let l = Arc::clone(&lock);
    let h = thread::spawn(move || {
        l.lock();
        unsafe {
            *l.data.get() += 1;
        }
        l.unlock();
    });

    lock.lock();
    unsafe {
        *lock.data.get() += 1;
    }
    lock.unlock();

    h.join().unwrap();
    assert_eq!(unsafe { *lock.data.get() }, 2);
}

// ========== 13_inline_assembly.md 测验验证 ==========

/// 测验1: 内联汇编读取 CPUID
#[test]
#[cfg(target_arch = "x86_64")]
fn test_inline_asm_cpuid() {
    let eax: u32;
    let ebx: u32;
    let ecx: u32;
    let edx: u32;

    unsafe {
        // 保存 rbx（LLVM 内部使用），cpuid 会修改它
        asm!(
            "push rbx",
            "cpuid",
            "mov {ebx:e}, ebx",
            "pop rbx",
            inout("eax") 0 => eax,
            ebx = lateout(reg) ebx,
            lateout("ecx") ecx,
            lateout("edx") edx,
        );
    }

    // CPUID leaf 0 返回厂商字符串信息
    // 至少应该返回非零值
    assert!(eax > 0 || ebx > 0 || ecx > 0 || edx > 0);
}

/// 测验2: RDTSC 读取时间戳计数器
#[test]
#[cfg(target_arch = "x86_64")]
fn test_inline_asm_rdtsc() {
    let lo: u32;
    let hi: u32;

    unsafe {
        asm!(
            "rdtsc",
            out("eax") lo,
            out("edx") hi,
        );
    }

    let tsc1 = ((hi as u64) << 32) | (lo as u64);

    // 执行一些工作
    let mut sum = 0u64;
    for i in 0..1000 {
        sum += i;
    }

    let lo2: u32;
    let hi2: u32;
    unsafe {
        asm!(
            "rdtsc",
            out("eax") lo2,
            out("edx") hi2,
        );
    }

    let tsc2 = ((hi2 as u64) << 32) | (lo2 as u64);

    // 时间戳应该递增
    assert!(tsc2 > tsc1, "RDTSC 应该递增");
    let _ = sum;
}

// ========== 16_lock_free.md 测验验证 ==========

/// 测验1: CAS 循环递增
#[test]
fn test_cas_loop_increment() {
    let counter = AtomicUsize::new(0);
    let c = Arc::new(counter);

    let mut handles = vec![];
    for _ in 0..10 {
        let cc = Arc::clone(&c);
        handles.push(thread::spawn(move || {
            loop {
                let current = cc.load(Ordering::Relaxed);
                let new = current + 1;
                match cc.compare_exchange(current, new, Ordering::Release, Ordering::Relaxed) {
                    Ok(_) => break,
                    Err(_) => continue,
                }
            }
        }));
    }

    for h in handles {
        h.join().unwrap();
    }

    assert_eq!(c.load(Ordering::Relaxed), 10);
}

/// 测验2: AtomicBool 实现简单标志
#[test]
fn test_atomic_bool_flag() {
    static FLAG: AtomicBool = AtomicBool::new(false);

    thread::scope(|s| {
        s.spawn(|| {
            thread::sleep(std::time::Duration::from_millis(10));
            FLAG.store(true, Ordering::Release);
        });

        s.spawn(|| {
            while !FLAG.load(Ordering::Acquire) {
                thread::yield_now();
            }
            assert!(FLAG.load(Ordering::Relaxed));
        });
    });
}

/// 测验3: compare_exchange 返回旧值
#[test]
fn test_compare_exchange_returns_old() {
    let atomic = AtomicUsize::new(5);

    // 期望 5，替换为 10 → 成功，返回 Ok(5)
    let result = atomic.compare_exchange(5, 10, Ordering::SeqCst, Ordering::Relaxed);
    assert_eq!(result, Ok(5));
    assert_eq!(atomic.load(Ordering::Relaxed), 10);

    // 期望 5，替换为 20 → 失败（当前是 10），返回 Err(10)
    let result = atomic.compare_exchange(5, 20, Ordering::SeqCst, Ordering::Relaxed);
    assert_eq!(result, Err(10));
    assert_eq!(atomic.load(Ordering::Relaxed), 10);
}
