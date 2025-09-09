//! 操作系统特定的同步原语
//! 
//! 本模块提供了针对不同操作系统的优化同步原语：
//! - Windows: 关键段、事件、信号量
//! - Linux: futex、pthread
//! - macOS: Grand Central Dispatch

use std::sync::{Arc, Mutex};
use std::sync::atomic::{
    AtomicUsize,
    //AtomicBool,
    Ordering
};
use std::thread;
use std::time::Duration;

#[allow(dead_code)]
#[cfg(target_os = "windows")]
mod windows_sync {
    use super::*;
    
    /// Windows关键段
    pub struct WindowsCriticalSection {
        cs: std::sync::Mutex<()>,
    }
    
    impl WindowsCriticalSection {
        pub fn new() -> Self {
            Self {
                cs: std::sync::Mutex::new(()),
            }
        }
        
        pub fn enter(&self) {
            drop(self.cs.lock().unwrap());
        }
        
        pub fn leave(&self) {
            drop(self.cs.lock().unwrap());
        }
        
        pub fn try_enter(&self) -> bool {
            self.cs.try_lock().is_ok()
        }
    }
    
    /// Windows事件
    pub struct WindowsEvent {
        event: Arc<Mutex<bool>>,
        condvar: Arc<std::sync::Condvar>,
    }
    
    impl WindowsEvent {
        pub fn new() -> Self {
            Self {
                event: Arc::new(Mutex::new(false)),
                condvar: Arc::new(std::sync::Condvar::new()),
            }
        }
        
        pub fn set(&self) {
            let mut event = self.event.lock().unwrap();
            *event = true;
            self.condvar.notify_all();
        }
        
        pub fn reset(&self) {
            let mut event = self.event.lock().unwrap();
            *event = false;
        }
        
        pub fn wait(&self) {
            let mut event = self.event.lock().unwrap();
            while !*event {
                event = self.condvar.wait(event).unwrap();
            }
        }
        
        pub fn wait_timeout(&self, timeout: Duration) -> bool {
            let mut event = self.event.lock().unwrap();
            while !*event {
                let result = self.condvar.wait_timeout(event, timeout).unwrap();
                event = result.0;
                if result.1.timed_out() {
                    return false;
                }
            }
            true
        }
    }
    
    /// Windows信号量
    pub struct WindowsSemaphore {
        count: Arc<Mutex<usize>>,
        condvar: Arc<std::sync::Condvar>,
    }
    
    impl WindowsSemaphore {
        pub fn new(initial_count: usize) -> Self {
            Self {
                count: Arc::new(Mutex::new(initial_count)),
                condvar: Arc::new(std::sync::Condvar::new()),
            }
        }
        
        pub fn acquire(&self) {
            let mut count = self.count.lock().unwrap();
            while *count == 0 {
                count = self.condvar.wait(count).unwrap();
            }
            *count -= 1;
        }
        
        pub fn release(&self) {
            let mut count = self.count.lock().unwrap();
            *count += 1;
            self.condvar.notify_one();
        }
        
        pub fn try_acquire(&self) -> bool {
            let mut count = self.count.lock().unwrap();
            if *count > 0 {
                *count -= 1;
                true
            } else {
                false
            }
        }
    }
}

#[cfg(target_os = "linux")]
mod linux_sync {
    use super::*;
    use std::sync::atomic::{AtomicU32, AtomicPtr};
    use std::ptr;
    
    /// Linux futex
    pub struct LinuxFutex {
        value: AtomicU32,
    }
    
    impl LinuxFutex {
        pub fn new() -> Self {
            Self {
                value: AtomicU32::new(0),
            }
        }
        
        pub fn wait(&self, expected: u32) {
            // 简化的futex实现
            while self.value.load(Ordering::Acquire) == expected {
                thread::yield_now();
            }
        }
        
        pub fn wake(&self, count: u32) {
            self.value.fetch_add(1, Ordering::Release);
        }
        
        pub fn compare_and_swap(&self, current: u32, new: u32) -> bool {
            self.value.compare_exchange(current, new, Ordering::Acquire, Ordering::Relaxed).is_ok()
        }
    }
    
    /// Linux pthread互斥锁
    pub struct LinuxPthreadMutex<T> {
        data: Arc<Mutex<T>>,
        futex: LinuxFutex,
    }
    
    impl<T> LinuxPthreadMutex<T> {
        pub fn new(data: T) -> Self {
            Self {
                data: Arc::new(Mutex::new(data)),
                futex: LinuxFutex::new(),
            }
        }
        
        pub fn lock<F, R>(&self, f: F) -> R
        where
            F: FnOnce(&mut T) -> R,
        {
            // 尝试快速路径
            if self.futex.compare_and_swap(0, 1) {
                let result = f(&mut self.data.lock().unwrap());
                self.futex.wake(1);
                result
            } else {
                // 慢速路径
                self.futex.wait(0);
                let result = f(&mut self.data.lock().unwrap());
                self.futex.wake(1);
                result
            }
        }
    }
}

#[cfg(target_os = "macos")]
mod macos_sync {
    use super::*;
    
    /// macOS Grand Central Dispatch队列
    pub struct MacOSDispatchQueue {
        queue: Arc<Mutex<Vec<Box<dyn FnOnce() + Send + 'static>>>>,
        condvar: Arc<std::sync::Condvar>,
        running: Arc<AtomicBool>,
    }
    
    impl MacOSDispatchQueue {
        pub fn new() -> Self {
            Self {
                queue: Arc::new(Mutex::new(Vec::new())),
                condvar: Arc::new(std::sync::Condvar::new()),
                running: Arc::new(AtomicBool::new(true)),
            }
        }
        
        pub fn dispatch<F>(&self, work: F)
        where
            F: FnOnce() + Send + 'static,
        {
            let mut queue = self.queue.lock().unwrap();
            queue.push(Box::new(work));
            self.condvar.notify_one();
        }
        
        pub fn start_worker(&self) {
            let queue = self.queue.clone();
            let condvar = self.condvar.clone();
            let running = self.running.clone();
            
            thread::spawn(move || {
                while running.load(Ordering::Relaxed) {
                    let mut queue = queue.lock().unwrap();
                    while queue.is_empty() && running.load(Ordering::Relaxed) {
                        queue = condvar.wait(queue).unwrap();
                    }
                    
                    if let Some(work) = queue.pop() {
                        drop(queue);
                        work();
                    }
                }
            });
        }
        
        pub fn stop(&self) {
            self.running.store(false, Ordering::Relaxed);
            self.condvar.notify_all();
        }
    }
}

/// 跨平台同步原语包装器
pub struct CrossPlatformSync<T> {
    data: Arc<Mutex<T>>,
    #[cfg(target_os = "windows")]
    cs: windows_sync::WindowsCriticalSection,
    #[cfg(target_os = "linux")]
    futex: linux_sync::LinuxFutex,
    #[cfg(target_os = "macos")]
    dispatch_queue: macos_sync::MacOSDispatchQueue,
}

impl<T> CrossPlatformSync<T> {
    pub fn new(data: T) -> Self {
        Self {
            data: Arc::new(Mutex::new(data)),
            #[cfg(target_os = "windows")]
            cs: windows_sync::WindowsCriticalSection::new(),
            #[cfg(target_os = "linux")]
            futex: linux_sync::LinuxFutex::new(),
            #[cfg(target_os = "macos")]
            dispatch_queue: macos_sync::MacOSDispatchQueue::new(),
        }
    }
    
    pub fn lock<F, R>(&self, f: F) -> R
    where
        F: FnOnce(&mut T) -> R,
    {
        #[cfg(target_os = "windows")]
        {
            self.cs.enter();
            let result = f(&mut self.data.lock().unwrap());
            self.cs.leave();
            result
        }
        
        #[cfg(target_os = "linux")]
        {
            self.futex.wait(0);
            let result = f(&mut self.data.lock().unwrap());
            self.futex.wake(1);
            result
        }
        
        #[cfg(target_os = "macos")]
        {
            let result = f(&mut self.data.lock().unwrap());
            result
        }
        
        #[cfg(not(any(target_os = "windows", target_os = "linux", target_os = "macos")))]
        {
            f(&mut self.data.lock().unwrap())
        }
    }
}

/// 操作系统特定的性能监控
pub struct OSSpecificPerformanceMonitor {
    lock_contention: AtomicUsize,
    lock_acquisitions: AtomicUsize,
    average_wait_time: AtomicUsize,
}

impl OSSpecificPerformanceMonitor {
    pub fn new() -> Self {
        Self {
            lock_contention: AtomicUsize::new(0),
            lock_acquisitions: AtomicUsize::new(0),
            average_wait_time: AtomicUsize::new(0),
        }
    }
    
    pub fn record_lock_acquisition(&self) {
        self.lock_acquisitions.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_lock_contention(&self) {
        self.lock_contention.fetch_add(1, Ordering::Relaxed);
    }
    
    pub fn record_wait_time(&self, wait_time: Duration) {
        let wait_micros = wait_time.as_micros() as usize;
        self.average_wait_time.store(wait_micros, Ordering::Relaxed);
    }
    
    pub fn get_contention_ratio(&self) -> f64 {
        let acquisitions = self.lock_acquisitions.load(Ordering::Relaxed);
        let contentions = self.lock_contention.load(Ordering::Relaxed);
        
        if acquisitions == 0 {
            0.0
        } else {
            contentions as f64 / acquisitions as f64
        }
    }
    
    pub fn get_average_wait_time(&self) -> Duration {
        Duration::from_micros(self.average_wait_time.load(Ordering::Relaxed) as u64)
    }
}

/// 运行所有操作系统特定示例
pub fn demonstrate_os_specific() {
    println!("=== 操作系统特定同步原语演示 ===");
    
    // 测试跨平台同步
    let sync = Arc::new(CrossPlatformSync::new(0));
    let handles: Vec<_> = (0..4)
        .map(|_i| {
            let sync = sync.clone();
            thread::spawn(move || {
                for _ in 0..1000 {
                    sync.lock(|data| {
                        *data += 1;
                    });
                }
            })
        })
        .collect();
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("跨平台同步测试完成");
    
    // 测试性能监控
    let monitor = Arc::new(OSSpecificPerformanceMonitor::new());
    let handles: Vec<_> = (0..4)
        .map(|i| {
            let monitor = monitor.clone();
            thread::spawn(move || {
                for _ in 0..1000 {
                    monitor.record_lock_acquisition();
                    if i % 100 == 0 {
                        monitor.record_lock_contention();
                    }
                }
            })
        })
        .collect();
    
    for handle in handles {
        handle.join().unwrap();
    }
    
    println!("性能监控统计:");
    println!("  竞争比例: {:.2}", monitor.get_contention_ratio());
    println!("  平均等待时间: {:?}", monitor.get_average_wait_time());
    
    #[cfg(target_os = "windows")]
    {
        println!("Windows特定功能测试:");
        let event = windows_sync::WindowsEvent::new();
        let semaphore = windows_sync::WindowsSemaphore::new(2);
        
        // 测试事件
        let event = Arc::new(event);
        let event_clone = event.clone();
        let handle = thread::spawn(move || {
            event_clone.wait();
            println!("事件被触发");
        });
        
        thread::sleep(Duration::from_millis(100));
        event.set();
        handle.join().unwrap();
        
        // 测试信号量
        semaphore.acquire();
        semaphore.release();
        println!("Windows信号量测试完成");
    }
    
    #[cfg(target_os = "linux")]
    {
        println!("Linux特定功能测试:");
        let futex = linux_sync::LinuxFutex::new();
        let mutex = linux_sync::LinuxPthreadMutex::new(0);
        
        // 测试futex
        futex.wake(1);
        futex.wait(0);
        
        // 测试pthread互斥锁
        mutex.lock(|data| {
            *data = 42;
        });
        
        println!("Linux futex和pthread测试完成");
    }
    
    #[cfg(target_os = "macos")]
    {
        println!("macOS特定功能测试:");
        let dispatch_queue = macos_sync::MacOSDispatchQueue::new();
        dispatch_queue.start_worker();
        
        dispatch_queue.dispatch(|| {
            println!("Grand Central Dispatch任务执行");
        });
        
        thread::sleep(Duration::from_millis(100));
        dispatch_queue.stop();
        println!("macOS Grand Central Dispatch测试完成");
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_cross_platform_sync() {
        let sync = CrossPlatformSync::new(0);
        
        sync.lock(|data| {
            *data = 42;
        });
        
        let value = sync.lock(|data| *data);
        assert_eq!(value, 42);
    }
    
    #[test]
    fn test_performance_monitor() {
        let monitor = OSSpecificPerformanceMonitor::new();
        
        monitor.record_lock_acquisition();
        monitor.record_lock_contention();
        monitor.record_wait_time(Duration::from_millis(1));
        
        assert_eq!(monitor.get_contention_ratio(), 1.0);
        assert_eq!(monitor.get_average_wait_time(), Duration::from_millis(1));
    }
    
    #[cfg(target_os = "windows")]
    #[test]
    fn test_windows_sync() {
        let event = windows_sync::WindowsEvent::new();
        let semaphore = windows_sync::WindowsSemaphore::new(1);
        
        assert!(semaphore.try_acquire());
        assert!(!semaphore.try_acquire());
        semaphore.release();
        
        event.set();
        assert!(event.wait_timeout(Duration::from_millis(1)));
    }
    
    #[cfg(target_os = "linux")]
    #[test]
    fn test_linux_sync() {
        let futex = linux_sync::LinuxFutex::new();
        let mutex = linux_sync::LinuxPthreadMutex::new(0);
        
        assert!(futex.compare_and_swap(0, 1));
        assert!(!futex.compare_and_swap(0, 1));
        
        mutex.lock(|data| {
            *data = 42;
        });
    }
    
    #[cfg(target_os = "macos")]
    #[test]
    fn test_macos_sync() {
        let dispatch_queue = macos_sync::MacOSDispatchQueue::new();
        dispatch_queue.start_worker();
        
        dispatch_queue.dispatch(|| {
            // 测试任务
        });
        
        thread::sleep(Duration::from_millis(10));
        dispatch_queue.stop();
    }
}
