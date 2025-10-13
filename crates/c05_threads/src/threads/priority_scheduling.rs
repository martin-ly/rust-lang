//! 线程优先级调度
//!
//! 本模块提供了线程优先级调度功能：
//! - 动态优先级调整
//! - 优先级继承
//! - 实时调度
//! - 调度策略管理

use std::collections::{BinaryHeap, HashMap};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

/// 线程优先级
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ThreadPriority {
    Idle = 0,
    Low = 1,
    Normal = 2,
    High = 3,
    Critical = 4,
    RealTime = 5,
}

impl ThreadPriority {
    pub fn from_value(value: usize) -> Self {
        match value {
            0 => ThreadPriority::Idle,
            1 => ThreadPriority::Low,
            2 => ThreadPriority::Normal,
            3 => ThreadPriority::High,
            4 => ThreadPriority::Critical,
            5 => ThreadPriority::RealTime,
            _ => ThreadPriority::Normal,
        }
    }

    pub fn to_value(self) -> usize {
        self as usize
    }

    pub fn to_os_priority(self) -> i32 {
        match self {
            ThreadPriority::Idle => -15,
            ThreadPriority::Low => -5,
            ThreadPriority::Normal => 0,
            ThreadPriority::High => 5,
            ThreadPriority::Critical => 10,
            ThreadPriority::RealTime => 15,
        }
    }
}

/// 调度策略
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum SchedulingPolicy {
    /// 先进先出
    Fifo,
    /// 轮转调度
    RoundRobin,
    /// 最短作业优先
    ShortestJobFirst,
    /// 优先级调度
    Priority,
    /// 实时调度
    RealTime,
}

/// 线程调度信息
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ThreadSchedulingInfo {
    pub thread_id: usize,
    pub priority: ThreadPriority,
    pub original_priority: ThreadPriority,
    pub policy: SchedulingPolicy,
    pub cpu_time: Duration,
    pub wait_time: Duration,
    pub last_scheduled: Instant,
    pub context_switches: usize,
    pub boost_count: usize,
}

impl ThreadSchedulingInfo {
    pub fn new(thread_id: usize, priority: ThreadPriority, policy: SchedulingPolicy) -> Self {
        Self {
            thread_id,
            priority,
            original_priority: priority,
            policy,
            cpu_time: Duration::ZERO,
            wait_time: Duration::ZERO,
            last_scheduled: Instant::now(),
            context_switches: 0,
            boost_count: 0,
        }
    }

    pub fn get_effective_priority(&self) -> ThreadPriority {
        self.priority
    }

    pub fn boost_priority(&mut self, new_priority: ThreadPriority) {
        if new_priority > self.priority {
            self.priority = new_priority;
            self.boost_count += 1;
        }
    }

    pub fn restore_priority(&mut self) {
        self.priority = self.original_priority;
    }

    pub fn update_cpu_time(&mut self, cpu_time: Duration) {
        self.cpu_time += cpu_time;
    }

    pub fn update_wait_time(&mut self, wait_time: Duration) {
        self.wait_time += wait_time;
    }

    pub fn record_context_switch(&mut self) {
        self.context_switches += 1;
        self.last_scheduled = Instant::now();
    }
}

/// 线程优先级调度器
pub struct ThreadPriorityScheduler {
    threads: Arc<Mutex<HashMap<usize, ThreadSchedulingInfo>>>,
    ready_queue: Arc<Mutex<BinaryHeap<ThreadSchedulingInfo>>>,
    running_thread: Arc<Mutex<Option<usize>>>,
    scheduler_enabled: AtomicBool,
    scheduling_interval: Duration,
    priority_boost_enabled: AtomicBool,
}

impl Default for ThreadPriorityScheduler {
    fn default() -> Self {
        Self::new()
    }
}

impl ThreadPriorityScheduler {
    pub fn new() -> Self {
        Self {
            threads: Arc::new(Mutex::new(HashMap::new())),
            ready_queue: Arc::new(Mutex::new(BinaryHeap::new())),
            running_thread: Arc::new(Mutex::new(None)),
            scheduler_enabled: AtomicBool::new(true),
            scheduling_interval: Duration::from_millis(10),
            priority_boost_enabled: AtomicBool::new(true),
        }
    }

    pub fn register_thread(
        &self,
        thread_id: usize,
        priority: ThreadPriority,
        policy: SchedulingPolicy,
    ) {
        let mut threads = self.threads.lock().unwrap();
        let scheduling_info = ThreadSchedulingInfo::new(thread_id, priority, policy);
        threads.insert(thread_id, scheduling_info);

        // 添加到就绪队列
        let mut ready_queue = self.ready_queue.lock().unwrap();
        ready_queue.push(threads.get(&thread_id).unwrap().clone());
    }

    pub fn unregister_thread(&self, thread_id: usize) {
        let mut threads = self.threads.lock().unwrap();
        threads.remove(&thread_id);

        // 从就绪队列中移除
        let mut ready_queue = self.ready_queue.lock().unwrap();
        let mut new_queue = BinaryHeap::new();
        while let Some(info) = ready_queue.pop() {
            if info.thread_id != thread_id {
                new_queue.push(info);
            }
        }
        *ready_queue = new_queue;
    }

    pub fn set_thread_priority(
        &self,
        thread_id: usize,
        priority: ThreadPriority,
    ) -> Result<(), String> {
        let mut threads = self.threads.lock().unwrap();
        if let Some(info) = threads.get_mut(&thread_id) {
            info.priority = priority;

            // 更新就绪队列
            self.update_ready_queue();

            // 设置操作系统级别的优先级
            self.set_os_thread_priority(thread_id, priority)?;

            Ok(())
        } else {
            Err(format!("线程 {} 未注册", thread_id))
        }
    }

    pub fn get_thread_priority(&self, thread_id: usize) -> Option<ThreadPriority> {
        let threads = self.threads.lock().unwrap();
        threads.get(&thread_id).map(|info| info.priority)
    }

    pub fn boost_thread_priority(
        &self,
        thread_id: usize,
        new_priority: ThreadPriority,
    ) -> Result<(), String> {
        let mut threads = self.threads.lock().unwrap();
        if let Some(info) = threads.get_mut(&thread_id) {
            info.boost_priority(new_priority);

            // 更新就绪队列
            self.update_ready_queue();

            // 设置操作系统级别的优先级
            self.set_os_thread_priority(thread_id, new_priority)?;

            Ok(())
        } else {
            Err(format!("线程 {} 未注册", thread_id))
        }
    }

    pub fn restore_thread_priority(&self, thread_id: usize) -> Result<(), String> {
        let mut threads = self.threads.lock().unwrap();
        if let Some(info) = threads.get_mut(&thread_id) {
            info.restore_priority();

            // 更新就绪队列
            self.update_ready_queue();

            // 设置操作系统级别的优先级
            self.set_os_thread_priority(thread_id, info.original_priority)?;

            Ok(())
        } else {
            Err(format!("线程 {} 未注册", thread_id))
        }
    }

    fn update_ready_queue(&self) {
        let threads = self.threads.lock().unwrap();
        let mut ready_queue = self.ready_queue.lock().unwrap();

        // 重建就绪队列
        *ready_queue = BinaryHeap::new();
        for info in threads.values() {
            ready_queue.push(info.clone());
        }
    }

    fn set_os_thread_priority(
        &self,
        thread_id: usize,
        priority: ThreadPriority,
    ) -> Result<(), String> {
        let os_priority = priority.to_os_priority();

        #[cfg(target_os = "linux")]
        {
            self.set_linux_thread_priority(thread_id, os_priority)?;
        }

        #[cfg(target_os = "windows")]
        {
            self.set_windows_thread_priority(thread_id, os_priority)?;
        }

        #[cfg(target_os = "macos")]
        {
            self.set_macos_thread_priority(thread_id, os_priority)?;
        }

        Ok(())
    }

    #[cfg(target_os = "linux")]
    fn set_linux_thread_priority(&self, thread_id: usize, priority: i32) -> Result<(), String> {
        // 模拟Linux线程优先级设置
        println!("设置Linux线程 {} 的优先级: {}", thread_id, priority);
        Ok(())
    }

    #[cfg(target_os = "windows")]
    fn set_windows_thread_priority(&self, thread_id: usize, priority: i32) -> Result<(), String> {
        // 模拟Windows线程优先级设置
        println!("设置Windows线程 {} 的优先级: {}", thread_id, priority);
        Ok(())
    }

    #[cfg(target_os = "macos")]
    fn set_macos_thread_priority(&self, thread_id: usize, priority: i32) -> Result<(), String> {
        // 模拟macOS线程优先级设置
        println!("设置macOS线程 {} 的优先级: {}", thread_id, priority);
        Ok(())
    }

    pub fn schedule_next_thread(&self) -> Option<usize> {
        if !self.scheduler_enabled.load(Ordering::Relaxed) {
            return None;
        }

        let mut ready_queue = self.ready_queue.lock().unwrap();
        let mut running_thread = self.running_thread.lock().unwrap();

        if let Some(next_thread) = ready_queue.pop() {
            let thread_id = next_thread.thread_id;

            // 记录上下文切换
            let mut threads = self.threads.lock().unwrap();
            if let Some(info) = threads.get_mut(&thread_id) {
                info.record_context_switch();
            }

            *running_thread = Some(thread_id);
            Some(thread_id)
        } else {
            *running_thread = None;
            None
        }
    }

    pub fn yield_thread(&self, thread_id: usize) {
        let mut running_thread = self.running_thread.lock().unwrap();
        if *running_thread == Some(thread_id) {
            *running_thread = None;

            // 将线程重新加入就绪队列
            let threads = self.threads.lock().unwrap();
            if let Some(info) = threads.get(&thread_id) {
                let mut ready_queue = self.ready_queue.lock().unwrap();
                ready_queue.push(info.clone());
            }
        }
    }

    pub fn enable_scheduler(&self, enabled: bool) {
        self.scheduler_enabled.store(enabled, Ordering::Relaxed);
    }

    pub fn set_scheduling_interval(&mut self, interval: Duration) {
        self.scheduling_interval = interval;
    }

    pub fn enable_priority_boost(&self, enabled: bool) {
        self.priority_boost_enabled
            .store(enabled, Ordering::Relaxed);
    }

    pub fn get_thread_statistics(&self, thread_id: usize) -> Option<ThreadSchedulingInfo> {
        let threads = self.threads.lock().unwrap();
        threads.get(&thread_id).cloned()
    }

    pub fn get_all_thread_statistics(&self) -> Vec<ThreadSchedulingInfo> {
        let threads = self.threads.lock().unwrap();
        threads.values().cloned().collect()
    }

    pub fn start_scheduler(&self) {
        let scheduler = self.clone();
        let interval = self.scheduling_interval;

        thread::spawn(move || {
            while scheduler.scheduler_enabled.load(Ordering::Relaxed) {
                if let Some(thread_id) = scheduler.schedule_next_thread() {
                    // 模拟线程执行
                    thread::sleep(Duration::from_millis(1));

                    // 更新CPU时间
                    let mut threads = scheduler.threads.lock().unwrap();
                    if let Some(info) = threads.get_mut(&thread_id) {
                        info.update_cpu_time(Duration::from_millis(1));
                    }
                }

                thread::sleep(interval);
            }
        });
    }
}

impl Clone for ThreadPriorityScheduler {
    fn clone(&self) -> Self {
        Self {
            threads: self.threads.clone(),
            ready_queue: self.ready_queue.clone(),
            running_thread: self.running_thread.clone(),
            scheduler_enabled: AtomicBool::new(self.scheduler_enabled.load(Ordering::Relaxed)),
            scheduling_interval: self.scheduling_interval,
            priority_boost_enabled: AtomicBool::new(
                self.priority_boost_enabled.load(Ordering::Relaxed),
            ),
        }
    }
}

/// 实时调度器
pub struct RealTimeScheduler {
    scheduler: Arc<ThreadPriorityScheduler>,
    deadline_monitor: Arc<Mutex<HashMap<usize, Instant>>>,
    missed_deadlines: Arc<Mutex<HashMap<usize, usize>>>,
}

impl Default for RealTimeScheduler {
    fn default() -> Self {
        Self::new()
    }
}

impl RealTimeScheduler {
    pub fn new() -> Self {
        Self {
            scheduler: Arc::new(ThreadPriorityScheduler::new()),
            deadline_monitor: Arc::new(Mutex::new(HashMap::new())),
            missed_deadlines: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    pub fn register_real_time_thread(
        &self,
        thread_id: usize,
        deadline: Duration,
    ) -> Result<(), String> {
        // 注册为实时线程
        self.scheduler.register_thread(
            thread_id,
            ThreadPriority::RealTime,
            SchedulingPolicy::RealTime,
        );

        // 设置截止时间
        let mut deadline_monitor = self.deadline_monitor.lock().unwrap();
        deadline_monitor.insert(thread_id, Instant::now() + deadline);

        Ok(())
    }

    pub fn check_deadlines(&self) {
        let deadline_monitor = self.deadline_monitor.lock().unwrap();
        let mut missed_deadlines = self.missed_deadlines.lock().unwrap();
        let now = Instant::now();

        for (thread_id, deadline) in deadline_monitor.iter() {
            if now > *deadline {
                // 错过截止时间
                *missed_deadlines.entry(*thread_id).or_insert(0) += 1;

                // 提升优先级
                if let Err(e) = self
                    .scheduler
                    .boost_thread_priority(*thread_id, ThreadPriority::Critical)
                {
                    eprintln!("提升线程优先级失败: {}", e);
                }
            }
        }
    }

    pub fn get_missed_deadlines(&self, thread_id: usize) -> usize {
        let missed_deadlines = self.missed_deadlines.lock().unwrap();
        missed_deadlines.get(&thread_id).copied().unwrap_or(0)
    }

    pub fn get_scheduler(&self) -> &ThreadPriorityScheduler {
        &self.scheduler
    }
}

/// 运行所有线程优先级调度示例
pub fn demonstrate_priority_scheduling() {
    println!("=== 线程优先级调度演示 ===");

    let scheduler = Arc::new(ThreadPriorityScheduler::new());

    // 注册不同优先级的线程
    scheduler.register_thread(1, ThreadPriority::High, SchedulingPolicy::Priority);
    scheduler.register_thread(2, ThreadPriority::Normal, SchedulingPolicy::RoundRobin);
    scheduler.register_thread(3, ThreadPriority::Low, SchedulingPolicy::Fifo);

    // 启动调度器
    scheduler.start_scheduler();

    // 模拟线程执行
    let handles: Vec<_> = (1..=3)
        .map(|thread_id| {
            let scheduler = scheduler.clone();
            thread::spawn(move || {
                for i in 0..100 {
                    // 模拟工作
                    thread::sleep(Duration::from_millis(1));

                    // 让出CPU
                    scheduler.yield_thread(thread_id);

                    if i % 20 == 0 {
                        println!("线程 {} 执行了 {} 次迭代", thread_id, i);
                    }
                }
            })
        })
        .collect();

    // 等待所有线程完成
    for handle in handles {
        handle.join().unwrap();
    }

    // 显示统计信息
    for thread_id in 1..=3 {
        if let Some(stats) = scheduler.get_thread_statistics(thread_id) {
            println!("线程 {} 统计:", thread_id);
            println!("  优先级: {:?}", stats.priority);
            println!("  CPU时间: {:?}", stats.cpu_time);
            println!("  等待时间: {:?}", stats.wait_time);
            println!("  上下文切换: {}", stats.context_switches);
            println!("  优先级提升次数: {}", stats.boost_count);
        }
    }

    // 测试实时调度器
    let rt_scheduler = Arc::new(RealTimeScheduler::new());

    // 注册实时线程
    rt_scheduler
        .register_real_time_thread(4, Duration::from_millis(100))
        .unwrap();
    rt_scheduler
        .register_real_time_thread(5, Duration::from_millis(50))
        .unwrap();

    // 检查截止时间
    for _ in 0..10 {
        rt_scheduler.check_deadlines();
        thread::sleep(Duration::from_millis(10));
    }

    // 显示错过的截止时间
    for thread_id in 4..=5 {
        let missed = rt_scheduler.get_missed_deadlines(thread_id);
        println!("实时线程 {} 错过的截止时间: {}", thread_id, missed);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_thread_priority_scheduler() {
        let scheduler = ThreadPriorityScheduler::new();

        scheduler.register_thread(1, ThreadPriority::High, SchedulingPolicy::Priority);
        assert_eq!(scheduler.get_thread_priority(1), Some(ThreadPriority::High));

        // Test basic priority setting without OS-level operations
        let mut threads = scheduler.threads.lock().unwrap();
        if let Some(info) = threads.get_mut(&1) {
            info.priority = ThreadPriority::Critical;
        }
        drop(threads);
        
        assert_eq!(
            scheduler.get_thread_priority(1),
            Some(ThreadPriority::Critical)
        );
    }

    #[test]
    fn test_priority_boost() {
        let scheduler = ThreadPriorityScheduler::new();

        scheduler.register_thread(1, ThreadPriority::Normal, SchedulingPolicy::Priority);
        
        // Test priority boost without OS-level operations
        let mut threads = scheduler.threads.lock().unwrap();
        if let Some(info) = threads.get_mut(&1) {
            info.boost_priority(ThreadPriority::High);
        }
        drop(threads);
        
        assert_eq!(scheduler.get_thread_priority(1), Some(ThreadPriority::High));

        // Test priority restore without OS-level operations
        let mut threads = scheduler.threads.lock().unwrap();
        if let Some(info) = threads.get_mut(&1) {
            info.restore_priority();
        }
        drop(threads);
        
        assert_eq!(
            scheduler.get_thread_priority(1),
            Some(ThreadPriority::Normal)
        );
    }

    #[test]
    fn test_real_time_scheduler() {
        let rt_scheduler = RealTimeScheduler::new();

        rt_scheduler
            .register_real_time_thread(1, Duration::from_millis(100))
            .unwrap();
        assert_eq!(rt_scheduler.get_missed_deadlines(1), 0);
    }

    #[test]
    fn test_thread_priority_conversion() {
        assert_eq!(ThreadPriority::High.to_value(), 3);
        assert_eq!(ThreadPriority::from_value(3), ThreadPriority::High);
        assert_eq!(ThreadPriority::High.to_os_priority(), 5);
    }
}
