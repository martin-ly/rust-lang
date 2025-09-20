//! 优先级通道实现
//!
//! 本模块提供了多种优先级通道实现：
//! - 基于优先级的消息通道
//! - 多级优先级通道
//! - 动态优先级调整通道
//! - 公平调度优先级通道

use std::cmp::Ordering;
use std::collections::{BinaryHeap, VecDeque};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::{Duration, Instant};
// use crossbeam_channel::{
//     bounded,
//     unbounded,
//     Receiver,
//     Sender
// };

/// 优先级消息
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PriorityMessage<T: PartialEq + Eq> {
    priority: u32,
    timestamp: Instant,
    data: T,
}

impl<T: PartialEq + Eq> PriorityMessage<T> {
    pub fn new(priority: u32, data: T) -> Self {
        Self {
            priority,
            timestamp: Instant::now(),
            data,
        }
    }

    pub fn into_data(self) -> T {
        self.data
    }

    pub fn priority(&self) -> u32 {
        self.priority
    }

    pub fn timestamp(&self) -> Instant {
        self.timestamp
    }
}

impl<T: PartialEq + Eq> PartialOrd for PriorityMessage<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        // BinaryHeap 是最大堆：我们需要“更小的优先级值更大”。
        // 同优先级时，时间戳更早者更大（先出堆）。
        Some(
            self.priority
                .cmp(&other.priority)
                .reverse()
                .then(other.timestamp.cmp(&self.timestamp)),
        )
    }
}

impl<T: Eq> Ord for PriorityMessage<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // 同 PartialOrd 逻辑保持一致
        self.priority
            .cmp(&other.priority)
            .reverse()
            .then(other.timestamp.cmp(&self.timestamp))
    }
}

/// 基于优先级的消息通道
///
/// 使用二进制堆实现优先级队列
pub struct PriorityChannel<T: Eq> {
    queue: Arc<Mutex<BinaryHeap<PriorityMessage<T>>>>,
    notifier: Arc<Condvar>,
    capacity: Option<usize>,
}

impl<T: PartialEq + Eq> Default for PriorityChannel<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: PartialEq + Eq> PriorityChannel<T> {
    /// 创建新的优先级通道
    pub fn new() -> Self {
        Self {
            queue: Arc::new(Mutex::new(BinaryHeap::new())),
            notifier: Arc::new(Condvar::new()),
            capacity: None,
        }
    }

    /// 创建有容量限制的优先级通道
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            queue: Arc::new(Mutex::new(BinaryHeap::new())),
            notifier: Arc::new(Condvar::new()),
            capacity: Some(capacity),
        }
    }

    /// 发送优先级消息
    pub fn send(&self, priority: u32, data: T) -> Result<(), T> {
        let message = PriorityMessage::new(priority, data);

        let mut queue = self.queue.lock().unwrap();

        // 检查容量限制
        if let Some(capacity) = self.capacity
            && queue.len() >= capacity {
                return Err(message.into_data());
            }

        queue.push(message);
        self.notifier.notify_one();
        Ok(())
    }

    /// 接收优先级消息
    pub fn recv(&self) -> Option<T> {
        let mut queue = self.queue.lock().unwrap();

        while queue.is_empty() {
            queue = self.notifier.wait(queue).unwrap();
        }

        queue.pop().map(|msg| msg.into_data())
    }

    /// 尝试接收优先级消息
    pub fn try_recv(&self) -> Option<T> {
        let mut queue = self.queue.lock().unwrap();
        queue.pop().map(|msg| msg.into_data())
    }

    /// 带超时的接收
    pub fn recv_timeout(&self, timeout: Duration) -> Option<T> {
        let mut queue = self.queue.lock().unwrap();

        while queue.is_empty() {
            let result = self.notifier.wait_timeout(queue, timeout).unwrap();
            queue = result.0;

            if result.1.timed_out() {
                return None;
            }
        }

        queue.pop().map(|msg| msg.into_data())
    }

    /// 获取队列长度
    pub fn len(&self) -> usize {
        self.queue.lock().unwrap().len()
    }

    /// 检查队列是否为空
    pub fn is_empty(&self) -> bool {
        self.queue.lock().unwrap().is_empty()
    }

    /// 运行优先级通道示例
    pub fn run_example() {
        println!("=== 优先级通道示例 ===");

        let channel = Arc::new(PriorityChannel::new());

        // 创建发送者线程
        let sender = {
            let channel = channel.clone();
            thread::spawn(move || {
                // 发送不同优先级的消息
                channel.send(3, "低优先级消息1").unwrap();
                channel.send(1, "高优先级消息1").unwrap();
                channel.send(2, "中优先级消息1").unwrap();
                channel.send(1, "高优先级消息2").unwrap();
                channel.send(3, "低优先级消息2").unwrap();
                println!("发送者完成");
            })
        };

        // 创建接收者线程
        let receiver = {
            let channel = channel.clone();
            thread::spawn(move || {
                let mut count = 0;
                while count < 5 {
                    if let Some(message) = channel.recv() {
                        println!("接收到消息: {}", message);
                        count += 1;
                    }
                }
                println!("接收者完成");
            })
        };

        sender.join().unwrap();
        receiver.join().unwrap();
    }
}

/// 多级优先级通道
///
/// 支持多个优先级级别的通道
pub struct MultiLevelPriorityChannel<T: Eq> {
    channels: Vec<Arc<PriorityChannel<T>>>,
    level_count: usize,
}

impl<T: PartialEq + Eq> MultiLevelPriorityChannel<T> {
    /// 创建新的多级优先级通道
    pub fn new(level_count: usize) -> Self {
        let channels: Vec<Arc<PriorityChannel<T>>> = (0..level_count)
            .map(|_| Arc::new(PriorityChannel::new()))
            .collect();

        Self {
            channels,
            level_count,
        }
    }

    /// 发送消息到指定级别
    pub fn send_to_level(&self, level: usize, data: T) -> Result<(), T> {
        if level >= self.level_count {
            return Err(data);
        }

        self.channels[level].send(0, data) // 在指定级别内使用最高优先级
    }

    /// 接收消息（按级别优先级）
    pub fn recv(&self) -> Option<T> {
        // 从高优先级级别开始接收
        for level in 0..self.level_count {
            if let Some(message) = self.channels[level].try_recv() {
                return Some(message);
            }
        }

        // 如果没有消息，等待任意级别的消息
        for level in 0..self.level_count {
            if let Some(message) = self.channels[level].recv() {
                return Some(message);
            }
        }

        None
    }

    /// 运行多级优先级通道示例
    pub fn run_example() {
        println!("=== 多级优先级通道示例 ===");

        let channel = Arc::new(MultiLevelPriorityChannel::new(3));

        // 创建发送者线程
        let sender = {
            let channel = channel.clone();
            thread::spawn(move || {
                // 发送到不同级别
                channel.send_to_level(2, "级别2消息1").unwrap();
                channel.send_to_level(0, "级别0消息1").unwrap();
                channel.send_to_level(1, "级别1消息1").unwrap();
                channel.send_to_level(0, "级别0消息2").unwrap();
                channel.send_to_level(2, "级别2消息2").unwrap();
                println!("发送者完成");
            })
        };

        // 创建接收者线程
        let receiver = {
            let channel = channel.clone();
            thread::spawn(move || {
                let mut count = 0;
                while count < 5 {
                    if let Some(message) = channel.recv() {
                        println!("接收到消息: {}", message);
                        count += 1;
                    }
                }
                println!("接收者完成");
            })
        };

        sender.join().unwrap();
        receiver.join().unwrap();
    }
}

/// 动态优先级调整通道
///
/// 支持运行时调整消息优先级的通道
pub struct DynamicPriorityChannel<T: Eq> {
    queue: Arc<Mutex<BinaryHeap<PriorityMessage<T>>>>,
    notifier: Arc<Condvar>,
    priority_adjuster: Arc<dyn Fn(&T) -> u32 + Send + Sync>,
}

impl<T: PartialEq + Eq> DynamicPriorityChannel<T> {
    /// 创建新的动态优先级通道
    pub fn new<F>(priority_adjuster: F) -> Self
    where
        F: Fn(&T) -> u32 + Send + Sync + 'static,
    {
        Self {
            queue: Arc::new(Mutex::new(BinaryHeap::new())),
            notifier: Arc::new(Condvar::new()),
            priority_adjuster: Arc::new(priority_adjuster),
        }
    }

    /// 发送消息（动态计算优先级）
    pub fn send(&self, data: T) -> Result<(), T> {
        let priority = (self.priority_adjuster)(&data);
        let message = PriorityMessage::new(priority, data);

        let mut queue = self.queue.lock().unwrap();
        queue.push(message);
        self.notifier.notify_one();
        Ok(())
    }

    /// 接收消息
    pub fn recv(&self) -> Option<T> {
        let mut queue = self.queue.lock().unwrap();

        while queue.is_empty() {
            queue = self.notifier.wait(queue).unwrap();
        }

        queue.pop().map(|msg| msg.into_data())
    }

    /// 运行动态优先级通道示例
    pub fn run_example() {
        println!("=== 动态优先级通道示例 ===");

        let channel = Arc::new(DynamicPriorityChannel::new(|data: &String| {
            // 根据消息长度动态调整优先级
            if data.len() < 5 {
                1 // 短消息高优先级
            } else if data.len() < 10 {
                2 // 中等消息中优先级
            } else {
                3 // 长消息低优先级
            }
        }));

        // 创建发送者线程
        let sender = {
            let channel = channel.clone();
            thread::spawn(move || {
                channel.send("短消息".to_string()).unwrap();
                channel
                    .send("这是一个很长的消息，应该具有较低的优先级".to_string())
                    .unwrap();
                channel.send("中等".to_string()).unwrap();
                channel.send("这是一个中等长度的消息".to_string()).unwrap();
                channel.send("长".to_string()).unwrap();
                println!("发送者完成");
            })
        };

        // 创建接收者线程
        let receiver = {
            let channel = channel.clone();
            thread::spawn(move || {
                let mut count = 0;
                while count < 5 {
                    if let Some(message) = channel.recv() {
                        println!("接收到消息: {}", message);
                        count += 1;
                    }
                }
                println!("接收者完成");
            })
        };

        sender.join().unwrap();
        receiver.join().unwrap();
    }
}

/// 公平调度优先级通道
///
/// 在保证优先级的同时，确保低优先级消息不会被饿死
pub struct FairSchedulingPriorityChannel<T: Eq> {
    high_priority_queue: Arc<Mutex<VecDeque<PriorityMessage<T>>>>,
    low_priority_queue: Arc<Mutex<VecDeque<PriorityMessage<T>>>>,
    notifier: Arc<Condvar>,
    high_priority_threshold: u32,
    low_priority_counter: Arc<Mutex<usize>>,
    fairness_ratio: usize,
}

impl<T: PartialEq + Eq> FairSchedulingPriorityChannel<T> {
    /// 创建新的公平调度优先级通道
    pub fn new(high_priority_threshold: u32, fairness_ratio: usize) -> Self {
        Self {
            high_priority_queue: Arc::new(Mutex::new(VecDeque::new())),
            low_priority_queue: Arc::new(Mutex::new(VecDeque::new())),
            notifier: Arc::new(Condvar::new()),
            high_priority_threshold,
            low_priority_counter: Arc::new(Mutex::new(0)),
            fairness_ratio,
        }
    }

    /// 发送消息
    pub fn send(&self, priority: u32, data: T) -> Result<(), T> {
        let message = PriorityMessage::new(priority, data);

        if priority <= self.high_priority_threshold {
            let mut queue = self.high_priority_queue.lock().unwrap();
            queue.push_back(message);
        } else {
            let mut queue = self.low_priority_queue.lock().unwrap();
            queue.push_back(message);
        }

        self.notifier.notify_one();
        Ok(())
    }

    /// 接收消息（公平调度）
    pub fn recv(&self) -> Option<T> {
        loop {
            // 快路径：尝试一次无阻塞检查
            if let Some(msg) = {
                let mut h = self.high_priority_queue.lock().unwrap();
                h.pop_front()
            } {
                return Some(msg.into_data());
            }
            if let Some(msg) = {
                let mut l = self.low_priority_queue.lock().unwrap();
                l.pop_front()
            } {
                // 计数更新
                let mut c = self.low_priority_counter.lock().unwrap();
                *c = c.saturating_add(1) % self.fairness_ratio.max(1);
                return Some(msg.into_data());
            }

            // 阻塞等待任一队列有元素
            let mut guard = self.high_priority_queue.lock().unwrap();
            guard = self.notifier.wait(guard).unwrap();
            drop(guard);
        }
    }

    /// 运行公平调度优先级通道示例
    pub fn run_example() {
        println!("=== 公平调度优先级通道示例 ===");

        let channel = Arc::new(FairSchedulingPriorityChannel::new(2, 3));

        // 创建发送者线程
        let sender = {
            let channel = channel.clone();
            thread::spawn(move || {
                // 发送大量高优先级消息
                for i in 0..10 {
                    channel.send(1, format!("高优先级消息{}", i)).unwrap();
                }

                // 发送一些低优先级消息
                for i in 0..5 {
                    channel.send(5, format!("低优先级消息{}", i)).unwrap();
                }

                println!("发送者完成");
            })
        };

        // 创建接收者线程
        let receiver = {
            let channel = channel.clone();
            thread::spawn(move || {
                let mut count = 0;
                while count < 15 {
                    if let Some(message) = channel.recv() {
                        println!("接收到消息: {}", message);
                        count += 1;
                    }
                }
                println!("接收者完成");
            })
        };

        sender.join().unwrap();
        receiver.join().unwrap();
    }
}

/// 运行所有优先级通道示例
pub fn demonstrate_priority_channels() {
    println!("=== 优先级通道演示 ===");

    PriorityChannel::<String>::run_example();
    MultiLevelPriorityChannel::<String>::run_example();
    DynamicPriorityChannel::<String>::run_example();
    FairSchedulingPriorityChannel::<String>::run_example();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_priority_channel() {
        let channel = PriorityChannel::new();

        // 测试发送和接收
        channel.send(3, "低优先级").unwrap();
        channel.send(1, "高优先级").unwrap();
        channel.send(2, "中优先级").unwrap();

        // 应该按优先级顺序接收
        assert_eq!(channel.recv(), Some("高优先级"));
        assert_eq!(channel.recv(), Some("中优先级"));
        assert_eq!(channel.recv(), Some("低优先级"));
    }

    #[test]
    fn test_multi_level_priority_channel() {
        let channel = MultiLevelPriorityChannel::new(3);

        // 测试发送到不同级别
        channel.send_to_level(2, "级别2").unwrap();
        channel.send_to_level(0, "级别0").unwrap();
        channel.send_to_level(1, "级别1").unwrap();

        // 应该按级别优先级接收
        assert_eq!(channel.recv(), Some("级别0"));
        assert_eq!(channel.recv(), Some("级别1"));
        assert_eq!(channel.recv(), Some("级别2"));
    }

    #[test]
    fn test_dynamic_priority_channel() {
        let channel =
            DynamicPriorityChannel::new(|data: &String| if data.len() < 5 { 1 } else { 3 });

        // 测试动态优先级
        channel.send("短".to_string()).unwrap();
        channel.send("这是一个很长的消息".to_string()).unwrap();

        // 短消息应该优先
        assert_eq!(channel.recv(), Some("短".to_string()));
        assert_eq!(channel.recv(), Some("这是一个很长的消息".to_string()));
    }

    #[test]
    fn test_fair_scheduling_priority_channel() {
        let channel = FairSchedulingPriorityChannel::new(2, 2);

        // 测试公平调度
        channel.send(1, "高优先级1").unwrap();
        channel.send(1, "高优先级2").unwrap();
        channel.send(5, "低优先级1").unwrap();
        channel.send(1, "高优先级3").unwrap();

        // 应该按公平调度接收
        let mut messages = Vec::new();
        for _ in 0..4 {
            if let Some(msg) = channel.recv() {
                messages.push(msg);
            }
        }

        assert_eq!(messages.len(), 4);
    }
}
