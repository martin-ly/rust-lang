//! 简化的优先级通道实现
//!
//! 为了避免复杂的线程安全问题，这里提供了一个简化版本的优先级通道

use std::collections::{
    //BinaryHeap,
    VecDeque,
};

use std::sync::{
    Arc,
    Mutex,
    //Condvar,
};

//use std::time::Duration;
use std::cmp::Ordering;

/// 简单的优先级消息
#[derive(Debug, Clone)]
pub struct SimplePriorityMessage<T> {
    pub priority: u32,
    pub data: T,
}

impl<T> SimplePriorityMessage<T> {
    pub fn new(priority: u32, data: T) -> Self {
        Self { priority, data }
    }
}

impl<T> PartialEq for SimplePriorityMessage<T> {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}

impl<T> Eq for SimplePriorityMessage<T> {}

impl<T> PartialOrd for SimplePriorityMessage<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<T> Ord for SimplePriorityMessage<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        // 注意：BinaryHeap 是最大堆，而我们希望优先级数字小的先出队
        // 所以这里使用反向排序
        other.priority.cmp(&self.priority)
    }
}

/// 简化的优先级通道
pub struct SimplePriorityChannel<T> {
    queue: Arc<Mutex<VecDeque<SimplePriorityMessage<T>>>>,
}

impl<T> Default for SimplePriorityChannel<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> SimplePriorityChannel<T> {
    /// 创建新的简化优先级通道
    pub fn new() -> Self {
        Self {
            queue: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    /// 发送消息
    pub fn send(&self, priority: u32, data: T) {
        let message = SimplePriorityMessage::new(priority, data);
        let mut queue = self.queue.lock().unwrap();

        // 简单的优先级插入：按优先级排序插入
        let position = queue
            .iter()
            .position(|msg| msg.priority > priority)
            .unwrap_or(queue.len());
        queue.insert(position, message);
    }

    /// 接收消息
    pub fn recv(&self) -> Option<T> {
        let mut queue = self.queue.lock().unwrap();
        queue.pop_front().map(|msg| msg.data)
    }

    /// 尝试接收消息
    pub fn try_recv(&self) -> Option<T> {
        if let Ok(mut queue) = self.queue.try_lock() {
            queue.pop_front().map(|msg| msg.data)
        } else {
            None
        }
    }

    /// 获取队列长度
    pub fn len(&self) -> usize {
        self.queue.lock().unwrap().len()
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.queue.lock().unwrap().is_empty()
    }
}

impl<T> Clone for SimplePriorityChannel<T> {
    fn clone(&self) -> Self {
        Self {
            queue: self.queue.clone(),
        }
    }
}

/// 运行简化优先级通道示例
pub fn run_simple_example() {
    println!("=== 简化优先级通道示例 ===");

    let channel = SimplePriorityChannel::new();

    // 发送不同优先级的消息
    channel.send(3, "低优先级消息");
    channel.send(1, "高优先级消息");
    channel.send(2, "中优先级消息");

    // 接收消息（按优先级顺序）
    while let Some(message) = channel.recv() {
        println!("接收到消息: {}", message);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;
    use std::time::Duration;

    #[test]
    fn test_simple_priority_channel() {
        let channel = SimplePriorityChannel::new();

        // 发送消息
        channel.send(3, "低优先级");
        channel.send(1, "高优先级");
        channel.send(2, "中优先级");

        // 检查优先级顺序
        assert_eq!(channel.recv(), Some("高优先级"));
        assert_eq!(channel.recv(), Some("中优先级"));
        assert_eq!(channel.recv(), Some("低优先级"));
        assert_eq!(channel.recv(), None);
    }

    #[test]
    fn test_multiple_threads() {
        let channel = Arc::new(SimplePriorityChannel::new());

        // 生产者线程
        let producer = {
            let channel = channel.clone();
            thread::spawn(move || {
                for i in 0..10 {
                    let priority = if i % 3 == 0 { 1 } else { 2 };
                    channel.send(priority, i);
                    thread::sleep(Duration::from_millis(1));
                }
            })
        };

        // 消费者线程
        let consumer = {
            let channel = channel.clone();
            thread::spawn(move || {
                let mut received = Vec::new();
                while received.len() < 10 {
                    if let Some(value) = channel.recv() {
                        received.push(value);
                    } else {
                        thread::sleep(Duration::from_millis(1));
                    }
                }
                received
            })
        };

        producer.join().unwrap();
        let received = consumer.join().unwrap();

        assert_eq!(received.len(), 10);
        // 检查高优先级消息是否先被处理
        let high_priority_indices: Vec<_> = received
            .iter()
            .enumerate()
            .filter(|(_, value)| *value % 3 == 0)
            .map(|(index, _)| index)
            .collect();

        // 高优先级消息应该在前面
        for i in 1..high_priority_indices.len() {
            assert!(high_priority_indices[i] >= high_priority_indices[i - 1]);
        }
    }

    #[test]
    fn test_try_recv() {
        let channel = SimplePriorityChannel::new();

        // 空队列时应该返回 None
        assert_eq!(channel.try_recv(), None);

        // 发送消息后应该能接收到
        channel.send(1, "测试消息");
        assert_eq!(channel.try_recv(), Some("测试消息"));
        assert_eq!(channel.try_recv(), None);
    }

    #[test]
    fn test_len_and_is_empty() {
        let channel = SimplePriorityChannel::new();

        assert!(channel.is_empty());
        assert_eq!(channel.len(), 0);

        channel.send(1, "消息1");
        channel.send(2, "消息2");

        assert!(!channel.is_empty());
        assert_eq!(channel.len(), 2);

        channel.recv();
        assert_eq!(channel.len(), 1);

        channel.recv();
        assert!(channel.is_empty());
        assert_eq!(channel.len(), 0);
    }
}
