//! Actor 模型实现
//! Actor
//! Actor 模型Implementation of
//! ## 核心概念
//! ## core concept
//! - **Message**: Actor 's间通信data structure
//! - **Scheduler**: 负责调度 Actor 处理消息
//! - **Scheduler**: Actor
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::Duration;

/// Actor 消息 trait
/// Actor message trait
pub trait Message: Send + 'static {
    /// 消息类型标识
    /// type
    fn message_type(&self) -> &'static str;
}

/// Actor trait - definition Actor 行as
/// Actor trait - definition Actor rowas
pub trait Actor: Send + 'static {
    type Message: Message;

    /// 处理消息
    /// Processes消息
    fn handle(&mut self, msg: Self::Message);

    /// Actor 名称（用于调试）
    /// Actor （）
    fn name(&self) -> &str {
        "UnnamedActor"
    }
}

pub struct Mailbox<M: Message> {
    messages: Arc<Mutex<VecDeque<M>>>,
}

impl<M: Message> Mailbox<M> {
    /// 创建新的邮箱
    /// Creates新的邮箱
    pub fn new() -> Self {
        Self {
            messages: Arc::new(Mutex::new(VecDeque::new())),
        }
    }

    /// 发送消息到邮箱
    /// Sends消息到邮箱
    /// to
    pub fn send(&self, msg: M) -> Result<(), String> {
        let mut queue = self
            .messages
            .lock()
            .map_err(|e| format!("Lock error: {}", e))?;
        queue.push_back(msg);
        Ok(())
    }

    /// 接收消息（非阻塞）
    /// Receives消息（非阻塞）
    /// （）
    pub fn try_recv(&self) -> Option<M> {
        let mut queue = self.messages.lock().ok()?;
        queue.pop_front()
    }

    /// 接收消息（阻塞，直到有消息）
    /// Receives消息（阻塞，直到有消息）
    /// （，to ）
    pub fn recv(&self) -> Option<M> {
        loop {
            if let Some(msg) = self.try_recv() {
                return Some(msg);
            }
            thread::sleep(Duration::from_millis(10));
        }
    }

    /// 检查邮箱是否为空
    /// Checks邮箱是否为空
    /// as
    pub fn is_empty(&self) -> bool {
        self.messages.lock().map(|q| q.is_empty()).unwrap_or(true)
    }

    /// 获取邮箱中的消息数量
    /// Gets邮箱中的消息数量
    /// in quantity
    /// Get邮箱in消息quantity
    pub fn len(&self) -> usize {
        self.messages.lock().map(|q| q.len()).unwrap_or(0)
    }
}

impl<M: Message> Default for Mailbox<M> {
    fn default() -> Self {
        Self::new()
    }
}

/// Actor 引用 - 用于向 Actor 发送消息
/// Actor reference - Actor
pub struct ActorRef<M: Message> {
    mailbox: Arc<Mailbox<M>>,
    name: String,
}

impl<M: Message> ActorRef<M> {
    pub fn new(mailbox: Arc<Mailbox<M>>, name: String) -> Self {
        Self { mailbox, name }
    }

    /// 发送消息到 Actor
    /// Sends消息到 Actor
    /// to Actor
    pub fn tell(&self, msg: M) -> Result<(), String> {
        self.mailbox.send(msg)
    }

    /// 获取 Actor 名称
    /// Gets Actor 名称
    /// Actor
    /// Get Actor 名称
    /// Get Actor name
    pub fn name(&self) -> &str {
        &self.name
    }
}

impl<M: Message> Clone for ActorRef<M> {
    fn clone(&self) -> Self {
        Self {
            mailbox: Arc::clone(&self.mailbox),
            name: self.name.clone(),
        }
    }
}

/// Actor 系统 - 管理多个 Actor
/// Actor system - Actor
/// Actor system - 管理多个 Actor
pub struct ActorSystem {
    actors: Vec<thread::JoinHandle<()>>,
}

impl ActorSystem {
    pub fn new() -> Self {
        Self { actors: Vec::new() }
    }

    /// 启动一个 Actor
    /// Starts一个 Actor
    /// Actor
    pub fn spawn<A>(&mut self, mut actor: A, mailbox: Arc<Mailbox<A::Message>>, name: String)
    where
        A: Actor,
    {
        let actor_name = name.clone();
        let handle = thread::spawn(move || {
            println!("Actor '{}' started", actor_name);
            loop {
                if let Some(msg) = mailbox.recv() {
                    actor.handle(msg);
                }
            }
        });
        self.actors.push(handle);
    }

    /// 等待所有 Actor 完成（通常 Actor 会一直运行）
    /// Waits for所有 Actor 完成（通常 Actor 会一直运行）
    /// etc. all Actor （ Actor Run ）
    pub fn join_all(self) {
        for handle in self.actors {
            let _ = handle.join();
        }
    }
}

impl Default for ActorSystem {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// 示例实现
// ============================================================================

/// 示例消息类型
/// examplemessagetype
/// example type
/// Example of消息type
/// Example ofmessagetype
#[derive(Debug, Clone)]
pub enum CounterMessage {
    Increment,
    Decrement,
    Get(Arc<Mutex<Option<i32>>>),
    Stop,
}

impl Message for CounterMessage {
    fn message_type(&self) -> &'static str {
        match self {
            CounterMessage::Increment => "Increment",
            CounterMessage::Decrement => "Decrement",
            CounterMessage::Get(_) => "Get",
            CounterMessage::Stop => "Stop",
        }
    }
}

/// 示例 Actor - 计数器
/// example Actor -
/// Example of Actor - 计数器
pub struct CounterActor {
    count: i32,
    name: String,
}

impl CounterActor {
    pub fn new(name: String) -> Self {
        Self { count: 0, name }
    }
}

impl Actor for CounterActor {
    type Message = CounterMessage;

    fn handle(&mut self, msg: Self::Message) {
        match msg {
            CounterMessage::Increment => {
                self.count += 1;
                println!("Actor '{}': Incremented, count = {}", self.name, self.count);
            }
            CounterMessage::Decrement => {
                self.count -= 1;
                println!("Actor '{}': Decremented, count = {}", self.name, self.count);
            }
            CounterMessage::Get(sender) => {
                let mut result = sender.lock().expect("获取发送器锁不应失败");
                *result = Some(self.count);
                println!("Actor '{}': Get request, count = {}", self.name, self.count);
            }
            CounterMessage::Stop => {
                println!("Actor '{}': Stopping", self.name);
            }
        }
    }

    fn name(&self) -> &str {
        &self.name
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Mutex};

    #[test]
    fn test_mailbox_send_recv() {
        let mailbox = Mailbox::new();
        let msg = CounterMessage::Increment;

        assert!(mailbox.send(msg.clone()).is_ok());
        assert_eq!(mailbox.len(), 1);
        assert!(!mailbox.is_empty());

        let received = mailbox.try_recv();
        assert!(received.is_some());
        assert!(mailbox.is_empty());
    }

    #[test]
    fn test_actor_ref() {
        let mailbox = Arc::new(Mailbox::new());
        let actor_ref = ActorRef::new(mailbox.clone(), "TestActor".to_string());

        assert_eq!(actor_ref.name(), "TestActor");
        assert!(actor_ref.tell(CounterMessage::Increment).is_ok());
        assert_eq!(mailbox.len(), 1);
    }

    #[test]
    fn test_counter_actor() {
        let mut counter = CounterActor::new("TestCounter".to_string());
        assert_eq!(counter.name(), "TestCounter");

        counter.handle(CounterMessage::Increment);
        counter.handle(CounterMessage::Increment);
        counter.handle(CounterMessage::Decrement);

        let result = Arc::new(Mutex::new(None));
        counter.handle(CounterMessage::Get(result.clone()));

        let count = result.lock().expect("获取结果锁不应失败");
        assert_eq!(*count, Some(1));
    }
}
