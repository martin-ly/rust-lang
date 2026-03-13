//! 异步消息传递示例
//! 
//! 展示如何使用异步编程进行消息传递和事件处理
use std::sync::Arc;
use std::time::Duration;
use anyhow::Result;
use tokio::time::sleep;
use tokio::sync::{mpsc, broadcast, RwLock};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 消息类型枚举
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MessageType {
    Text(String),
    Image(Vec<u8>),
    File(String, Vec<u8>),
    Command(String),
    Notification(String),
}

/// 消息结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Message {
    pub id: u64,
    pub sender: String,
    pub recipient: String,
    pub message_type: MessageType,
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub priority: MessagePriority,
}

/// 消息优先级
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum MessagePriority {
    Low = 1,
    Normal = 2,
    High = 3,
    Critical = 4,
}

/// 消息处理器trait
#[async_trait::async_trait]
pub trait MessageHandler: Send + Sync {
    async fn handle_message(&self, message: Message) -> Result<()>;
    fn get_handler_name(&self) -> &str;
}

/// 文本消息处理器
pub struct TextMessageHandler {
    name: String,
}

impl TextMessageHandler {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
        }
    }
}

#[async_trait::async_trait]
impl MessageHandler for TextMessageHandler {
    async fn handle_message(&self, message: Message) -> Result<()> {
        if let MessageType::Text(content) = &message.message_type {
            println!("📝 [{}] 处理文本消息: {}", self.name, content);
            sleep(Duration::from_millis(10)).await;
        }
        Ok(())
    }
    
    fn get_handler_name(&self) -> &str {
        &self.name
    }
}

/// 图片消息处理器
pub struct ImageMessageHandler {
    name: String,
}

impl ImageMessageHandler {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
        }
    }
}

#[async_trait::async_trait]
impl MessageHandler for ImageMessageHandler {
    async fn handle_message(&self, message: Message) -> Result<()> {
        if let MessageType::Image(data) = &message.message_type {
            println!("🖼️ [{}] 处理图片消息，大小: {} bytes", self.name, data.len());
            sleep(Duration::from_millis(50)).await;
        }
        Ok(())
    }
    
    fn get_handler_name(&self) -> &str {
        &self.name
    }
}

/// 命令消息处理器
pub struct CommandMessageHandler {
    name: String,
}

impl CommandMessageHandler {
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
        }
    }
}

#[async_trait::async_trait]
impl MessageHandler for CommandMessageHandler {
    async fn handle_message(&self, message: Message) -> Result<()> {
        if let MessageType::Command(cmd) = &message.message_type {
            println!("⚡ [{}] 执行命令: {}", self.name, cmd);
            sleep(Duration::from_millis(20)).await;
        }
        Ok(())
    }
    
    fn get_handler_name(&self) -> &str {
        &self.name
    }
}

/// 异步消息系统
pub struct AsyncMessageSystem {
    message_id_counter: Arc<RwLock<u64>>,
    handlers: Arc<RwLock<HashMap<String, Box<dyn MessageHandler>>>>,
    message_queue: mpsc::UnboundedSender<Message>,
    broadcast_tx: broadcast::Sender<Message>,
    statistics: Arc<RwLock<MessageStatistics>>,
}

/// 消息统计
#[derive(Debug, Default)]
pub struct MessageStatistics {
    pub total_messages: u64,
    pub processed_messages: u64,
    pub failed_messages: u64,
    pub messages_by_type: HashMap<String, u64>,
    pub messages_by_priority: HashMap<MessagePriority, u64>,
}

impl AsyncMessageSystem {
    /// 创建新的消息系统
    pub fn new() -> Self {
        let (message_tx, message_rx) = mpsc::unbounded_channel();
        let (broadcast_tx, _) = broadcast::channel(1000);
        
        let system = Self {
            message_id_counter: Arc::new(RwLock::new(0)),
            handlers: Arc::new(RwLock::new(HashMap::new())),
            message_queue: message_tx,
            broadcast_tx: broadcast_tx.clone(),
            statistics: Arc::new(RwLock::new(MessageStatistics::default())),
        };
        
        // 启动消息处理循环
        let system_clone = system.clone();
        tokio::spawn(async move {
            system_clone.message_processing_loop(message_rx).await;
        });
        
        system
    }
    
    /// 注册消息处理器
    pub async fn register_handler(&self, handler: Box<dyn MessageHandler>) -> Result<()> {
        let name = handler.get_handler_name().to_string();
        let mut handlers = self.handlers.write().await;
        handlers.insert(name.clone(), handler);
        println!("✅ 注册消息处理器: {}", name);
        Ok(())
    }
    
    /// 发送消息
    pub async fn send_message(&self, sender: String, recipient: String, message_type: MessageType, priority: MessagePriority) -> Result<u64> {
        let mut counter = self.message_id_counter.write().await;
        *counter += 1;
        let message_id = *counter;
        
        let message = Message {
            id: message_id,
            sender,
            recipient,
            message_type,
            timestamp: chrono::Utc::now(),
            priority,
        };
        
        // 发送到消息队列
        self.message_queue.send(message.clone())?;
        
        // 广播消息
        let _ = self.broadcast_tx.send(message);
        
        // 更新统计
        {
            let mut stats = self.statistics.write().await;
            stats.total_messages += 1;
        }
        
        Ok(message_id)
    }
    
    /// 订阅消息广播
    pub fn subscribe(&self) -> broadcast::Receiver<Message> {
        self.broadcast_tx.subscribe()
    }
    
    /// 获取消息统计
    pub async fn get_statistics(&self) -> MessageStatistics {
        self.statistics.read().await.clone()
    }
    
    /// 消息处理循环
    async fn message_processing_loop(&self, mut message_rx: mpsc::UnboundedReceiver<Message>) {
        println!("🔄 消息处理循环启动");
        
        while let Some(message) = message_rx.recv().await {
            self.process_message(message).await;
        }
    }
    
    /// 处理单个消息
    async fn process_message(&self, message: Message) {
        let message_type_name = match &message.message_type {
            MessageType::Text(_) => "Text",
            MessageType::Image(_) => "Image",
            MessageType::File(_, _) => "File",
            MessageType::Command(_) => "Command",
            MessageType::Notification(_) => "Notification",
        };
        
        println!("📨 处理消息 ID: {}, 类型: {}, 优先级: {:?}", 
                message.id, message_type_name, message.priority);
        
        // 更新统计
        {
            let mut stats = self.statistics.write().await;
            stats.messages_by_type.entry(message_type_name.to_string())
                .and_modify(|count| *count += 1)
                .or_insert(1);
            stats.messages_by_priority.entry(message.priority)
                .and_modify(|count| *count += 1)
                .or_insert(1);
        }
        
        // 根据消息类型选择合适的处理器
        let handlers = self.handlers.read().await;
        let mut processed = false;
        
        for (_, handler) in handlers.iter() {
            if self.should_handle_message(handler.as_ref(), &message) {
                match handler.handle_message(message.clone()).await {
                    Ok(_) => {
                        processed = true;
                        println!("✅ 消息处理成功");
                        break;
                    }
                    Err(e) => {
                        eprintln!("❌ 消息处理失败: {}", e);
                    }
                }
            }
        }
        
        // 更新处理统计
        {
            let mut stats = self.statistics.write().await;
            if processed {
                stats.processed_messages += 1;
            } else {
                stats.failed_messages += 1;
                println!("⚠️ 没有找到合适的处理器");
            }
        }
    }
    
    /// 判断处理器是否应该处理该消息
    fn should_handle_message(&self, handler: &dyn MessageHandler, message: &Message) -> bool {
        match &message.message_type {
            MessageType::Text(_) => handler.get_handler_name().contains("Text"),
            MessageType::Image(_) => handler.get_handler_name().contains("Image"),
            MessageType::Command(_) => handler.get_handler_name().contains("Command"),
            _ => false,
        }
    }
}

impl Clone for AsyncMessageSystem {
    fn clone(&self) -> Self {
        Self {
            message_id_counter: Arc::clone(&self.message_id_counter),
            handlers: Arc::clone(&self.handlers),
            message_queue: self.message_queue.clone(),
            broadcast_tx: self.broadcast_tx.clone(),
            statistics: Arc::clone(&self.statistics),
        }
    }
}

impl Clone for MessageStatistics {
    fn clone(&self) -> Self {
        Self {
            total_messages: self.total_messages,
            processed_messages: self.processed_messages,
            failed_messages: self.failed_messages,
            messages_by_type: self.messages_by_type.clone(),
            messages_by_priority: self.messages_by_priority.clone(),
        }
    }
}

/// 消息订阅者
pub struct MessageSubscriber {
    name: String,
    receiver: broadcast::Receiver<Message>,
}

impl MessageSubscriber {
    pub fn new(name: &str, system: &AsyncMessageSystem) -> Self {
        Self {
            name: name.to_string(),
            receiver: system.subscribe(),
        }
    }
    
    /// 开始监听消息
    pub async fn start_listening(&mut self) -> Result<()> {
        println!("👂 [{}] 开始监听消息", self.name);
        
        while let Ok(message) = self.receiver.recv().await {
            println!("📬 [{}] 收到消息: ID={}, 发送者={}, 接收者={}", 
                    self.name, message.id, message.sender, message.recipient);
            
            // 模拟消息处理
            sleep(Duration::from_millis(5)).await;
        }
        
        Ok(())
    }
}

/// 消息生产者
pub struct MessageProducer {
    name: String,
    system: AsyncMessageSystem,
}

impl MessageProducer {
    pub fn new(name: &str, system: AsyncMessageSystem) -> Self {
        Self {
            name: name.to_string(),
            system,
        }
    }
    
    /// 发送文本消息
    pub async fn send_text(&self, recipient: &str, content: &str, priority: MessagePriority) -> Result<u64> {
        self.system.send_message(
            self.name.clone(),
            recipient.to_string(),
            MessageType::Text(content.to_string()),
            priority
        ).await
    }
    
    /// 发送图片消息
    pub async fn send_image(&self, recipient: &str, image_data: Vec<u8>, priority: MessagePriority) -> Result<u64> {
        self.system.send_message(
            self.name.clone(),
            recipient.to_string(),
            MessageType::Image(image_data),
            priority
        ).await
    }
    
    /// 发送命令消息
    pub async fn send_command(&self, recipient: &str, command: &str, priority: MessagePriority) -> Result<u64> {
        self.system.send_message(
            self.name.clone(),
            recipient.to_string(),
            MessageType::Command(command.to_string()),
            priority
        ).await
    }
    
    /// 批量发送消息
    pub async fn send_batch_messages(&self, messages: Vec<(String, MessageType, MessagePriority)>) -> Result<Vec<u64>> {
        let mut message_ids = Vec::new();
        
        for (recipient, message_type, priority) in messages {
            let message_id = self.system.send_message(
                self.name.clone(),
                recipient,
                message_type,
                priority
            ).await?;
            message_ids.push(message_id);
        }
        
        Ok(message_ids)
    }
}

/// 主函数
#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 启动异步消息传递示例");
    
    // 创建消息系统
    let message_system = AsyncMessageSystem::new();
    
    // 注册消息处理器
    let text_handler = Box::new(TextMessageHandler::new("TextHandler"));
    let image_handler = Box::new(ImageMessageHandler::new("ImageHandler"));
    let command_handler = Box::new(CommandMessageHandler::new("CommandHandler"));
    
    message_system.register_handler(text_handler).await?;
    message_system.register_handler(image_handler).await?;
    message_system.register_handler(command_handler).await?;
    
    // 创建消息订阅者
    let mut subscriber1 = MessageSubscriber::new("Subscriber1", &message_system);
    let mut subscriber2 = MessageSubscriber::new("Subscriber2", &message_system);
    
    // 启动订阅者
    let subscriber1_task = tokio::spawn(async move {
        subscriber1.start_listening().await
    });
    
    let subscriber2_task = tokio::spawn(async move {
        subscriber2.start_listening().await
    });
    
    // 创建消息生产者
    let producer1 = MessageProducer::new("Producer1", message_system.clone());
    let producer2 = MessageProducer::new("Producer2", message_system.clone());
    
    // 发送各种类型的消息
    println!("\n📤 发送消息示例:");
    
    // 发送文本消息
    let text_msg_id = producer1.send_text("User1", "Hello, World!", MessagePriority::Normal).await?;
    println!("📝 发送文本消息，ID: {}", text_msg_id);
    
    // 发送图片消息
    let image_data = vec![0u8; 1024]; // 模拟图片数据
    let image_msg_id = producer1.send_image("User2", image_data, MessagePriority::High).await?;
    println!("🖼️ 发送图片消息，ID: {}", image_msg_id);
    
    // 发送命令消息
    let cmd_msg_id = producer2.send_command("User3", "restart_service", MessagePriority::Critical).await?;
    println!("⚡ 发送命令消息，ID: {}", cmd_msg_id);
    
    // 批量发送消息
    let batch_messages = vec![
        ("User1".to_string(), MessageType::Text("批量消息1".to_string()), MessagePriority::Normal),
        ("User2".to_string(), MessageType::Text("批量消息2".to_string()), MessagePriority::High),
        ("User3".to_string(), MessageType::Notification("系统通知".to_string()), MessagePriority::Low),
    ];
    
    let batch_ids = producer1.send_batch_messages(batch_messages).await?;
    println!("📦 批量发送消息，IDs: {:?}", batch_ids);
    
    // 等待消息处理
    sleep(Duration::from_secs(2)).await;
    
    // 获取统计信息
    let stats = message_system.get_statistics().await;
    println!("\n📊 消息统计:");
    println!("  总消息数: {}", stats.total_messages);
    println!("  已处理: {}", stats.processed_messages);
    println!("  失败: {}", stats.failed_messages);
    println!("  按类型统计: {:?}", stats.messages_by_type);
    println!("  按优先级统计: {:?}", stats.messages_by_priority);
    
    // 停止订阅者
    subscriber1_task.abort();
    subscriber2_task.abort();
    
    println!("\n✅ 异步消息传递示例完成!");
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_message_system() {
        let system = AsyncMessageSystem::new();
        
        // 注册处理器
        let handler = Box::new(TextMessageHandler::new("TestHandler"));
        system.register_handler(handler).await.unwrap();
        
        // 发送消息
        let message_id = system.send_message(
            "sender".to_string(),
            "recipient".to_string(),
            MessageType::Text("test message".to_string()),
            MessagePriority::Normal
        ).await.unwrap();
        
        assert!(message_id > 0);
        
        // 等待消息处理
        sleep(Duration::from_millis(100)).await;
        
        let stats = system.get_statistics().await;
        assert!(stats.total_messages > 0);
    }
    
    #[tokio::test]
    async fn test_message_producer() {
        let system = AsyncMessageSystem::new();
        let producer = MessageProducer::new("TestProducer", system);
        
        let message_id = producer.send_text("recipient", "test", MessagePriority::Normal).await.unwrap();
        assert!(message_id > 0);
    }
    
    #[tokio::test]
    async fn test_message_handlers() {
        let text_handler = TextMessageHandler::new("TestTextHandler");
        let image_handler = ImageMessageHandler::new("TestImageHandler");
        let command_handler = CommandMessageHandler::new("TestCommandHandler");
        
        let message = Message {
            id: 1,
            sender: "test".to_string(),
            recipient: "test".to_string(),
            message_type: MessageType::Text("test".to_string()),
            timestamp: chrono::Utc::now(),
            priority: MessagePriority::Normal,
        };
        
        assert!(text_handler.handle_message(message.clone()).await.is_ok());
        assert!(image_handler.handle_message(message.clone()).await.is_ok());
        assert!(command_handler.handle_message(message).await.is_ok());
    }
}
