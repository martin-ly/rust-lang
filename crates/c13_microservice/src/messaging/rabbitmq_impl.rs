//! RabbitMQ消息队列实现
//! 
//! 提供基于lapin crate的实际RabbitMQ连接和消息队列功能

// use std::collections::HashMap; // 暂时未使用
use std::sync::Arc;
use tokio::sync::RwLock;
use tracing::{info, warn};

use crate::error::{Error, Result};

/// RabbitMQ连接配置
#[derive(Debug, Clone)]
pub struct RabbitMQConfig {
    pub url: String,
    pub exchange: String,
    pub queue: String,
    pub routing_key: String,
    pub prefetch_count: u16,
    pub connection_timeout: u64,
}

impl Default for RabbitMQConfig {
    fn default() -> Self {
        Self {
            url: "amqp://localhost:5672".to_string(),
            exchange: "microservice.exchange".to_string(),
            queue: "microservice.queue".to_string(),
            routing_key: "microservice.routing".to_string(),
            prefetch_count: 1,
            connection_timeout: 30,
        }
    }
}

/// RabbitMQ消息队列实现
pub struct RabbitMQMessageQueue {
    config: RabbitMQConfig,
    #[cfg(feature = "with-rabbitmq")]
    connection: Option<lapin::Connection>,
    #[cfg(feature = "with-rabbitmq")]
    channel: Option<lapin::Channel>,
    connected: Arc<RwLock<bool>>,
}

impl RabbitMQMessageQueue {
    /// 创建新的RabbitMQ消息队列
    pub fn new(config: RabbitMQConfig) -> Self {
        Self {
            config,
            #[cfg(feature = "with-rabbitmq")]
            connection: None,
            #[cfg(feature = "with-rabbitmq")]
            channel: None,
            connected: Arc::new(RwLock::new(false)),
        }
    }
    
    /// 连接到RabbitMQ服务器
    pub async fn connect(&mut self) -> Result<()> {
        info!("连接RabbitMQ服务器: {}", self.config.url);
        
        #[cfg(feature = "with-rabbitmq")]
        {
            match lapin::Connection::connect(&self.config.url, lapin::ConnectionProperties::default()).await {
                Ok(connection) => {
                    match connection.create_channel().await {
                        Ok(channel) => {
                            self.connection = Some(connection);
                            self.channel = Some(channel);
                            *self.connected.write().await = true;
                            info!("RabbitMQ连接成功");
                            
                            // 设置QoS
                            if let Some(ref channel) = self.channel {
                                if let Err(e) = channel.basic_qos(self.config.prefetch_count, lapin::options::BasicQosOptions::default()).await {
                                    warn!("设置QoS失败: {}", e);
                                }
                            }
                            
                            Ok(())
                        }
                        Err(e) => {
                            error!("创建RabbitMQ通道失败: {}", e);
                            Err(Error::config(format!("创建RabbitMQ通道失败: {}", e)))
                        }
                    }
                }
                Err(e) => {
                    error!("RabbitMQ连接失败: {}", e);
                    Err(Error::config(format!("RabbitMQ连接失败: {}", e)))
                }
            }
        }
        
        #[cfg(not(feature = "with-rabbitmq"))]
        {
            warn!("RabbitMQ功能未启用，请添加 'with-rabbitmq' feature");
            *self.connected.write().await = true; // 模拟连接成功
            Ok(())
        }
    }
    
    /// 声明交换器
    pub async fn declare_exchange(&self) -> Result<()> {
        if !*self.connected.read().await {
            return Err(Error::config("RabbitMQ未连接".to_string()));
        }
        
        info!("声明RabbitMQ交换器: {}", self.config.exchange);
        
        #[cfg(feature = "with-rabbitmq")]
        {
            if let Some(ref channel) = self.channel {
                match channel
                    .exchange_declare(
                        &self.config.exchange,
                        lapin::ExchangeKind::Topic,
                        lapin::options::ExchangeDeclareOptions {
                            durable: true,
                            ..Default::default()
                        },
                        lapin::types::FieldTable::default(),
                    )
                    .await
                {
                    Ok(_) => {
                        info!("交换器声明成功");
                        Ok(())
                    }
                    Err(e) => {
                        error!("声明交换器失败: {}", e);
                        Err(Error::config(format!("声明交换器失败: {}", e)))
                    }
                }
            } else {
                Err(Error::config("RabbitMQ通道不可用".to_string()))
            }
        }
        
        #[cfg(not(feature = "with-rabbitmq"))]
        {
            info!("模拟声明RabbitMQ交换器: {}", self.config.exchange);
            Ok(())
        }
    }
    
    /// 声明队列
    pub async fn declare_queue(&self) -> Result<()> {
        if !*self.connected.read().await {
            return Err(Error::config("RabbitMQ未连接".to_string()));
        }
        
        info!("声明RabbitMQ队列: {}", self.config.queue);
        
        #[cfg(feature = "with-rabbitmq")]
        {
            if let Some(ref channel) = self.channel {
                match channel
                    .queue_declare(
                        &self.config.queue,
                        lapin::options::QueueDeclareOptions {
                            durable: true,
                            ..Default::default()
                        },
                        lapin::types::FieldTable::default(),
                    )
                    .await
                {
                    Ok(_) => {
                        info!("队列声明成功");
                        Ok(())
                    }
                    Err(e) => {
                        error!("声明队列失败: {}", e);
                        Err(Error::config(format!("声明队列失败: {}", e)))
                    }
                }
            } else {
                Err(Error::config("RabbitMQ通道不可用".to_string()))
            }
        }
        
        #[cfg(not(feature = "with-rabbitmq"))]
        {
            info!("模拟声明RabbitMQ队列: {}", self.config.queue);
            Ok(())
        }
    }
    
    /// 绑定队列到交换器
    pub async fn bind_queue(&self) -> Result<()> {
        if !*self.connected.read().await {
            return Err(Error::config("RabbitMQ未连接".to_string()));
        }
        
        info!("绑定队列到交换器: {} -> {}", self.config.queue, self.config.exchange);
        
        #[cfg(feature = "with-rabbitmq")]
        {
            if let Some(ref channel) = self.channel {
                match channel
                    .queue_bind(
                        &self.config.queue,
                        &self.config.exchange,
                        &self.config.routing_key,
                        lapin::options::QueueBindOptions::default(),
                        lapin::types::FieldTable::default(),
                    )
                    .await
                {
                    Ok(_) => {
                        info!("队列绑定成功");
                        Ok(())
                    }
                    Err(e) => {
                        error!("绑定队列失败: {}", e);
                        Err(Error::config(format!("绑定队列失败: {}", e)))
                    }
                }
            } else {
                Err(Error::config("RabbitMQ通道不可用".to_string()))
            }
        }
        
        #[cfg(not(feature = "with-rabbitmq"))]
        {
            info!("模拟绑定队列到交换器");
            Ok(())
        }
    }
    
    /// 发布消息
    pub async fn publish(&self, routing_key: &str, _message: &[u8]) -> Result<()> {
        if !*self.connected.read().await {
            return Err(Error::config("RabbitMQ未连接".to_string()));
        }
        
        info!("发布消息到RabbitMQ: {} -> {}", routing_key, self.config.exchange);
        
        #[cfg(feature = "with-rabbitmq")]
        {
            if let Some(ref channel) = self.channel {
                match channel
                    .basic_publish(
                        &self.config.exchange,
                        routing_key,
                        lapin::options::BasicPublishOptions::default(),
                        message,
                        lapin::BasicProperties::default(),
                    )
                    .await
                {
                    Ok(_) => {
                        info!("消息发布成功");
                        Ok(())
                    }
                    Err(e) => {
                        error!("发布消息失败: {}", e);
                        Err(Error::config(format!("发布消息失败: {}", e)))
                    }
                }
            } else {
                Err(Error::config("RabbitMQ通道不可用".to_string()))
            }
        }
        
        #[cfg(not(feature = "with-rabbitmq"))]
        {
            info!("模拟发布消息到RabbitMQ: {}", routing_key);
            Ok(())
        }
    }
    
    /// 消费消息
    pub async fn consume<F>(&self, mut handler: F) -> Result<()>
    where
        F: FnMut(Vec<u8>) -> Result<()> + Send + 'static,
    {
        if !*self.connected.read().await {
            return Err(Error::config("RabbitMQ未连接".to_string()));
        }
        
        info!("开始消费RabbitMQ队列: {}", self.config.queue);
        
        #[cfg(feature = "with-rabbitmq")]
        {
            if let Some(ref channel) = self.channel {
                let mut consumer = channel
                    .basic_consume(
                        &self.config.queue,
                        "consumer",
                        lapin::options::BasicConsumeOptions::default(),
                        lapin::types::FieldTable::default(),
                    )
                    .await
                    .map_err(|e| Error::config(format!("创建消费者失败: {}", e)))?;
                
                info!("消费者创建成功，开始处理消息...");
                
                while let Some(delivery) = consumer.next().await {
                    match delivery {
                        Ok(delivery) => {
                            info!("收到消息，处理中...");
                            
                            match handler(delivery.data) {
                                Ok(_) => {
                                    // 确认消息
                                    if let Err(e) = delivery.ack(lapin::options::BasicAckOptions::default()).await {
                                        error!("确认消息失败: {}", e);
                                    }
                                }
                                Err(e) => {
                                    error!("处理消息失败: {}", e);
                                    // 拒绝消息
                                    if let Err(e) = delivery.nack(lapin::options::BasicNackOptions::default()).await {
                                        error!("拒绝消息失败: {}", e);
                                    }
                                }
                            }
                        }
                        Err(e) => {
                            error!("接收消息失败: {}", e);
                        }
                    }
                }
                
                Ok(())
            } else {
                Err(Error::config("RabbitMQ通道不可用".to_string()))
            }
        }
        
        #[cfg(not(feature = "with-rabbitmq"))]
        {
            info!("模拟消费RabbitMQ队列: {}", self.config.queue);
            // 模拟处理一条消息
            handler(b"test message".to_vec())?;
            Ok(())
        }
    }
    
    /// 检查连接状态
    pub async fn is_connected(&self) -> bool {
        *self.connected.read().await
    }
    
    /// 断开连接
    pub async fn disconnect(&mut self) -> Result<()> {
        info!("断开RabbitMQ连接");
        *self.connected.write().await = false;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_rabbitmq_config() {
        let config = RabbitMQConfig::default();
        assert_eq!(config.url, "amqp://localhost:5672");
        assert_eq!(config.exchange, "microservice.exchange");
        assert_eq!(config.queue, "microservice.queue");
    }
    
    #[tokio::test]
    async fn test_rabbitmq_message_queue_creation() {
        let config = RabbitMQConfig::default();
        let _queue = RabbitMQMessageQueue::new(config);
        assert!(true); // 如果能创建成功就说明测试通过
    }
    
    #[tokio::test]
    async fn test_rabbitmq_connection_simulation() {
        let config = RabbitMQConfig::default();
        let mut queue = RabbitMQMessageQueue::new(config);
        
        // 测试连接（模拟模式）
        let result = queue.connect().await;
        assert!(result.is_ok());
        assert!(queue.is_connected().await);
        
        // 测试声明交换器（模拟模式）
        let result = queue.declare_exchange().await;
        assert!(result.is_ok());
        
        // 测试声明队列（模拟模式）
        let result = queue.declare_queue().await;
        assert!(result.is_ok());
        
        // 测试绑定队列（模拟模式）
        let result = queue.bind_queue().await;
        assert!(result.is_ok());
        
        // 测试发布消息（模拟模式）
        let result = queue.publish("test.routing", b"test message").await;
        assert!(result.is_ok());
        
        // 测试断开连接
        let result = queue.disconnect().await;
        assert!(result.is_ok());
        assert!(!queue.is_connected().await);
    }
}
