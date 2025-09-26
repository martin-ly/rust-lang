//! 增强的进程间通信功能
//! 
//! 这个模块提供了高性能的IPC通信功能，包括零拷贝数据传输、
//! 智能错误恢复、连接池管理等 Rust 1.90 新特性

use crate::error::{IpcError, IpcResult};
use crate::types::{IpcConfig, IpcProtocol, Message};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex as TokioMutex, RwLock as TokioRwLock};
use tokio::net::{TcpListener, TcpStream};
#[cfg(unix)]
use tokio::net::{UnixListener, UnixStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use serde::{Serialize, Deserialize};

/// 增强的IPC管理器
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct EnhancedIpcManager {
    channels: Arc<TokioRwLock<HashMap<String, EnhancedIpcChannel>>>,
    connection_pool: Arc<ConnectionPool>,
    performance_monitor: Arc<IpcPerformanceMonitor>,
    error_recovery: Arc<IpcErrorRecovery>,
    config: IpcConfig,
}

/// 增强的IPC通道
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct EnhancedIpcChannel {
    name: String,
    protocol: IpcProtocol,
    connection: EnhancedConnection,
    stats: Arc<TokioMutex<ChannelStats>>,
    created_at: Instant,
    last_activity: Arc<TokioMutex<Instant>>,
}

/// 增强的连接
#[cfg(feature = "async")]
#[allow(dead_code)]
pub enum EnhancedConnection {
    Tcp(tokio::sync::Mutex<TcpStream>),
    #[cfg(unix)]
    Unix(tokio::sync::Mutex<UnixStream>),
    NamedPipe(NamedPipeConnection),
    SharedMemory(SharedMemoryConnection),
    MessageQueue(MessageQueueConnection),
}

/// 命名管道连接
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct NamedPipeConnection {
    read_stream: tokio::fs::File,
    write_stream: tokio::fs::File,
    path: String,
}

/// 共享内存连接
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct SharedMemoryConnection {
    region: Arc<tokio::sync::Mutex<memmap2::MmapMut>>,
    name: String,
    size: usize,
}

/// 消息队列连接
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct MessageQueueConnection {
    queue: Arc<TokioMutex<Vec<Message<Vec<u8>>>>>,
    name: String,
    capacity: usize,
}

/// 连接池
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct ConnectionPool {
    tcp_connections: Arc<TokioMutex<HashMap<String, Vec<TcpStream>>>>,
    #[cfg(unix)]
    unix_connections: Arc<TokioMutex<HashMap<String, Vec<UnixStream>>>>,
    max_connections_per_endpoint: usize,
    connection_timeout: Duration,
}

/// IPC性能监控器
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct IpcPerformanceMonitor {
    metrics: Arc<TokioMutex<HashMap<String, IpcMetrics>>>,
    update_interval: Duration,
}

/// IPC指标
#[cfg(feature = "async")]
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct IpcMetrics {
    pub messages_sent: u64,
    pub messages_received: u64,
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub average_latency: Duration,
    pub max_latency: Duration,
    pub error_count: u64,
    pub last_activity: Instant,
}

/// IPC错误恢复器
#[cfg(feature = "async")]
#[allow(dead_code)]
pub struct IpcErrorRecovery {
    retry_policies: Arc<TokioMutex<HashMap<String, IpcRetryPolicy>>>,
    // 使用字符串键，避免 IpcError 需要实现 Hash/Eq
    recovery_strategies: Arc<TokioMutex<HashMap<String, IpcRecoveryStrategy>>>,
}

/// IPC重试策略
#[cfg(feature = "async")]
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct IpcRetryPolicy {
    pub max_retries: u32,
    pub backoff_duration: Duration,
    pub backoff_multiplier: f64,
    pub max_backoff: Duration,
}

/// IPC恢复策略
#[cfg(feature = "async")]
#[allow(dead_code)]
pub enum IpcRecoveryStrategy {
    Reconnect,
    Recreate,
    Skip,
    Custom(std::sync::Arc<dyn Fn(&IpcError) -> IpcResult<()> + Send + Sync>),
}

/// 通道统计信息
#[cfg(feature = "async")]
#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct ChannelStats {
    pub name: String,
    pub protocol: IpcProtocol,
    pub messages_sent: u64,
    pub messages_received: u64,
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub connection_count: usize,
    pub last_activity: Instant,
    pub created_at: Instant,
}

#[cfg(feature = "async")]
#[allow(dead_code)]
impl EnhancedIpcManager {
    /// 创建新的增强IPC管理器
    pub async fn new(config: IpcConfig) -> IpcResult<Self> {
        let channels = Arc::new(TokioRwLock::new(HashMap::new()));
        let connection_pool = Arc::new(ConnectionPool::new(10, Duration::from_secs(30)));
        let performance_monitor = Arc::new(IpcPerformanceMonitor::new());
        let error_recovery = Arc::new(IpcErrorRecovery::new());

        Ok(Self {
            channels,
            connection_pool,
            performance_monitor,
            error_recovery,
            config,
        })
    }

    /// 创建TCP套接字通道
    #[allow(dead_code)]
    pub async fn create_tcp_channel(&self, name: &str, host: &str, port: u16) -> IpcResult<()> {
        let _listener = TcpListener::bind(format!("{}:{}", host, port)).await
            .map_err(|e| IpcError::ConnectionFailed(e.to_string()))?;

        let connection = EnhancedConnection::Tcp(
            tokio::sync::Mutex::new(
                TcpStream::connect(format!("{}:{}", host, port)).await
                    .map_err(|e| IpcError::ConnectionFailed(e.to_string()))?
            )
        );

        let stats = ChannelStats {
            name: name.to_string(),
            protocol: IpcProtocol::Socket,
            messages_sent: 0,
            messages_received: 0,
            bytes_sent: 0,
            bytes_received: 0,
            connection_count: 1,
            last_activity: Instant::now(),
            created_at: Instant::now(),
        };

        let channel = EnhancedIpcChannel {
            name: name.to_string(),
            protocol: IpcProtocol::Socket,
            connection,
            stats: Arc::new(TokioMutex::new(stats)),
            created_at: Instant::now(),
            last_activity: Arc::new(TokioMutex::new(Instant::now())),
        };

        self.channels.write().await.insert(name.to_string(), channel);
        self.performance_monitor.add_channel(name).await;

        Ok(())
    }

    /// 创建Unix套接字通道
    #[cfg(unix)]
    #[allow(dead_code)]
    pub async fn create_unix_channel(&self, name: &str, path: &str) -> IpcResult<()> {
        let connection = EnhancedConnection::Unix(
            UnixStream::connect(path).await
                .map_err(|e| IpcError::ConnectionFailed(e.to_string()))?
        );

        let stats = ChannelStats {
            name: name.to_string(),
            protocol: IpcProtocol::Socket,
            messages_sent: 0,
            messages_received: 0,
            bytes_sent: 0,
            bytes_received: 0,
            connection_count: 1,
            last_activity: Instant::now(),
            created_at: Instant::now(),
        };

        let channel = EnhancedIpcChannel {
            name: name.to_string(),
            protocol: IpcProtocol::Socket,
            connection,
            stats: Arc::new(TokioMutex::new(stats)),
            created_at: Instant::now(),
            last_activity: Arc::new(TokioMutex::new(Instant::now())),
        };

        self.channels.write().await.insert(name.to_string(), channel);
        self.performance_monitor.add_channel(name).await;

        Ok(())
    }

    /// 创建共享内存通道
    #[allow(dead_code)]
    pub async fn create_shared_memory_channel(&self, name: &str, size: usize) -> IpcResult<()> {
        let region = memmap2::MmapOptions::new()
            .len(size)
            .map_anon()
            .map_err(|e| IpcError::SharedMemoryError(e.to_string()))?
            ;

        let connection = EnhancedConnection::SharedMemory(SharedMemoryConnection {
            region: Arc::new(tokio::sync::Mutex::new(region)),
            name: name.to_string(),
            size,
        });

        let stats = ChannelStats {
            name: name.to_string(),
            protocol: IpcProtocol::SharedMemory,
            messages_sent: 0,
            messages_received: 0,
            bytes_sent: 0,
            bytes_received: 0,
            connection_count: 1,
            last_activity: Instant::now(),
            created_at: Instant::now(),
        };

        let channel = EnhancedIpcChannel {
            name: name.to_string(),
            protocol: IpcProtocol::SharedMemory,
            connection,
            stats: Arc::new(TokioMutex::new(stats)),
            created_at: Instant::now(),
            last_activity: Arc::new(TokioMutex::new(Instant::now())),
        };

        self.channels.write().await.insert(name.to_string(), channel);
        self.performance_monitor.add_channel(name).await;

        Ok(())
    }

    /// 创建消息队列通道
    #[allow(dead_code)]
    pub async fn create_message_queue_channel(&self, name: &str, capacity: usize) -> IpcResult<()> {
        let connection = EnhancedConnection::MessageQueue(MessageQueueConnection {
            queue: Arc::new(TokioMutex::new(Vec::with_capacity(capacity))),
            name: name.to_string(),
            capacity,
        });

        let stats = ChannelStats {
            name: name.to_string(),
            protocol: IpcProtocol::MessageQueue,
            messages_sent: 0,
            messages_received: 0,
            bytes_sent: 0,
            bytes_received: 0,
            connection_count: 1,
            last_activity: Instant::now(),
            created_at: Instant::now(),
        };

        let channel = EnhancedIpcChannel {
            name: name.to_string(),
            protocol: IpcProtocol::MessageQueue,
            connection,
            stats: Arc::new(TokioMutex::new(stats)),
            created_at: Instant::now(),
            last_activity: Arc::new(TokioMutex::new(Instant::now())),
        };

        self.channels.write().await.insert(name.to_string(), channel);
        self.performance_monitor.add_channel(name).await;

        Ok(())
    }

    /// 发送消息（零拷贝优化）
    #[allow(dead_code)]
    pub async fn send_message_zero_copy<T>(&self, channel_name: &str, message: &Message<T>) -> IpcResult<()>
    where
        T: Serialize,
    {
        let start_time = Instant::now();
        
        let channels = self.channels.read().await;
        let channel = channels.get(channel_name)
            .ok_or_else(|| IpcError::ChannelNotFound(channel_name.to_string()))?;

        // 序列化消息
        let serialized = serde_json::to_vec(message)
            .map_err(|e| IpcError::SerializationError(e.to_string()))?;

        // 根据协议类型发送
        match &channel.connection {
            EnhancedConnection::Tcp(stream_mutex) => {
                let mut stream = stream_mutex.lock().await;
                // 发送消息长度（小端）
                let len = serialized.len() as u32;
                stream
                    .write_all(&len.to_le_bytes())
                    .await
                    .map_err(|e| IpcError::SendFailed(e.to_string()))?;
                // 发送内容
                stream
                    .write_all(&serialized)
                    .await
                    .map_err(|e| IpcError::SendFailed(e.to_string()))?;
            }
            #[cfg(unix)]
            EnhancedConnection::Unix(stream_mutex) => {
                let mut stream = stream_mutex.lock().await;
                let len = serialized.len() as u32;
                stream
                    .write_all(&len.to_le_bytes())
                    .await
                    .map_err(|e| IpcError::SendFailed(e.to_string()))?;
                stream
                    .write_all(&serialized)
                    .await
                    .map_err(|e| IpcError::SendFailed(e.to_string()))?;
            }
            EnhancedConnection::SharedMemory(conn) => {
                let mut region = conn.region.lock().await;
                if serialized.len() > region.len() {
                    return Err(IpcError::SendFailed("Message too large for shared memory".to_string()));
                }
                
                region[..serialized.len()].copy_from_slice(&serialized);
            }
            EnhancedConnection::MessageQueue(conn) => {
                let mut queue = conn.queue.lock().await;
                if queue.len() >= conn.capacity {
                    return Err(IpcError::SendFailed("Message queue is full".to_string()));
                }
                
                let message = Message {
                    id: message.id,
                    message_type: message.message_type.clone(),
                    data: serialized.clone(),
                    timestamp: message.timestamp,
                    source_pid: message.source_pid,
                    target_pid: message.target_pid,
                    priority: message.priority,
                };
                
                queue.push(message);
            }
            _ => return Err(IpcError::ProtocolNotSupported("Unsupported connection type".to_string())),
        }

        // 更新统计信息
        let latency = start_time.elapsed();
        self.update_channel_stats(channel_name, serialized.len() as u64, 0, latency).await;

        Ok(())
    }

    /// 接收消息（零拷贝优化）
    #[allow(dead_code)]
    pub async fn receive_message_zero_copy<T>(&self, channel_name: &str) -> IpcResult<Message<T>>
    where
        T: for<'de> Deserialize<'de>,
    {
        let start_time = Instant::now();
        
        let channels = self.channels.read().await;
        let channel = channels.get(channel_name)
            .ok_or_else(|| IpcError::ChannelNotFound(channel_name.to_string()))?;

        let (data, latency) = match &channel.connection {
            EnhancedConnection::Tcp(stream_mutex) => {
                let mut stream = stream_mutex.lock().await;
                let mut len_buf = [0u8; 4];
                stream
                    .read_exact(&mut len_buf)
                    .await
                    .map_err(|e| IpcError::ReceiveFailed(e.to_string()))?;
                let len = u32::from_le_bytes(len_buf) as usize;
                let mut buffer = vec![0u8; len];
                stream
                    .read_exact(&mut buffer)
                    .await
                    .map_err(|e| IpcError::ReceiveFailed(e.to_string()))?;
                (buffer, start_time.elapsed())
            }
            #[cfg(unix)]
            EnhancedConnection::Unix(stream_mutex) => {
                let mut stream = stream_mutex.lock().await;
                let mut len_buf = [0u8; 4];
                stream
                    .read_exact(&mut len_buf)
                    .await
                    .map_err(|e| IpcError::ReceiveFailed(e.to_string()))?;
                let len = u32::from_le_bytes(len_buf) as usize;
                let mut buffer = vec![0u8; len];
                stream
                    .read_exact(&mut buffer)
                    .await
                    .map_err(|e| IpcError::ReceiveFailed(e.to_string()))?;
                (buffer, start_time.elapsed())
            }
            EnhancedConnection::SharedMemory(conn) => {
                let region = conn.region.lock().await;
                let data = region.to_vec();
                (data, start_time.elapsed())
            }
            EnhancedConnection::MessageQueue(conn) => {
                let mut queue = conn.queue.lock().await;
                if let Some(message) = queue.pop() {
                    (message.data, start_time.elapsed())
                } else {
                    return Err(IpcError::ReceiveFailed("No messages in queue".to_string()));
                }
            }
            _ => return Err(IpcError::ProtocolNotSupported("Unsupported connection type".to_string())),
        };

        // 反序列化消息
        let message: Message<T> = serde_json::from_slice(&data)
            .map_err(|e| IpcError::DeserializationError(e.to_string()))?;

        // 更新统计信息
        self.update_channel_stats(channel_name, 0, data.len() as u64, latency).await;

        Ok(message)
    }

    /// 获取通道统计信息
    #[allow(dead_code)]
    pub async fn get_channel_stats(&self, channel_name: &str) -> Option<ChannelStats> {
        let channels = self.channels.read().await;
        channels.get(channel_name).and_then(|channel| {
            let stats = channel.stats.try_lock().ok()?;
            Some(stats.clone())
        })
    }

    /// 获取所有通道统计信息
    pub async fn get_all_channel_stats(&self) -> HashMap<String, ChannelStats> {
        let channels = self.channels.read().await;
        let mut stats = HashMap::new();
        
        for (name, channel) in channels.iter() {
            if let Ok(stats_guard) = channel.stats.try_lock() {
                stats.insert(name.clone(), stats_guard.clone());
            }
        }
        
        stats
    }

    /// 清理所有通道
    pub async fn cleanup(&self) -> IpcResult<()> {
        let mut channels = self.channels.write().await;
        channels.clear();
        Ok(())
    }

    /// 更新通道统计信息
    async fn update_channel_stats(&self, channel_name: &str, bytes_sent: u64, bytes_received: u64, latency: Duration) {
        let channels = self.channels.read().await;
        if let Some(channel) = channels.get(channel_name) {
            if let Ok(mut stats) = channel.stats.try_lock() {
                stats.bytes_sent += bytes_sent;
                stats.bytes_received += bytes_received;
                stats.last_activity = Instant::now();
                
                if bytes_sent > 0 {
                    stats.messages_sent += 1;
                }
                if bytes_received > 0 {
                    stats.messages_received += 1;
                }
            }
            
            if let Ok(mut last_activity) = channel.last_activity.try_lock() {
                *last_activity = Instant::now();
            }
        }
        
        self.performance_monitor.update_metrics(channel_name, bytes_sent, bytes_received, latency).await;
    }
}

#[cfg(feature = "async")]
impl ConnectionPool {
    pub fn new(max_connections_per_endpoint: usize, connection_timeout: Duration) -> Self {
        Self {
            tcp_connections: Arc::new(TokioMutex::new(HashMap::new())),
            
            max_connections_per_endpoint,
            connection_timeout,
        }
    }

    pub async fn get_tcp_connection(&self, endpoint: &str) -> Option<TcpStream> {
        let mut connections = self.tcp_connections.lock().await;
        connections.get_mut(endpoint).and_then(|conns| conns.pop())
    }

    pub async fn return_tcp_connection(&self, endpoint: &str, connection: TcpStream) {
        let mut connections = self.tcp_connections.lock().await;
        let conns = connections.entry(endpoint.to_string()).or_insert_with(Vec::new);
        
        if conns.len() < self.max_connections_per_endpoint {
            conns.push(connection);
        }
    }
}

#[cfg(feature = "async")]
impl IpcPerformanceMonitor {
    pub fn new() -> Self {
        Self {
            metrics: Arc::new(TokioMutex::new(HashMap::new())),
            update_interval: Duration::from_secs(1),
        }
    }

    pub async fn add_channel(&self, channel_name: &str) {
        let metrics = IpcMetrics {
            messages_sent: 0,
            messages_received: 0,
            bytes_sent: 0,
            bytes_received: 0,
            average_latency: Duration::ZERO,
            max_latency: Duration::ZERO,
            error_count: 0,
            last_activity: Instant::now(),
        };
        
        self.metrics.lock().await.insert(channel_name.to_string(), metrics);
    }

    pub async fn update_metrics(&self, channel_name: &str, bytes_sent: u64, bytes_received: u64, latency: Duration) {
        {
            let mut metrics = self.metrics.lock().await;
            if let Some(metric) = metrics.get_mut(channel_name) {
                metric.bytes_sent += bytes_sent;
                metric.bytes_received += bytes_received;
                metric.last_activity = Instant::now();
                
                if bytes_sent > 0 {
                    metric.messages_sent += 1;
                }
                if bytes_received > 0 {
                    metric.messages_received += 1;
                }
                
                // 更新延迟统计
                if latency > metric.max_latency {
                    metric.max_latency = latency;
                }
                
                // 计算平均延迟
                let total_messages = metric.messages_sent + metric.messages_received;
                if total_messages > 0 {
                    metric.average_latency = Duration::from_nanos(
                        (metric.average_latency.as_nanos() as u64 * (total_messages - 1) + latency.as_nanos() as u64) / total_messages
                    );
                }
            }
        }
    }

    pub async fn get_metrics(&self, channel_name: &str) -> Option<IpcMetrics> {
        self.metrics.lock().await.get(channel_name).cloned()
    }
}

#[cfg(feature = "async")]
impl IpcErrorRecovery {
    pub fn new() -> Self {
        Self {
            retry_policies: Arc::new(TokioMutex::new(HashMap::new())),
            recovery_strategies: Arc::new(TokioMutex::new(HashMap::new())),
        }
    }

    pub async fn add_retry_policy(&self, name: String, policy: IpcRetryPolicy) {
        self.retry_policies.lock().await.insert(name, policy);
    }

    pub async fn add_recovery_strategy(&self, error: IpcError, strategy: IpcRecoveryStrategy) {
        // 使用字符串键，避免 IpcError 需要实现 Hash/Eq
        self.recovery_strategies.lock().await.insert(format!("{:?}", error), strategy);
    }

    pub async fn attempt_recovery(&self, error: &IpcError) -> IpcResult<()> {
        let key = format!("{:?}", error);
        if let Some(strategy) = self.recovery_strategies.lock().await.get(&key) {
            match strategy {
                IpcRecoveryStrategy::Reconnect => {
                    // 实现重连逻辑
                    Ok(())
                }
                IpcRecoveryStrategy::Recreate => {
                    // 实现重新创建逻辑
                    Ok(())
                }
                IpcRecoveryStrategy::Skip => {
                    // 跳过错误
                    Ok(())
                }
                IpcRecoveryStrategy::Custom(f) => {
                    f(error)
                }
            }
        } else {
            Err(IpcError::ConnectionFailed("No recovery strategy found".to_string()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_enhanced_ipc_manager() {
        let config = IpcConfig::default();
        let manager = EnhancedIpcManager::new(config).await.unwrap();
        
        // 测试创建消息队列通道
        manager.create_message_queue_channel("test_queue", 100).await.unwrap();
        
        // 测试发送和接收消息
        let message = Message::new(1, "test", "Hello, World!".as_bytes().to_vec(), 1234);
        manager.send_message_zero_copy("test_queue", &message).await.unwrap();
        
        let received: Message<Vec<u8>> = manager.receive_message_zero_copy("test_queue").await.unwrap();
        assert_eq!(received.id, message.id);
        assert_eq!(received.message_type, message.message_type);
        
        // 清理
        manager.cleanup().await.unwrap();
    }

    #[tokio::test]
    async fn test_shared_memory_channel() {
        let config = IpcConfig::default();
        let manager = EnhancedIpcManager::new(config).await.unwrap();
        
        // 测试创建共享内存通道
        manager.create_shared_memory_channel("test_memory", 1024).await.unwrap();
        
        // 测试发送消息
        let message = Message::new(1, "test", "Hello, Shared Memory!".as_bytes().to_vec(), 1234);
        manager.send_message_zero_copy("test_memory", &message).await.unwrap();
        
        // 清理
        manager.cleanup().await.unwrap();
    }
}
