use crate::error::{IpcError, IpcResult};
use crate::types::{IpcConfig, Message};
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// 重新设计IpcChannel trait，使其与dyn兼容
pub trait IpcChannel: Send + Sync {
    /// 发送消息
    fn send_message(&self, msg: &Message<Vec<u8>>) -> IpcResult<()>;

    /// 接收消息
    fn receive_message(&self) -> IpcResult<Message<Vec<u8>>>;

    /// 获取通道名称
    fn name(&self) -> &str;

    /// 检查通道是否已关闭
    fn is_closed(&self) -> bool;

    /// 关闭通道
    fn close(&mut self) -> IpcResult<()>;
}

/// 通道统计信息
#[derive(Debug, Clone)]
pub struct ChannelStats {
    pub messages_sent: u64,
    pub messages_received: u64,
    pub bytes_sent: u64,
    pub bytes_received: u64,
    pub created_at: std::time::SystemTime,
    pub last_activity: std::time::SystemTime,
}

impl Default for ChannelStats {
    fn default() -> Self {
        Self {
            messages_sent: 0,
            messages_received: 0,
            bytes_sent: 0,
            bytes_received: 0,
            created_at: std::time::SystemTime::now(),
            last_activity: std::time::SystemTime::now(),
        }
    }
}

/// IPC管理器
pub struct IpcManager {
    channels: Arc<Mutex<HashMap<String, Box<dyn IpcChannel>>>>,
    config: IpcConfig,
    stats: Arc<Mutex<ChannelStats>>,
}

impl IpcManager {
    pub fn new(config: IpcConfig) -> Self {
        Self {
            channels: Arc::new(Mutex::new(HashMap::new())),
            config,
            stats: Arc::new(Mutex::new(ChannelStats::default())),
        }
    }

    /// 创建命名管道
    pub fn create_named_pipe(&mut self, name: &str) -> IpcResult<()> {
        let pipe = crate::pipe::NamedPipe::new(name, self.config.clone())?;
        let mut channels = self.channels.lock().unwrap();
        channels.insert(name.to_string(), Box::new(pipe));
        Ok(())
    }

    /// 创建Unix域套接字
    pub fn create_unix_socket(&mut self, name: &str) -> IpcResult<()> {
        let socket = socket::UnixSocket::new(name, self.config.clone())?;
        let mut channels = self.channels.lock().unwrap();
        channels.insert(name.to_string(), Box::new(socket));
        Ok(())
    }

    /// 创建TCP套接字
    pub fn create_tcp_socket(&mut self, name: &str, port: u16) -> IpcResult<()> {
        let socket = socket::TcpSocket::new(name, port, self.config.clone())?;
        let mut channels = self.channels.lock().unwrap();
        channels.insert(name.to_string(), Box::new(socket));
        Ok(())
    }

    /// 创建共享内存区域
    pub fn create_shared_memory(&mut self, name: &str, size: usize) -> IpcResult<()> {
        let shm = shared_memory::SharedMemoryRegion::new(name, size, self.config.clone())?;
        let mut channels = self.channels.lock().unwrap();
        channels.insert(name.to_string(), Box::new(shm));
        Ok(())
    }

    /// 创建消息队列
    pub fn create_message_queue(&mut self, name: &str, capacity: usize) -> IpcResult<()> {
        let queue = message_queue::MessageQueue::new(name, capacity, self.config.clone())?;
        let mut channels = self.channels.lock().unwrap();
        channels.insert(name.to_string(), Box::new(queue));
        Ok(())
    }

    /// 创建文件系统通道
    pub fn create_file_system_channel(&mut self, name: &str) -> IpcResult<()> {
        let fs = channel::FileSystemChannel::new(name, self.config.clone())?;
        let mut channels = self.channels.lock().unwrap();
        channels.insert(name.to_string(), Box::new(fs));
        Ok(())
    }

    /// 删除通道
    pub fn remove_channel(&mut self, name: &str) -> IpcResult<()> {
        let mut channels = self.channels.lock().unwrap();
        if let Some(mut channel) = channels.remove(name) {
            channel.close()?;
        }
        Ok(())
    }

    /// 清理所有通道
    pub fn cleanup(&mut self) -> IpcResult<()> {
        let mut channels = self.channels.lock().unwrap();
        for (_, mut channel) in channels.drain() {
            channel.close()?;
        }
        Ok(())
    }

    /// 获取通道列表
    pub fn list_channels(&self) -> Vec<String> {
        let channels = self.channels.lock().unwrap();
        channels.keys().cloned().collect()
    }

    /// 获取通道统计信息
    pub fn get_channel_stats(&self, name: &str) -> Option<ChannelStats> {
        let channels = self.channels.lock().unwrap();
        if channels.contains_key(name) {
            Some(ChannelStats::default())
        } else {
            None
        }
    }

    /// 发送消息到指定通道
    pub fn send_message(&self, channel_name: &str, msg: &Message<Vec<u8>>) -> IpcResult<()> {
        let channels = self.channels.lock().unwrap();
        if let Some(channel) = channels.get(channel_name) {
            channel.send_message(msg)?;
            // 更新统计信息
            if let Ok(mut stats) = self.stats.lock() {
                stats.messages_sent += 1;
                stats.bytes_sent += msg.data.len() as u64;
                stats.last_activity = std::time::SystemTime::now();
            }
            Ok(())
        } else {
            Err(IpcError::ChannelNotFound(channel_name.to_string()))
        }
    }

    /// 从指定通道接收消息
    pub fn receive_message(&self, channel_name: &str) -> IpcResult<Message<Vec<u8>>> {
        let channels = self.channels.lock().unwrap();
        if let Some(channel) = channels.get(channel_name) {
            let msg = channel.receive_message()?;
            // 更新统计信息
            if let Ok(mut stats) = self.stats.lock() {
                stats.messages_received += 1;
                stats.bytes_received += msg.data.len() as u64;
                stats.last_activity = std::time::SystemTime::now();
            }
            Ok(msg)
        } else {
            Err(IpcError::ChannelNotFound(channel_name.to_string()))
        }
    }

    /// 获取总体统计信息
    pub fn get_stats(&self) -> ChannelStats {
        self.stats.lock().unwrap().clone()
    }
}

/// 异步IPC管理器
pub struct AsyncIpcManager {
    manager: IpcManager,
}

impl AsyncIpcManager {
    pub fn new(config: IpcConfig) -> Self {
        Self {
            manager: IpcManager::new(config),
        }
    }

    /// 异步发送消息（简化版本，不使用tokio）
    pub fn send_message(&self, channel_name: &str, msg: &Message<Vec<u8>>) -> IpcResult<()> {
        self.manager.send_message(channel_name, msg)
    }

    /// 异步接收消息（简化版本，不使用tokio）
    pub fn receive_message(&self, channel_name: &str) -> IpcResult<Message<Vec<u8>>> {
        self.manager.receive_message(channel_name)
    }
}

/// IPC连接器
pub struct IpcConnector {
    config: IpcConfig,
}

impl IpcConnector {
    pub fn new(config: IpcConfig) -> Self {
        Self { config }
    }

    /// 连接到命名管道
    pub fn connect_to_pipe(&self, name: &str) -> IpcResult<Box<dyn IpcChannel>> {
        let pipe = crate::pipe::NamedPipe::connect(name, self.config.clone())?;
        Ok(Box::new(pipe))
    }

    /// 连接到Unix域套接字
    pub fn connect_to_unix_socket(&self, name: &str) -> IpcResult<Box<dyn IpcChannel>> {
        let socket = socket::UnixSocket::connect(name, self.config.clone())?;
        Ok(Box::new(socket))
    }

    /// 连接到TCP套接字
    pub fn connect_to_tcp_socket(&self, name: &str, port: u16) -> IpcResult<Box<dyn IpcChannel>> {
        let socket = socket::TcpSocket::connect(name, port, self.config.clone())?;
        Ok(Box::new(socket))
    }

    /// 连接到共享内存区域
    pub fn connect_to_shared_memory(&self, name: &str) -> IpcResult<Box<dyn IpcChannel>> {
        let shm = shared_memory::SharedMemoryRegion::connect(name, self.config.clone())?;
        Ok(Box::new(shm))
    }

    /// 连接到消息队列
    pub fn connect_to_message_queue(&self, name: &str) -> IpcResult<Box<dyn IpcChannel>> {
        let queue = message_queue::MessageQueue::connect(name, self.config.clone())?;
        Ok(Box::new(queue))
    }

    /// 连接到文件系统通道
    pub fn connect_to_file_system_channel(&self, name: &str) -> IpcResult<Box<dyn IpcChannel>> {
        let fs = channel::FileSystemChannel::connect(name, self.config.clone())?;
        Ok(Box::new(fs))
    }
}

// 子模块声明
pub mod channel;
pub mod message_queue;
pub mod pipe;
pub mod shared_memory;
pub mod socket;

// 增强的IPC功能
#[cfg(feature = "async")]
pub mod enhanced;
