use crate::types::{IpcConfig, IpcProtocol, Message};
use crate::error::{IpcResult, IpcError};
use crate::inter_process_communication::IpcChannel;
use serde::{Serialize, Deserialize};
use std::fs::OpenOptions;
use std::io::{Write, BufReader, BufRead};
use std::path::Path;
use std::sync::{Arc, Mutex};

/// 命名管道实现
#[allow(dead_code)]
pub struct NamedPipe {
    name: String,
    config: IpcConfig,
    is_closed: Arc<Mutex<bool>>,
}

impl NamedPipe {
    /// 创建新的命名管道
    pub fn new(name: &str, config: IpcConfig) -> IpcResult<Self> {
        // 在Windows上，我们使用文件作为简单的IPC机制
        let pipe_path = format!("{}.pipe", name);
        
        // 创建管道文件
        let _file = OpenOptions::new()
            .create(true)
            .write(true)
            .open(&pipe_path)
            .map_err(|e| IpcError::ConnectionFailed(e.to_string()))?;
        
        Ok(Self {
            name: name.to_string(),
            config,
            is_closed: Arc::new(Mutex::new(false)),
        })
    }
    
    /// 连接到现有的命名管道
    pub fn connect(name: &str, config: IpcConfig) -> IpcResult<Self> {
        let pipe_path = format!("{}.pipe", name);
        
        // 检查管道文件是否存在
        if !Path::new(&pipe_path).exists() {
            return Err(IpcError::ConnectionFailed(format!("Pipe '{}' not found", name)));
        }
        
        Ok(Self {
            name: name.to_string(),
            config,
            is_closed: Arc::new(Mutex::new(false)),
        })
    }
    
    /// 发送消息
    pub fn send<T: Serialize + Send>(&self, msg: Message<T>) -> IpcResult<()> {
        let pipe_path = format!("{}.pipe", self.name);
        
        // 序列化消息
        let json = serde_json::to_string(&msg)
            .map_err(|e| IpcError::SerializationError(e.to_string()))?;
        
        // 写入管道文件
        let mut file = OpenOptions::new()
            .write(true)
            .append(true)
            .open(&pipe_path)
            .map_err(|e| IpcError::SendFailed(e.to_string()))?;
        
        writeln!(file, "{}", json)
            .map_err(|e| IpcError::SendFailed(e.to_string()))?;
        
        Ok(())
    }
    
    /// 接收消息
    pub fn receive<T: for<'de> Deserialize<'de> + Send>(&self) -> IpcResult<Message<T>> {
        let pipe_path = format!("{}.pipe", self.name);
        
        // 读取管道文件
        let file = OpenOptions::new()
            .read(true)
            .open(&pipe_path)
            .map_err(|e| IpcError::ReceiveFailed(e.to_string()))?;
        
        let reader = BufReader::new(file);
        let mut lines = reader.lines();
        
        // 读取最后一行（最新的消息）
        let mut last_line = String::new();
        while let Some(Ok(line)) = lines.next() {
            last_line = line;
        }
        
        if last_line.is_empty() {
            return Err(IpcError::ReceiveFailed("No message available".to_string()));
        }
        
        // 反序列化消息
        let msg: Message<T> = serde_json::from_str(&last_line)
            .map_err(|e| IpcError::DeserializationError(e.to_string()))?;
        
        Ok(msg)
    }
    
    /// 检查管道是否关闭
    pub fn is_closed(&self) -> bool {
        *self.is_closed.lock().unwrap()
    }
    
    /// 关闭管道
    pub fn close(&mut self) -> IpcResult<()> {
        let mut closed = self.is_closed.lock().unwrap();
        *closed = true;
        
        // 删除管道文件
        let pipe_path = format!("{}.pipe", self.name);
        if Path::new(&pipe_path).exists() {
            std::fs::remove_file(&pipe_path)
                .map_err(|e| IpcError::ConnectionFailed(e.to_string()))?;
        }
        
        Ok(())
    }
    
    /// 获取管道名称
    pub fn name(&self) -> &str {
        &self.name
    }
    
    /// 获取协议类型
    pub fn protocol(&self) -> IpcProtocol {
        IpcProtocol::Pipe
    }
}

impl IpcChannel for NamedPipe {
    fn send_message(&self, msg: &Message<Vec<u8>>) -> IpcResult<()> {
        // 将Vec<u8>转换为Message<Vec<u8>>的克隆
        let msg_clone = Message {
            id: msg.id,
            message_type: msg.message_type.clone(),
            data: msg.data.clone(),
            timestamp: msg.timestamp,
            source_pid: msg.source_pid,
            target_pid: msg.target_pid,
            priority: msg.priority,
        };
        self.send(msg_clone)
    }
    
    fn receive_message(&self) -> IpcResult<Message<Vec<u8>>> {
        self.receive()
    }
    
    fn name(&self) -> &str {
        self.name()
    }
    
    fn is_closed(&self) -> bool {
        self.is_closed()
    }
    
    fn close(&mut self) -> IpcResult<()> {
        self.close()
    }
}
