use crate::types::{IpcConfig, Message};
use crate::error::{IpcResult, IpcError};
use crate::inter_process_communication::IpcChannel;
use std::sync::{Arc, Mutex};
use std::collections::HashMap;

/// 共享内存区域实现（简化版本）
pub struct SharedMemoryRegion {
    name: String,
    size: usize,
    config: IpcConfig,
    is_closed: Arc<Mutex<bool>>,
    data: Arc<Mutex<HashMap<String, Vec<u8>>>>,
}

impl SharedMemoryRegion {
    /// 创建新的共享内存区域
    pub fn new(name: &str, size: usize, config: IpcConfig) -> IpcResult<Self> {
        Ok(Self {
            name: name.to_string(),
            size,
            config,
            is_closed: Arc::new(Mutex::new(false)),
            data: Arc::new(Mutex::new(HashMap::new())),
        })
    }
    
    /// 连接到现有的共享内存区域
    pub fn connect(name: &str, config: IpcConfig) -> IpcResult<Self> {
        Ok(Self {
            name: name.to_string(),
            size: 0, // 未知大小
            config,
            is_closed: Arc::new(Mutex::new(false)),
            data: Arc::new(Mutex::new(HashMap::new())),
        })
    }
}

impl IpcChannel for SharedMemoryRegion {
    fn send_message(&self, msg: &Message<Vec<u8>>) -> IpcResult<()> {
        let key = format!("msg_{}", msg.id);
        let data = serde_json::to_vec(&msg)
            .map_err(|e| IpcError::SerializationError(e.to_string()))?;
        
        let mut shared_data = self.data.lock().unwrap();
        shared_data.insert(key, data);
        
        Ok(())
    }
    
    fn receive_message(&self) -> IpcResult<Message<Vec<u8>>> {
        let shared_data = self.data.lock().unwrap();
        
        // 查找最新的消息
        let mut latest_key = None;
        let mut latest_id = 0u64;
        
        for key in shared_data.keys() {
            if key.starts_with("msg_") {
                if let Ok(id) = key[4..].parse::<u64>() {
                    if id > latest_id {
                        latest_id = id;
                        latest_key = Some(key.clone());
                    }
                }
            }
        }
        
        if let Some(key) = latest_key {
            if let Some(data) = shared_data.get(&key) {
                let msg: Message<Vec<u8>> = serde_json::from_slice(data)
                    .map_err(|e| IpcError::DeserializationError(e.to_string()))?;
                return Ok(msg);
            }
        }
        
        Err(IpcError::ReceiveFailed("No message available".to_string()))
    }
    
    fn is_closed(&self) -> bool {
        *self.is_closed.lock().unwrap()
    }
    
    fn close(&mut self) -> IpcResult<()> {
        let mut closed = self.is_closed.lock().unwrap();
        *closed = true;
        
        // 清理数据
        let mut shared_data = self.data.lock().unwrap();
        shared_data.clear();
        
        Ok(())
    }
    
    fn name(&self) -> &str {
        &self.name
    }
}
