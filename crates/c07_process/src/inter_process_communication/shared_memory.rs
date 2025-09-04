use crate::inter_process_communication::{IpcChannel, IpcResult, Message};
use std::sync::{Arc, Mutex};
use std::collections::HashMap;
use std::sync::atomic::AtomicBool;

/// 共享内存区域实现（简化版本）
pub struct SharedMemoryRegion {
    name: String,
    is_closed: Arc<AtomicBool>,
    data: Arc<Mutex<HashMap<String, Vec<u8>>>>,
}

impl SharedMemoryRegion {
    /// 创建新的共享内存区域
    pub fn new(name: &str, _size: usize, _config: crate::types::IpcConfig) -> IpcResult<Self> {
        Ok(Self {
            name: name.to_string(),
            is_closed: Arc::new(AtomicBool::new(false)),
            data: Arc::new(Mutex::new(HashMap::new())),
        })
    }

    /// 连接到现有的共享内存区域
    pub fn connect(name: &str, _config: crate::types::IpcConfig) -> IpcResult<Self> {
        Ok(Self {
            name: name.to_string(),
            is_closed: Arc::new(AtomicBool::new(false)),
            data: Arc::new(Mutex::new(HashMap::new())),
        })
    }
}

impl IpcChannel for SharedMemoryRegion {
    fn send_message(&self, msg: &Message<Vec<u8>>) -> IpcResult<()> {
        if self.is_closed() {
            return Err(crate::error::IpcError::ConnectionFailed("Channel is closed".to_string()));
        }

        let key = format!("msg_{}", msg.id);
        let mut data = self.data.lock().unwrap();
        data.insert(key, msg.data.clone());
        Ok(())
    }

    fn receive_message(&self) -> IpcResult<Message<Vec<u8>>> {
        if self.is_closed() {
            return Err(crate::error::IpcError::ConnectionFailed("Channel is closed".to_string()));
        }

        let data = self.data.lock().unwrap();
        if let Some((key, value)) = data.iter().next() {
            let msg = Message::new(
                key.parse().unwrap_or(0),
                "shared_memory",
                value.clone(),
                0,
            );
            Ok(msg)
        } else {
            Err(crate::error::IpcError::ConnectionFailed("No data available".to_string()))
        }
    }

    fn name(&self) -> &str {
        &self.name
    }

    fn is_closed(&self) -> bool {
        self.is_closed.load(std::sync::atomic::Ordering::Relaxed)
    }

    fn close(&mut self) -> IpcResult<()> {
        self.is_closed.store(true, std::sync::atomic::Ordering::Relaxed);
        Ok(())
    }
}
