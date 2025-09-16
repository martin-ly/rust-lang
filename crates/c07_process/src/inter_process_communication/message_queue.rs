use crate::error::{IpcError, IpcResult};
use crate::inter_process_communication::IpcChannel;
use crate::types::{IpcConfig, Message};
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};

/// 消息队列实现（简化版本）
pub struct MessageQueue {
    name: String,
    capacity: usize,
    queue: Arc<Mutex<VecDeque<Vec<u8>>>>,
    is_closed: Arc<Mutex<bool>>,
}

#[allow(dead_code)]
impl MessageQueue {
    /// 创建新的消息队列
    pub fn new(name: &str, capacity: usize, _config: IpcConfig) -> IpcResult<Self> {
        Ok(Self {
            name: name.to_string(),
            capacity,
            queue: Arc::new(Mutex::new(VecDeque::new())),
            is_closed: Arc::new(Mutex::new(false)),
        })
    }

    /// 连接到现有的消息队列
    pub fn connect(name: &str, _config: IpcConfig) -> IpcResult<Self> {
        Ok(Self {
            name: name.to_string(),
            capacity: 1000, // 默认容量
            queue: Arc::new(Mutex::new(VecDeque::new())),
            is_closed: Arc::new(Mutex::new(false)),
        })
    }
}

impl IpcChannel for MessageQueue {
    fn send_message(&self, msg: &Message<Vec<u8>>) -> IpcResult<()> {
        let data =
            serde_json::to_vec(&msg).map_err(|e| IpcError::SerializationError(e.to_string()))?;

        let mut queue = self.queue.lock().unwrap();
        if queue.len() >= self.capacity {
            return Err(IpcError::SendFailed("Queue is full".to_string()));
        }
        queue.push_back(data);

        Ok(())
    }

    fn receive_message(&self) -> IpcResult<Message<Vec<u8>>> {
        let mut queue = self.queue.lock().unwrap();

        if let Some(data) = queue.pop_front() {
            let msg: Message<Vec<u8>> = serde_json::from_slice(&data)
                .map_err(|e| IpcError::DeserializationError(e.to_string()))?;
            Ok(msg)
        } else {
            Err(IpcError::ReceiveFailed("Queue is empty".to_string()))
        }
    }

    fn is_closed(&self) -> bool {
        *self.is_closed.lock().unwrap()
    }

    fn close(&mut self) -> IpcResult<()> {
        let mut closed = self.is_closed.lock().unwrap();
        *closed = true;

        // 清理队列
        let mut queue = self.queue.lock().unwrap();
        queue.clear();

        Ok(())
    }

    fn name(&self) -> &str {
        &self.name
    }
}
