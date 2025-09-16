use crate::error::{IpcError, IpcResult};
use crate::inter_process_communication::IpcChannel;
use crate::types::{IpcConfig, Message};
use std::fs::OpenOptions;
use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::sync::{Arc, Mutex};

/// 文件系统通道实现
#[allow(dead_code)]
pub struct FileSystemChannel {
    name: String,
    config: IpcConfig,
    is_closed: Arc<Mutex<bool>>,
}

impl FileSystemChannel {
    /// 创建新的文件系统通道
    pub fn new(name: &str, config: IpcConfig) -> IpcResult<Self> {
        let file_path = format!("{}.fs", name);

        // 创建通道文件
        let _file = OpenOptions::new()
            .create(true)
            .write(true)
            .open(&file_path)
            .map_err(|e| IpcError::ConnectionFailed(e.to_string()))?;

        Ok(Self {
            name: name.to_string(),
            config,
            is_closed: Arc::new(Mutex::new(false)),
        })
    }

    /// 连接到现有的文件系统通道
    pub fn connect(name: &str, config: IpcConfig) -> IpcResult<Self> {
        let file_path = format!("{}.fs", name);

        // 检查通道文件是否存在
        if !Path::new(&file_path).exists() {
            return Err(IpcError::ConnectionFailed(format!(
                "Channel '{}' not found",
                name
            )));
        }

        Ok(Self {
            name: name.to_string(),
            config,
            is_closed: Arc::new(Mutex::new(false)),
        })
    }
}

impl IpcChannel for FileSystemChannel {
    fn send_message(&self, msg: &Message<Vec<u8>>) -> IpcResult<()> {
        let file_path = format!("{}.fs", self.name);

        // 序列化消息
        let json =
            serde_json::to_string(&msg).map_err(|e| IpcError::SerializationError(e.to_string()))?;

        // 写入通道文件
        let mut file = OpenOptions::new()
            .write(true)
            .append(true)
            .open(&file_path)
            .map_err(|e| IpcError::SendFailed(e.to_string()))?;

        writeln!(file, "{}", json).map_err(|e| IpcError::SendFailed(e.to_string()))?;

        Ok(())
    }

    fn receive_message(&self) -> IpcResult<Message<Vec<u8>>> {
        let file_path = format!("{}.fs", self.name);

        // 读取通道文件
        let file = OpenOptions::new()
            .read(true)
            .open(&file_path)
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
        let msg: Message<Vec<u8>> = serde_json::from_str(&last_line)
            .map_err(|e| IpcError::DeserializationError(e.to_string()))?;

        Ok(msg)
    }

    fn is_closed(&self) -> bool {
        *self.is_closed.lock().unwrap()
    }

    fn close(&mut self) -> IpcResult<()> {
        let mut closed = self.is_closed.lock().unwrap();
        *closed = true;

        // 删除通道文件
        let file_path = format!("{}.fs", self.name);
        if Path::new(&file_path).exists() {
            std::fs::remove_file(&file_path)
                .map_err(|e| IpcError::ConnectionFailed(e.to_string()))?;
        }

        Ok(())
    }

    fn name(&self) -> &str {
        &self.name
    }
}
