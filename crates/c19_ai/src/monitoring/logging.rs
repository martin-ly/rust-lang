//! 日志记录
//! 
//! 提供 AI 系统的日志记录功能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// 日志级别
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogLevel {
    Error,
    Warn,
    Info,
    Debug,
    Trace,
}

/// 日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry {
    pub level: LogLevel,
    pub message: String,
    pub timestamp: u64,
    pub fields: HashMap<String, String>,
}

/// 日志记录器
pub struct AILogger {
    entries: Vec<LogEntry>,
}

impl AILogger {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }
    
    pub fn log(&mut self, level: LogLevel, message: String, fields: HashMap<String, String>) {
        let entry = LogEntry {
            level,
            message,
            timestamp: std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_secs(),
            fields,
        };
        self.entries.push(entry);
    }
    
    pub fn get_entries(&self) -> &[LogEntry] {
        &self.entries
    }
}
