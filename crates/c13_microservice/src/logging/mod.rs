//! 日志模块
//! 
//! 提供统一的日志记录功能

use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};
use tracing::{info, warn, error, debug};

/// 日志级别
#[derive(Debug, Clone, PartialEq)]
pub enum LogLevel {
    Debug,
    Info,
    Warn,
    Error,
}

impl ToString for LogLevel {
    fn to_string(&self) -> String {
        match self {
            LogLevel::Debug => "DEBUG".to_string(),
            LogLevel::Info => "INFO".to_string(),
            LogLevel::Warn => "WARN".to_string(),
            LogLevel::Error => "ERROR".to_string(),
        }
    }
}

/// 日志条目
#[derive(Debug, Clone)]
pub struct LogEntry {
    pub timestamp: u64,
    pub level: LogLevel,
    pub message: String,
    pub fields: HashMap<String, String>,
}

/// 日志记录器
pub struct Logger {
    service_name: String,
    service_version: String,
}

impl Logger {
    pub fn new(service_name: String, service_version: String) -> Self {
        Self {
            service_name,
            service_version,
        }
    }
    
    pub fn log(&self, level: LogLevel, message: &str, fields: Option<HashMap<String, String>>) {
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_secs();
        
        let mut log_fields = HashMap::new();
        log_fields.insert("service.name".to_string(), self.service_name.clone());
        log_fields.insert("service.version".to_string(), self.service_version.clone());
        
        if let Some(fields) = fields {
            log_fields.extend(fields);
        }
        
        let entry = LogEntry {
            timestamp,
            level: level.clone(),
            message: message.to_string(),
            fields: log_fields,
        };
        
        match level {
            LogLevel::Debug => debug!("{:?}", entry),
            LogLevel::Info => info!("{:?}", entry),
            LogLevel::Warn => warn!("{:?}", entry),
            LogLevel::Error => error!("{:?}", entry),
        }
    }
    
    pub fn debug(&self, message: &str, fields: Option<HashMap<String, String>>) {
        self.log(LogLevel::Debug, message, fields);
    }
    
    pub fn info(&self, message: &str, fields: Option<HashMap<String, String>>) {
        self.log(LogLevel::Info, message, fields);
    }
    
    pub fn warn(&self, message: &str, fields: Option<HashMap<String, String>>) {
        self.log(LogLevel::Warn, message, fields);
    }
    
    pub fn error(&self, message: &str, fields: Option<HashMap<String, String>>) {
        self.log(LogLevel::Error, message, fields);
    }
}

/// 初始化日志系统
pub fn init_logging() -> Result<(), Box<dyn std::error::Error>> {
    info!("日志系统初始化完成");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_logger() {
        let logger = Logger::new("test_service".to_string(), "1.0.0".to_string());
        
        let mut fields = HashMap::new();
        fields.insert("user_id".to_string(), "123".to_string());
        
        logger.info("测试消息", Some(fields));
        logger.error("错误消息", None);
    }
}
