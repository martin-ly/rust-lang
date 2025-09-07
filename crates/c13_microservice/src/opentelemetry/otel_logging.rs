//! 结构化日志模块

use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH, Duration};
use std::sync::{Arc, Mutex, RwLock};
use std::fs::OpenOptions;
use std::io::Write;
use std::thread;
use std::sync::mpsc;
use tracing::{debug, info, warn, error};
use serde::{Serialize, Deserialize};
use anyhow::Result;

/// 异步日志写入器
#[derive(Debug)]
pub struct AsyncLogWriter {
    sender: mpsc::Sender<LogEntry>,
    worker_handle: Option<thread::JoinHandle<()>>,
}

impl AsyncLogWriter {
    pub fn new(slog_logger: Arc<SlogLogger>) -> Self {
        let (sender, receiver) = mpsc::channel();
        let slog_logger_clone = slog_logger.clone();
        
        let worker_handle = thread::spawn(move || {
            while let Ok(entry) = receiver.recv() {
                if let Err(e) = slog_logger_clone.write_log(entry) {
                    eprintln!("Failed to write log asynchronously: {}", e);
                }
            }
        });
        
        Self {
            sender,
            worker_handle: Some(worker_handle),
        }
    }
    
    pub fn send_log(&self, entry: LogEntry) -> Result<()> {
        self.sender.send(entry)
            .map_err(|e| anyhow::anyhow!("Failed to send log entry: {}", e))?;
        Ok(())
    }
    
    pub fn shutdown(mut self) -> Result<()> {
        drop(self.sender);
        if let Some(handle) = self.worker_handle.take() {
            handle.join().map_err(|_| anyhow::anyhow!("Failed to join log worker thread"))?;
        }
        Ok(())
    }
}

/// 日志级别过滤器
#[derive(Debug, Clone)]
pub struct LogLevelFilter {
    min_level: LogLevel,
    enabled_levels: Vec<LogLevel>,
}

impl LogLevelFilter {
    pub fn new(min_level: LogLevel) -> Self {
        let all_levels = vec![
            LogLevel::Debug,
            LogLevel::Info,
            LogLevel::Warn,
            LogLevel::Error,
        ];
        
        let min_level_index = all_levels.iter().position(|l| std::mem::discriminant(l) == std::mem::discriminant(&min_level)).unwrap_or(0);
        let enabled_levels = all_levels.into_iter().skip(min_level_index).collect();
        
        Self {
            min_level,
            enabled_levels,
        }
    }
    
    pub fn is_enabled(&self, level: &LogLevel) -> bool {
        self.enabled_levels.contains(level)
    }
    
    pub fn set_min_level(&mut self, level: LogLevel) {
        self.min_level = level.clone();
        let all_levels = vec![
            LogLevel::Debug,
            LogLevel::Info,
            LogLevel::Warn,
            LogLevel::Error,
        ];
        
        let min_level_index = all_levels.iter().position(|l| std::mem::discriminant(l) == std::mem::discriminant(&level)).unwrap_or(0);
        self.enabled_levels = all_levels.into_iter().skip(min_level_index).collect();
    }
}

/// 日志记录器（增强版本）
#[derive(Debug)]
pub struct StructuredLogger {
    service_name: String,
    service_version: String,
    default_fields: HashMap<String, String>,
    slog_logger: Option<Arc<SlogLogger>>,
    async_writer: Option<AsyncLogWriter>,
    level_filter: LogLevelFilter,
    log_buffer: Arc<RwLock<Vec<LogEntry>>>,
    buffer_size: usize,
    flush_interval: Duration,
}

impl StructuredLogger {
    pub fn new(service_name: String, service_version: String) -> Self {
        let mut default_fields = HashMap::new();
        default_fields.insert("service.name".to_string(), service_name.clone());
        default_fields.insert("service.version".to_string(), service_version.clone());
        
        Self {
            service_name,
            service_version,
            default_fields,
            slog_logger: None,
            async_writer: None,
            level_filter: LogLevelFilter::new(LogLevel::Info),
            log_buffer: Arc::new(RwLock::new(Vec::new())),
            buffer_size: 1000,
            flush_interval: Duration::from_secs(5),
        }
    }
    
    /// 设置SlogLogger
    pub fn set_slog_logger(&mut self, slog_logger: Arc<SlogLogger>) {
        self.slog_logger = Some(slog_logger.clone());
        self.async_writer = Some(AsyncLogWriter::new(slog_logger));
    }
    
    /// 设置日志级别过滤器
    pub fn set_level_filter(&mut self, min_level: LogLevel) {
        self.level_filter.set_min_level(min_level);
    }
    
    /// 设置缓冲区大小
    pub fn set_buffer_size(&mut self, size: usize) {
        self.buffer_size = size;
    }
    
    /// 设置刷新间隔
    pub fn set_flush_interval(&mut self, interval: Duration) {
        self.flush_interval = interval;
    }
    
    /// 验证日志字段
    fn validate_fields(&self, fields: &HashMap<String, String>) -> Result<()> {
        for (key, value) in fields {
            if key.is_empty() {
                return Err(anyhow::anyhow!("Log field key cannot be empty"));
            }
            if key.len() > 100 {
                return Err(anyhow::anyhow!("Log field key too long: {}", key));
            }
            if value.len() > 1000 {
                return Err(anyhow::anyhow!("Log field value too long for key: {}", key));
            }
        }
        Ok(())
    }
    
    /// 刷新日志缓冲区
    pub fn flush_buffer(&self) -> Result<()> {
        if let Ok(mut buffer) = self.log_buffer.write() {
            for entry in buffer.drain(..) {
                if let Some(async_writer) = &self.async_writer {
                    async_writer.send_log(entry)?;
                } else if let Some(slog_logger) = &self.slog_logger {
                    if let Err(e) = slog_logger.write_log(entry) {
                        eprintln!("Failed to write log: {:?}", e);
                    }
                }
            }
        }
        Ok(())
    }
    
    /// 获取缓冲区中的日志数量
    pub fn get_buffer_size(&self) -> usize {
        if let Ok(buffer) = self.log_buffer.read() {
            buffer.len()
        } else {
            0
        }
    }
    
    /// 获取最近的日志条目
    pub fn get_recent_logs(&self, count: usize) -> Vec<LogEntry> {
        if let Ok(buffer) = self.log_buffer.read() {
            buffer.iter().rev().take(count).cloned().collect()
        } else {
            Vec::new()
        }
    }
    
    pub fn log(&self, level: LogLevel, message: &str, fields: Option<HashMap<String, String>>) {
        // 检查日志级别是否启用
        if !self.level_filter.is_enabled(&level) {
            return;
        }
        
        let mut log_fields = self.default_fields.clone();
        if let Some(fields) = fields {
            // 验证字段
            if let Err(e) = self.validate_fields(&fields) {
                eprintln!("Invalid log fields: {}", e);
                return;
            }
            log_fields.extend(fields);
        }
        
        let timestamp = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_millis();
        
        let log_entry = LogEntry {
            timestamp: timestamp.to_string(),
            level: level.to_string(),
            message: message.to_string(),
            service_name: self.service_name.clone(),
            service_version: self.service_version.clone(),
            thread_id: Some(format!("{:?}", std::thread::current().id())),
            fields: log_fields,
        };
        
        // 添加到缓冲区
        if let Ok(mut buffer) = self.log_buffer.write() {
            buffer.push(log_entry.clone());
            
            // 如果缓冲区满了，刷新
            if buffer.len() >= self.buffer_size {
                drop(buffer); // 释放锁
                if let Err(e) = self.flush_buffer() {
                    eprintln!("Failed to flush log buffer: {}", e);
                }
            }
        }
        
        // 使用异步写入器或直接写入
        if let Some(async_writer) = &self.async_writer {
            if let Err(e) = async_writer.send_log(log_entry.clone()) {
                eprintln!("Failed to send log to async writer: {}", e);
            }
        } else if let Some(slog_logger) = &self.slog_logger {
            if let Err(e) = slog_logger.write_log(log_entry.clone()) {
                eprintln!("Failed to write log: {}", e);
            }
        }
        
        // 同时使用tracing进行日志记录
        match level {
            LogLevel::Debug => debug!("{:?}", log_entry),
            LogLevel::Info => info!("{:?}", log_entry),
            LogLevel::Warn => warn!("{:?}", log_entry),
            LogLevel::Error => error!("{:?}", log_entry),
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
    
    /// 记录HTTP请求日志
    pub fn log_http_request(&self, method: &str, path: &str, status_code: u16, duration_ms: u64) {
        let mut fields = HashMap::new();
        fields.insert("http.method".to_string(), method.to_string());
        fields.insert("http.path".to_string(), path.to_string());
        fields.insert("http.status_code".to_string(), status_code.to_string());
        fields.insert("http.duration_ms".to_string(), duration_ms.to_string());
        
        let level = if status_code >= 400 {
            LogLevel::Warn
        } else {
            LogLevel::Info
        };
        
        self.log(level, &format!("HTTP {} {} - {}", method, path, status_code), Some(fields));
    }
    
    /// 记录数据库查询日志
    pub fn log_database_query(&self, query: &str, duration_ms: u64, rows_affected: Option<u64>) {
        let mut fields = HashMap::new();
        fields.insert("db.query".to_string(), query.to_string());
        fields.insert("db.duration_ms".to_string(), duration_ms.to_string());
        if let Some(rows) = rows_affected {
            fields.insert("db.rows_affected".to_string(), rows.to_string());
        }
        
        self.info("Database query executed", Some(fields));
    }
    
    /// 记录错误日志
    pub fn log_error(&self, error: &str, context: Option<HashMap<String, String>>) {
        let mut fields = HashMap::new();
        fields.insert("error.message".to_string(), error.to_string());
        if let Some(context) = context {
            fields.extend(context);
        }
        
        self.error("An error occurred", Some(fields));
    }
    
    /// 记录性能指标日志
    pub fn log_performance(&self, operation: &str, duration_ms: u64, additional_fields: Option<HashMap<String, String>>) {
        let mut fields = HashMap::new();
        fields.insert("operation".to_string(), operation.to_string());
        fields.insert("duration_ms".to_string(), duration_ms.to_string());
        if let Some(additional) = additional_fields {
            fields.extend(additional);
        }
        
        let level = if duration_ms > 1000 {
            LogLevel::Warn
        } else {
            LogLevel::Info
        };
        
        self.log(level, &format!("Performance: {} took {}ms", operation, duration_ms), Some(fields));
    }
}

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

/// 日志配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogConfig {
    pub level: String,
    pub format: String,
    pub output: String,
    pub file_path: Option<String>,
    pub max_file_size: Option<u64>,
    pub max_files: Option<u32>,
    pub enable_console: bool,
    pub enable_file: bool,
    pub include_timestamp: bool,
    pub include_thread_id: bool,
}

impl Default for LogConfig {
    fn default() -> Self {
        Self {
            level: "info".to_string(),
            format: "json".to_string(),
            output: "stdout".to_string(),
            file_path: Some("logs/app.log".to_string()),
            max_file_size: Some(10 * 1024 * 1024), // 10MB
            max_files: Some(5),
            enable_console: true,
            enable_file: false,
            include_timestamp: true,
            include_thread_id: false,
        }
    }
}

/// 日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry {
    pub timestamp: String,
    pub level: String,
    pub message: String,
    pub service_name: String,
    pub service_version: String,
    pub thread_id: Option<String>,
    pub fields: HashMap<String, String>,
}

/// Slog日志器（增强版本）
#[derive(Debug)]
pub struct SlogLogger {
    config: LogConfig,
    file_writer: Option<Arc<Mutex<std::fs::File>>>,
}

impl SlogLogger {
    pub fn new(config: LogConfig) -> Self {
        Self { 
            config,
            file_writer: None,
        }
    }
    
    pub fn init(&mut self) -> Result<(), Box<dyn std::error::Error>> {
        info!("Initializing Slog logger with config: {:?}", self.config);
        
        // 如果启用文件输出，创建文件写入器
        if self.config.enable_file {
            if let Some(file_path) = &self.config.file_path {
                // 确保日志目录存在
                if let Some(parent) = std::path::Path::new(file_path).parent() {
                    std::fs::create_dir_all(parent)?;
                }
                
                let file = OpenOptions::new()
                    .create(true)
                    .append(true)
                    .open(file_path)?;
                
                self.file_writer = Some(Arc::new(Mutex::new(file)));
                info!("File logging enabled: {}", file_path);
            }
        }
        
        Ok(())
    }
    
    /// 写入日志条目
    pub fn write_log(&self, entry: LogEntry) -> Result<(), Box<dyn std::error::Error>> {
        let formatted_log = self.format_log_entry(&entry)?;
        
        // 控制台输出
        if self.config.enable_console {
            match entry.level.as_str() {
                "DEBUG" => debug!("{}", formatted_log),
                "INFO" => info!("{}", formatted_log),
                "WARN" => warn!("{}", formatted_log),
                "ERROR" => error!("{}", formatted_log),
                _ => info!("{}", formatted_log),
            }
        }
        
        // 文件输出
        if self.config.enable_file {
            if let Some(writer) = &self.file_writer {
                let mut file = writer.lock().unwrap();
                writeln!(file, "{}", formatted_log)?;
                file.flush()?;
            }
        }
        
        Ok(())
    }
    
    /// 格式化日志条目
    fn format_log_entry(&self, entry: &LogEntry) -> Result<String, Box<dyn std::error::Error>> {
        match self.config.format.as_str() {
            "json" => {
                Ok(serde_json::to_string(entry)?)
            },
            "text" => {
                let mut formatted = String::new();
                
                if self.config.include_timestamp {
                    formatted.push_str(&format!("[{}] ", entry.timestamp));
                }
                
                formatted.push_str(&format!("{} ", entry.level));
                formatted.push_str(&format!("{}:{} ", entry.service_name, entry.service_version));
                
                if let Some(thread_id) = &entry.thread_id {
                    formatted.push_str(&format!("[{}] ", thread_id));
                }
                
                formatted.push_str(&entry.message);
                
                if !entry.fields.is_empty() {
                    formatted.push_str(" | ");
                    for (key, value) in &entry.fields {
                        formatted.push_str(&format!("{}={} ", key, value));
                    }
                }
                
                Ok(formatted)
            },
            _ => Ok(serde_json::to_string(entry)?),
        }
    }
    
    /// 检查是否需要日志轮转
    pub fn check_rotation(&self) -> Result<(), Box<dyn std::error::Error>> {
        if let Some(file_path) = &self.config.file_path {
            if let Ok(metadata) = std::fs::metadata(file_path) {
                if let Some(max_size) = self.config.max_file_size {
                    if metadata.len() > max_size {
                        self.rotate_log_file(file_path)?;
                    }
                }
            }
        }
        Ok(())
    }
    
    /// 执行日志轮转
    fn rotate_log_file(&self, file_path: &str) -> Result<(), Box<dyn std::error::Error>> {
        let max_files = self.config.max_files.unwrap_or(5);
        
        // 删除最旧的文件
        for i in (1..max_files).rev() {
            let old_file = format!("{}.{}", file_path, i);
            let new_file = format!("{}.{}", file_path, i + 1);
            
            if std::path::Path::new(&old_file).exists() {
                if i == max_files - 1 {
                    std::fs::remove_file(&old_file)?;
                } else {
                    std::fs::rename(&old_file, &new_file)?;
                }
            }
        }
        
        // 重命名当前文件
        if std::path::Path::new(file_path).exists() {
            std::fs::rename(file_path, &format!("{}.1", file_path))?;
        }
        
        info!("Log file rotated: {}", file_path);
        Ok(())
    }
}

/// 日志聚合器
#[allow(dead_code)]
#[derive(Debug)]
pub struct LogAggregator {
    logs: Arc<RwLock<Vec<LogEntry>>>,
    max_logs: usize,
    
    aggregation_window: Duration,
}

impl LogAggregator {
    pub fn new(max_logs: usize, aggregation_window: Duration) -> Self {
        Self {
            logs: Arc::new(RwLock::new(Vec::new())),
            max_logs,
            aggregation_window,
        }
    }
    
    pub fn add_log(&self, entry: LogEntry) {
        if let Ok(mut logs) = self.logs.write() {
            logs.push(entry);
            
            // 保持最大日志数量
            if logs.len() > self.max_logs {
                let excess = logs.len() - self.max_logs;
                logs.drain(0..excess);
            }
        }
    }
    
    pub fn get_logs_by_level(&self, level: &str) -> Vec<LogEntry> {
        if let Ok(logs) = self.logs.read() {
            logs.iter()
                .filter(|log| log.level == level)
                .cloned()
                .collect()
        } else {
            Vec::new()
        }
    }
    
    pub fn get_logs_by_time_range(&self, start_time: u64, end_time: u64) -> Vec<LogEntry> {
        if let Ok(logs) = self.logs.read() {
            logs.iter()
                .filter(|log| {
                    if let Ok(timestamp) = log.timestamp.parse::<u64>() {
                        timestamp >= start_time && timestamp <= end_time
                    } else {
                        false
                    }
                })
                .cloned()
                .collect()
        } else {
            Vec::new()
        }
    }
    
    pub fn get_error_logs(&self) -> Vec<LogEntry> {
        self.get_logs_by_level("ERROR")
    }
    
    pub fn get_warning_logs(&self) -> Vec<LogEntry> {
        self.get_logs_by_level("WARN")
    }
    
    pub fn get_log_statistics(&self) -> LogStatistics {
        if let Ok(logs) = self.logs.read() {
            let mut stats = LogStatistics::default();
            
            for log in logs.iter() {
                match log.level.as_str() {
                    "DEBUG" => stats.debug_count += 1,
                    "INFO" => stats.info_count += 1,
                    "WARN" => stats.warn_count += 1,
                    "ERROR" => stats.error_count += 1,
                    _ => {}
                }
            }
            
            stats.total_count = logs.len();
            stats
        } else {
            LogStatistics::default()
        }
    }
    
    pub fn clear_old_logs(&self, cutoff_time: u64) -> usize {
        if let Ok(mut logs) = self.logs.write() {
            let initial_count = logs.len();
            logs.retain(|log| {
                if let Ok(timestamp) = log.timestamp.parse::<u64>() {
                    timestamp >= cutoff_time
                } else {
                    true
                }
            });
            initial_count - logs.len()
        } else {
            0
        }
    }
}

/// 日志统计信息
#[derive(Debug, Default, Clone, Serialize, Deserialize)]
pub struct LogStatistics {
    pub total_count: usize,
    pub debug_count: usize,
    pub info_count: usize,
    pub warn_count: usize,
    pub error_count: usize,
}

impl LogStatistics {
    pub fn error_rate(&self) -> f64 {
        if self.total_count == 0 {
            0.0
        } else {
            self.error_count as f64 / self.total_count as f64
        }
    }
    
    pub fn warning_rate(&self) -> f64 {
        if self.total_count == 0 {
            0.0
        } else {
            self.warn_count as f64 / self.total_count as f64
        }
    }
}

/// 初始化日志系统
pub fn init_logging(config: LogConfig) -> Result<(), Box<dyn std::error::Error>> {
    info!("Initializing logging system with level: {}, format: {}, output: {}", 
          config.level, config.format, config.output);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_structured_logger() {
        let logger = StructuredLogger::new("test_service".to_string(), "1.0.0".to_string());
        
        let mut fields = HashMap::new();
        fields.insert("user_id".to_string(), "123".to_string());
        
        // 这些调用不会panic，只是记录日志
        logger.info("Test message", Some(fields));
        logger.error("Error message", None);
    }
    
    #[test]
    fn test_http_request_logging() {
        let logger = StructuredLogger::new("test_service".to_string(), "1.0.0".to_string());
        
        logger.log_http_request("GET", "/api/users", 200, 150);
        logger.log_http_request("POST", "/api/users", 400, 50);
    }
    
    #[test]
    fn test_database_query_logging() {
        let logger = StructuredLogger::new("test_service".to_string(), "1.0.0".to_string());
        
        logger.log_database_query("SELECT * FROM users", 25, Some(10));
        logger.log_database_query("INSERT INTO users", 15, Some(1));
    }
    
    #[test]
    fn test_error_logging() {
        let logger = StructuredLogger::new("test_service".to_string(), "1.0.0".to_string());
        
        let mut context = HashMap::new();
        context.insert("user_id".to_string(), "123".to_string());
        context.insert("operation".to_string(), "create_user".to_string());
        
        logger.log_error("Database connection failed", Some(context));
    }
    
    #[test]
    fn test_performance_logging() {
        let logger = StructuredLogger::new("test_service".to_string(), "1.0.0".to_string());
        
        let mut fields = HashMap::new();
        fields.insert("cache_hit".to_string(), "true".to_string());
        
        logger.log_performance("user_lookup", 50, Some(fields));
        logger.log_performance("heavy_computation", 1500, None);
    }
    
    #[test]
    fn test_log_config() {
        let config = LogConfig::default();
        assert_eq!(config.level, "info");
        assert_eq!(config.format, "json");
        assert_eq!(config.output, "stdout");
    }
    
    #[test]
    fn test_slog_logger() {
        let config = LogConfig::default();
        let mut logger = SlogLogger::new(config);
        assert!(logger.init().is_ok());
    }
}
