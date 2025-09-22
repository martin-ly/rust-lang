//! 日志记录模块
//! 
//! 提供统一的日志记录、结构化日志和日志分析功能

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use chrono::{DateTime, Utc};

/// 日志级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum LogLevel {
    Trace = 0,
    Debug = 1,
    Info = 2,
    Warn = 3,
    Error = 4,
    Fatal = 5,
}

impl LogLevel {
    /// 从字符串创建日志级别
    pub fn from_str(level: &str) -> Option<Self> {
        match level.to_lowercase().as_str() {
            "trace" => Some(LogLevel::Trace),
            "debug" => Some(LogLevel::Debug),
            "info" => Some(LogLevel::Info),
            "warn" | "warning" => Some(LogLevel::Warn),
            "error" => Some(LogLevel::Error),
            "fatal" => Some(LogLevel::Fatal),
            _ => None,
        }
    }
    
    /// 转换为字符串
    pub fn as_str(&self) -> &'static str {
        match self {
            LogLevel::Trace => "TRACE",
            LogLevel::Debug => "DEBUG",
            LogLevel::Info => "INFO",
            LogLevel::Warn => "WARN",
            LogLevel::Error => "ERROR",
            LogLevel::Fatal => "FATAL",
        }
    }
}

/// 日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogEntry {
    pub timestamp: DateTime<Utc>,
    pub level: LogLevel,
    pub message: String,
    pub module: String,
    pub target: String,
    pub fields: HashMap<String, serde_json::Value>,
    pub request_id: Option<String>,
    pub user_id: Option<String>,
    pub session_id: Option<String>,
    pub trace_id: Option<String>,
    pub span_id: Option<String>,
}

impl LogEntry {
    /// 创建新的日志条目
    pub fn new(level: LogLevel, message: String, module: String) -> Self {
        Self {
            timestamp: Utc::now(),
            level,
            message,
            module: module.clone(),
            target: module,
            fields: HashMap::new(),
            request_id: None,
            user_id: None,
            session_id: None,
            trace_id: None,
            span_id: None,
        }
    }
    
    /// 添加字段
    pub fn with_field(mut self, key: String, value: serde_json::Value) -> Self {
        self.fields.insert(key, value);
        self
    }
    
    /// 设置请求ID
    pub fn with_request_id(mut self, request_id: String) -> Self {
        self.request_id = Some(request_id);
        self
    }
    
    /// 设置用户ID
    pub fn with_user_id(mut self, user_id: String) -> Self {
        self.user_id = Some(user_id);
        self
    }
    
    /// 设置会话ID
    pub fn with_session_id(mut self, session_id: String) -> Self {
        self.session_id = Some(session_id);
        self
    }
    
    /// 设置追踪ID
    pub fn with_trace_id(mut self, trace_id: String) -> Self {
        self.trace_id = Some(trace_id);
        self
    }
    
    /// 设置跨度ID
    pub fn with_span_id(mut self, span_id: String) -> Self {
        self.span_id = Some(span_id);
        self
    }
}

/// 日志配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogConfig {
    pub level: LogLevel,
    pub format: LogFormat,
    pub output: LogOutput,
    pub max_file_size: u64,
    pub max_files: u32,
    pub buffer_size: usize,
    pub flush_interval: u64,
    pub enable_structured: bool,
    pub enable_colors: bool,
    pub enable_timestamps: bool,
    pub enable_module_path: bool,
    pub enable_line_numbers: bool,
}

/// 日志格式
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogFormat {
    Json,
    Text,
    Compact,
}

/// 日志输出
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogOutput {
    Console,
    File(String),
    Both(String),
    Syslog,
    Journald,
}

impl Default for LogConfig {
    fn default() -> Self {
        Self {
            level: LogLevel::Info,
            format: LogFormat::Json,
            output: LogOutput::Console,
            max_file_size: 100 * 1024 * 1024, // 100MB
            max_files: 10,
            buffer_size: 1000,
            flush_interval: 5, // 5 seconds
            enable_structured: true,
            enable_colors: true,
            enable_timestamps: true,
            enable_module_path: true,
            enable_line_numbers: false,
        }
    }
}

/// 日志统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LogStats {
    pub total_logs: u64,
    pub logs_by_level: HashMap<String, u64>,
    pub logs_by_module: HashMap<String, u64>,
    pub error_rate: f64,
    pub last_log_time: Option<DateTime<Utc>>,
}

/// 日志管理器
pub struct LogManager {
    config: LogConfig,
    stats: Arc<RwLock<LogStats>>,
    buffer: Arc<RwLock<Vec<LogEntry>>>,
}

impl LogManager {
    /// 创建新的日志管理器
    pub fn new(config: LogConfig) -> Self {
        Self {
            config,
            stats: Arc::new(RwLock::new(LogStats {
                total_logs: 0,
                logs_by_level: HashMap::new(),
                logs_by_module: HashMap::new(),
                error_rate: 0.0,
                last_log_time: None,
            })),
            buffer: Arc::new(RwLock::new(Vec::new())),
        }
    }
    
    /// 记录日志
    pub async fn log(&self, entry: LogEntry) {
        // 检查日志级别
        if entry.level < self.config.level {
            return;
        }
        
        // 更新统计信息
        self.update_stats(&entry).await;
        
        // 添加到缓冲区
        {
            let mut buffer = self.buffer.write().await;
            buffer.push(entry.clone());
            
            // 如果缓冲区满了，刷新
            if buffer.len() >= self.config.buffer_size {
                self.flush_buffer().await;
            }
        }
        
        // 输出日志
        self.output_log(&entry).await;
    }
    
    /// 更新统计信息
    async fn update_stats(&self, entry: &LogEntry) {
        let mut stats = self.stats.write().await;
        stats.total_logs += 1;
        
        // 按级别统计
        let level_key = entry.level.as_str().to_string();
        *stats.logs_by_level.entry(level_key).or_insert(0) += 1;
        
        // 按模块统计
        *stats.logs_by_module.entry(entry.module.clone()).or_insert(0) += 1;
        
        // 计算错误率
        let error_count = stats.logs_by_level.get("ERROR").unwrap_or(&0) + 
                         stats.logs_by_level.get("FATAL").unwrap_or(&0);
        stats.error_rate = if stats.total_logs > 0 {
            error_count as f64 / stats.total_logs as f64
        } else {
            0.0
        };
        
        stats.last_log_time = Some(entry.timestamp);
    }
    
    /// 输出日志
    async fn output_log(&self, entry: &LogEntry) {
        match &self.config.output {
            LogOutput::Console => {
                self.output_to_console(entry).await;
            }
            LogOutput::File(path) => {
                self.output_to_file(entry, path).await;
            }
            LogOutput::Both(path) => {
                self.output_to_console(entry).await;
                self.output_to_file(entry, path).await;
            }
            LogOutput::Syslog => {
                self.output_to_syslog(entry).await;
            }
            LogOutput::Journald => {
                self.output_to_journald(entry).await;
            }
        }
    }
    
    /// 输出到控制台
    async fn output_to_console(&self, entry: &LogEntry) {
        let formatted = self.format_log(entry);
        
        match entry.level {
            LogLevel::Trace | LogLevel::Debug => {
                println!("{}", formatted);
            }
            LogLevel::Info => {
                println!("{}", formatted);
            }
            LogLevel::Warn => {
                eprintln!("{}", formatted);
            }
            LogLevel::Error | LogLevel::Fatal => {
                eprintln!("{}", formatted);
            }
        }
    }
    
    /// 输出到文件
    async fn output_to_file(&self, entry: &LogEntry, _path: &str) {
        let formatted = self.format_log(entry);
        // TODO: 实现文件输出
        // 这里应该使用异步文件写入
        println!("[FILE] {}", formatted);
    }
    
    /// 输出到系统日志
    async fn output_to_syslog(&self, entry: &LogEntry) {
        let formatted = self.format_log(entry);
        // TODO: 实现syslog输出
        println!("[SYSLOG] {}", formatted);
    }
    
    /// 输出到journald
    async fn output_to_journald(&self, entry: &LogEntry) {
        let formatted = self.format_log(entry);
        // TODO: 实现journald输出
        println!("[JOURNALD] {}", formatted);
    }
    
    /// 格式化日志
    fn format_log(&self, entry: &LogEntry) -> String {
        match self.config.format {
            LogFormat::Json => {
                serde_json::to_string(entry).unwrap_or_else(|_| "JSON格式化失败".to_string())
            }
            LogFormat::Text => {
                self.format_text(entry)
            }
            LogFormat::Compact => {
                self.format_compact(entry)
            }
        }
    }
    
    /// 格式化文本日志
    fn format_text(&self, entry: &LogEntry) -> String {
        let mut parts = Vec::new();
        
        if self.config.enable_timestamps {
            parts.push(format!("{}", entry.timestamp.format("%Y-%m-%d %H:%M:%S%.3f UTC")));
        }
        
        parts.push(format!("[{}]", entry.level.as_str()));
        
        if self.config.enable_module_path {
            parts.push(format!("[{}]", entry.module));
        }
        
        if let Some(request_id) = &entry.request_id {
            parts.push(format!("[req:{}]", request_id));
        }
        
        if let Some(user_id) = &entry.user_id {
            parts.push(format!("[user:{}]", user_id));
        }
        
        parts.push(entry.message.clone());
        
        if !entry.fields.is_empty() {
            let fields_str = entry.fields.iter()
                .map(|(k, v)| format!("{}={}", k, v))
                .collect::<Vec<_>>()
                .join(" ");
            parts.push(format!("{{{}}}", fields_str));
        }
        
        parts.join(" ")
    }
    
    /// 格式化紧凑日志
    fn format_compact(&self, entry: &LogEntry) -> String {
        let level_char = match entry.level {
            LogLevel::Trace => 'T',
            LogLevel::Debug => 'D',
            LogLevel::Info => 'I',
            LogLevel::Warn => 'W',
            LogLevel::Error => 'E',
            LogLevel::Fatal => 'F',
        };
        
        format!("{} {} {}", 
                entry.timestamp.format("%H:%M:%S%.3f"),
                level_char,
                entry.message)
    }
    
    /// 刷新缓冲区
    pub async fn flush_buffer(&self) {
        let mut buffer = self.buffer.write().await;
        if !buffer.is_empty() {
            // TODO: 批量写入日志
            buffer.clear();
        }
    }
    
    /// 获取日志统计信息
    pub async fn get_stats(&self) -> LogStats {
        self.stats.read().await.clone()
    }
    
    /// 更新配置
    pub fn update_config(&mut self, config: LogConfig) {
        self.config = config;
    }
}

/// 日志宏
#[macro_export]
macro_rules! log_trace {
    ($logger:expr, $msg:expr) => {
        $logger.log(LogEntry::new(LogLevel::Trace, $msg.to_string(), module_path!().to_string())).await;
    };
    ($logger:expr, $msg:expr, $($key:expr => $value:expr),*) => {
        {
            let mut entry = LogEntry::new(LogLevel::Trace, $msg.to_string(), module_path!().to_string());
            $(
                entry = entry.with_field($key.to_string(), serde_json::to_value($value).unwrap_or(serde_json::Value::Null));
            )*
            $logger.log(entry).await;
        }
    };
}

#[macro_export]
macro_rules! log_debug {
    ($logger:expr, $msg:expr) => {
        $logger.log(LogEntry::new(LogLevel::Debug, $msg.to_string(), module_path!().to_string())).await;
    };
    ($logger:expr, $msg:expr, $($key:expr => $value:expr),*) => {
        {
            let mut entry = LogEntry::new(LogLevel::Debug, $msg.to_string(), module_path!().to_string());
            $(
                entry = entry.with_field($key.to_string(), serde_json::to_value($value).unwrap_or(serde_json::Value::Null));
            )*
            $logger.log(entry).await;
        }
    };
}

#[macro_export]
macro_rules! log_info {
    ($logger:expr, $msg:expr) => {
        $logger.log(LogEntry::new(LogLevel::Info, $msg.to_string(), module_path!().to_string())).await;
    };
    ($logger:expr, $msg:expr, $($key:expr => $value:expr),*) => {
        {
            let mut entry = LogEntry::new(LogLevel::Info, $msg.to_string(), module_path!().to_string());
            $(
                entry = entry.with_field($key.to_string(), serde_json::to_value($value).unwrap_or(serde_json::Value::Null));
            )*
            $logger.log(entry).await;
        }
    };
}

#[macro_export]
macro_rules! log_warn {
    ($logger:expr, $msg:expr) => {
        $logger.log(LogEntry::new(LogLevel::Warn, $msg.to_string(), module_path!().to_string())).await;
    };
    ($logger:expr, $msg:expr, $($key:expr => $value:expr),*) => {
        {
            let mut entry = LogEntry::new(LogLevel::Warn, $msg.to_string(), module_path!().to_string());
            $(
                entry = entry.with_field($key.to_string(), serde_json::to_value($value).unwrap_or(serde_json::Value::Null));
            )*
            $logger.log(entry).await;
        }
    };
}

#[macro_export]
macro_rules! log_error {
    ($logger:expr, $msg:expr) => {
        $logger.log(LogEntry::new(LogLevel::Error, $msg.to_string(), module_path!().to_string())).await;
    };
    ($logger:expr, $msg:expr, $($key:expr => $value:expr),*) => {
        {
            let mut entry = LogEntry::new(LogLevel::Error, $msg.to_string(), module_path!().to_string());
            $(
                entry = entry.with_field($key.to_string(), serde_json::to_value($value).unwrap_or(serde_json::Value::Null));
            )*
            $logger.log(entry).await;
        }
    };
}

#[macro_export]
macro_rules! log_fatal {
    ($logger:expr, $msg:expr) => {
        $logger.log(LogEntry::new(LogLevel::Fatal, $msg.to_string(), module_path!().to_string())).await;
    };
    ($logger:expr, $msg:expr, $($key:expr => $value:expr),*) => {
        {
            let mut entry = LogEntry::new(LogLevel::Fatal, $msg.to_string(), module_path!().to_string());
            $(
                entry = entry.with_field($key.to_string(), serde_json::to_value($value).unwrap_or(serde_json::Value::Null));
            )*
            $logger.log(entry).await;
        }
    };
}
