//! 本地日志模块
//!
//! 提供完整的本地日志功能，包括：
//! - 日志滚动（按大小和时间）
//! - 日志压缩
//! - 固定缓存大小管理
//! - 按日期文件命名
//! - 异步写入
//! - 性能优化

use anyhow::{Context, Result};
use chrono::{DateTime, Local};
use flate2::Compression;
use flate2::write::GzEncoder;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::fmt;
use std::fs::{File, OpenOptions, create_dir_all, metadata, remove_file, rename};
use std::io::{BufRead, BufReader, BufWriter, Write};
use std::path::{Path, PathBuf};
use std::sync::mpsc::{self, Receiver, Sender};
use std::sync::{Arc, Mutex};
use std::thread::{self, JoinHandle};
use std::time::{Duration, Instant, SystemTime};
use tracing::{debug, error, info, warn};

/// 日志级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum LocalLogLevel {
    Debug = 0,
    Info = 1,
    Warn = 2,
    Error = 3,
}

impl fmt::Display for LocalLogLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LocalLogLevel::Debug => write!(f, "DEBUG"),
            LocalLogLevel::Info => write!(f, "INFO"),
            LocalLogLevel::Warn => write!(f, "WARN"),
            LocalLogLevel::Error => write!(f, "ERROR"),
        }
    }
}

/// 日志滚动策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum RotationStrategy {
    /// 按文件大小滚动
    Size { max_size_bytes: u64 },
    /// 按时间滚动
    Time { interval_hours: u32 },
    /// 按大小和时间滚动
    SizeAndTime {
        max_size_bytes: u64,
        interval_hours: u32,
    },
}

/// 压缩策略
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum CompressionStrategy {
    /// 不压缩
    None,
    /// 立即压缩
    Immediate,
    /// 延迟压缩（指定天数后）
    Delayed { days: u32 },
}

/// 本地日志配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LocalLogConfig {
    /// 日志目录
    pub log_dir: PathBuf,
    /// 日志文件名前缀
    pub file_prefix: String,
    /// 日志级别
    pub level: LocalLogLevel,
    /// 滚动策略
    pub rotation_strategy: RotationStrategy,
    /// 压缩策略
    pub compression_strategy: CompressionStrategy,
    /// 最大文件数量
    pub max_files: u32,
    /// 缓存大小（字节）
    pub cache_size_bytes: usize,
    /// 是否启用异步写入
    pub async_write: bool,
    /// 是否启用控制台输出
    pub enable_console: bool,
    /// 是否启用文件输出
    pub enable_file: bool,
    /// 日志格式
    pub format: LogFormat,
    /// 是否包含时间戳
    pub include_timestamp: bool,
    /// 是否包含线程ID
    pub include_thread_id: bool,
}

impl Default for LocalLogConfig {
    fn default() -> Self {
        Self {
            log_dir: PathBuf::from("logs"),
            file_prefix: "app".to_string(),
            level: LocalLogLevel::Info,
            rotation_strategy: RotationStrategy::SizeAndTime {
                max_size_bytes: 10 * 1024 * 1024, // 10MB
                interval_hours: 24,               // 24小时
            },
            compression_strategy: CompressionStrategy::Delayed { days: 1 },
            max_files: 10,
            cache_size_bytes: 1024 * 1024, // 1MB
            async_write: true,
            enable_console: true,
            enable_file: true,
            format: LogFormat::Json,
            include_timestamp: true,
            include_thread_id: false,
        }
    }
}

/// 日志格式
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum LogFormat {
    Json,
    Text,
    Compact,
}

/// 日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct LocalLogEntry {
    pub timestamp: DateTime<Local>,
    pub level: LocalLogLevel,
    pub message: String,
    pub module: Option<String>,
    pub thread_id: Option<String>,
    pub fields: HashMap<String, String>,
}

/// 日志缓存
#[derive(Debug)]
pub struct LogCache {
    entries: Vec<LocalLogEntry>,
    max_size: usize,
    current_size: usize,
}

impl LogCache {
    pub fn new(max_size: usize) -> Self {
        Self {
            entries: Vec::new(),
            max_size,
            current_size: 0,
        }
    }

    pub fn add_entry(&mut self, entry: LocalLogEntry) -> bool {
        let entry_size = self.estimate_entry_size(&entry);

        // 如果添加这个条目会超过缓存大小，返回false
        if self.current_size + entry_size > self.max_size {
            return false;
        }

        self.entries.push(entry);
        self.current_size += entry_size;
        true
    }

    pub fn take_entries(&mut self) -> Vec<LocalLogEntry> {
        let entries = std::mem::take(&mut self.entries);
        self.current_size = 0;
        entries
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    fn estimate_entry_size(&self, entry: &LocalLogEntry) -> usize {
        // 估算日志条目的大小
        let mut size = entry.message.len();
        size += entry.module.as_ref().map_or(0, |m| m.len());
        size += entry.thread_id.as_ref().map_or(0, |t| t.len());
        size += entry
            .fields
            .iter()
            .map(|(k, v)| k.len() + v.len())
            .sum::<usize>();
        size += 100; // 时间戳和其他元数据的估算大小
        size
    }
}

/// 本地日志管理器
pub struct LocalLogManager {
    config: LocalLogConfig,
    cache: Arc<Mutex<LogCache>>,
    current_file: Arc<Mutex<Option<BufWriter<File>>>>,
    current_file_path: Arc<Mutex<PathBuf>>,
    current_file_size: Arc<Mutex<u64>>,
    last_rotation_time: Arc<Mutex<SystemTime>>,
    sender: Option<Sender<LocalLogEntry>>,
    worker_handle: Option<JoinHandle<()>>,
    compression_handle: Option<JoinHandle<()>>,
}

impl LocalLogManager {
    /// 创建新的本地日志管理器
    pub fn new(config: LocalLogConfig) -> Result<Self> {
        // 确保日志目录存在
        create_dir_all(&config.log_dir)
            .with_context(|| format!("Failed to create log directory: {:?}", config.log_dir))?;

        let cache = Arc::new(Mutex::new(LogCache::new(config.cache_size_bytes)));
        let current_file_path = Arc::new(Mutex::new(Self::generate_log_file_path(&config)?));
        let current_file_size = Arc::new(Mutex::new(0));
        let last_rotation_time = Arc::new(Mutex::new(SystemTime::now()));

        let mut manager = Self {
            config,
            cache,
            current_file: Arc::new(Mutex::new(None)),
            current_file_path,
            current_file_size,
            last_rotation_time,
            sender: None,
            worker_handle: None,
            compression_handle: None,
        };

        manager.initialize()?;
        Ok(manager)
    }

    /// 初始化日志管理器
    fn initialize(&mut self) -> Result<()> {
        // 初始化当前日志文件
        self.open_current_log_file()?;

        // 启动异步写入器
        if self.config.async_write {
            self.start_async_writer()?;
        }

        // 启动压缩器
        self.start_compression_worker()?;

        info!("Local log manager initialized successfully");
        Ok(())
    }

    /// 生成日志文件路径
    fn generate_log_file_path(config: &LocalLogConfig) -> Result<PathBuf> {
        let now = Local::now();
        let date_str = now.format("%Y-%m-%d").to_string();
        let time_str = now.format("%H-%M-%S").to_string();

        let filename = match &config.rotation_strategy {
            RotationStrategy::Time { .. } | RotationStrategy::SizeAndTime { .. } => {
                format!("{}_{}_{}.log", config.file_prefix, date_str, time_str)
            }
            _ => {
                format!("{}_{}.log", config.file_prefix, date_str)
            }
        };

        Ok(config.log_dir.join(filename))
    }

    /// 打开当前日志文件
    fn open_current_log_file(&self) -> Result<()> {
        let file_path = self.current_file_path.lock().unwrap().clone();

        // 确保目录存在
        if let Some(parent) = file_path.parent() {
            create_dir_all(parent)?;
        }

        let file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&file_path)?;

        let writer = BufWriter::new(file);
        *self.current_file.lock().unwrap() = Some(writer);

        // 获取当前文件大小
        if let Ok(metadata) = metadata(&file_path) {
            *self.current_file_size.lock().unwrap() = metadata.len();
        }

        info!("Opened log file: {:?}", file_path);
        Ok(())
    }

    /// 启动异步写入器
    fn start_async_writer(&mut self) -> Result<()> {
        let (sender, receiver) = mpsc::channel();
        self.sender = Some(sender);

        let cache = self.cache.clone();
        let current_file = self.current_file.clone();
        let current_file_path = self.current_file_path.clone();
        let current_file_size = self.current_file_size.clone();
        let last_rotation_time = self.last_rotation_time.clone();
        let config = self.config.clone();

        let handle = thread::spawn(move || {
            Self::async_writer_worker(
                receiver,
                cache,
                current_file,
                current_file_path,
                current_file_size,
                last_rotation_time,
                config,
            );
        });

        self.worker_handle = Some(handle);
        Ok(())
    }

    /// 异步写入器工作线程
    fn async_writer_worker(
        receiver: Receiver<LocalLogEntry>,
        cache: Arc<Mutex<LogCache>>,
        current_file: Arc<Mutex<Option<BufWriter<File>>>>,
        current_file_path: Arc<Mutex<PathBuf>>,
        current_file_size: Arc<Mutex<u64>>,
        last_rotation_time: Arc<Mutex<SystemTime>>,
        config: LocalLogConfig,
    ) {
        let mut batch = Vec::new();
        let mut last_flush = Instant::now();
        let flush_interval = Duration::from_millis(100);

        while let Ok(entry) = receiver.recv() {
            batch.push(entry);

            // 检查是否需要刷新
            if batch.len() >= 100 || last_flush.elapsed() >= flush_interval {
                if let Err(e) = Self::flush_batch(
                    &batch,
                    &cache,
                    &current_file,
                    &current_file_path,
                    &current_file_size,
                    &last_rotation_time,
                    &config,
                ) {
                    eprintln!("Failed to flush log batch: {}", e);
                }
                batch.clear();
                last_flush = Instant::now();
            }
        }

        // 处理剩余的日志条目
        if !batch.is_empty()
            && let Err(e) = Self::flush_batch(
                &batch,
                &cache,
                &current_file,
                &current_file_path,
                &current_file_size,
                &last_rotation_time,
                &config,
            ) {
                eprintln!("Failed to flush final log batch: {}", e);
            }
    }

    /// 刷新日志批次
    fn flush_batch(
        batch: &[LocalLogEntry],
        cache: &Arc<Mutex<LogCache>>,
        current_file: &Arc<Mutex<Option<BufWriter<File>>>>,
        current_file_path: &Arc<Mutex<PathBuf>>,
        current_file_size: &Arc<Mutex<u64>>,
        last_rotation_time: &Arc<Mutex<SystemTime>>,
        config: &LocalLogConfig,
    ) -> Result<()> {
        // 将日志条目添加到缓存
        for entry in batch {
            let mut cache_guard = cache.lock().unwrap();
            if !cache_guard.add_entry(entry.clone()) {
                // 缓存满了，先刷新缓存
                let entries = cache_guard.take_entries();
                drop(cache_guard);
                Self::write_entries_to_file(
                    &entries,
                    current_file,
                    current_file_path,
                    current_file_size,
                    last_rotation_time,
                    config,
                )?;

                // 重新尝试添加
                let mut cache_guard = cache.lock().unwrap();
                cache_guard.add_entry(entry.clone());
            }
        }

        // 检查是否需要刷新缓存
        let should_flush = {
            let cache_guard = cache.lock().unwrap();
            cache_guard.len() >= 50 // 每50条日志刷新一次
        };

        if should_flush {
            let mut cache_guard = cache.lock().unwrap();
            let entries = cache_guard.take_entries();
            drop(cache_guard);
            Self::write_entries_to_file(
                &entries,
                current_file,
                current_file_path,
                current_file_size,
                last_rotation_time,
                config,
            )?;
        }

        Ok(())
    }

    /// 将日志条目写入文件
    fn write_entries_to_file(
        entries: &[LocalLogEntry],
        current_file: &Arc<Mutex<Option<BufWriter<File>>>>,
        current_file_path: &Arc<Mutex<PathBuf>>,
        current_file_size: &Arc<Mutex<u64>>,
        last_rotation_time: &Arc<Mutex<SystemTime>>,
        config: &LocalLogConfig,
    ) -> Result<()> {
        if entries.is_empty() {
            return Ok(());
        }

        // 检查是否需要轮转
        if Self::should_rotate(current_file_size, last_rotation_time, config)? {
            Self::rotate_log_file(
                current_file,
                current_file_path,
                current_file_size,
                last_rotation_time,
                config,
            )?;
        }

        // 写入日志条目
        if let Some(ref mut writer) = *current_file.lock().unwrap() {
            for entry in entries {
                let formatted = Self::format_log_entry(entry, config)?;
                writeln!(writer, "{}", formatted)?;

                // 更新文件大小
                *current_file_size.lock().unwrap() += formatted.len() as u64 + 1; // +1 for newline
            }
            writer.flush()?;
        }

        Ok(())
    }

    /// 检查是否需要轮转日志文件
    fn should_rotate(
        current_file_size: &Arc<Mutex<u64>>,
        last_rotation_time: &Arc<Mutex<SystemTime>>,
        config: &LocalLogConfig,
    ) -> Result<bool> {
        let current_size = *current_file_size.lock().unwrap();
        let last_rotation = *last_rotation_time.lock().unwrap();
        let now = SystemTime::now();

        match &config.rotation_strategy {
            RotationStrategy::Size { max_size_bytes } => Ok(current_size >= *max_size_bytes),
            RotationStrategy::Time { interval_hours } => {
                let interval = Duration::from_secs(*interval_hours as u64 * 3600);
                Ok(now.duration_since(last_rotation)? >= interval)
            }
            RotationStrategy::SizeAndTime {
                max_size_bytes,
                interval_hours,
            } => {
                let size_rotation = current_size >= *max_size_bytes;
                let interval = Duration::from_secs(*interval_hours as u64 * 3600);
                let time_rotation = now.duration_since(last_rotation)? >= interval;
                Ok(size_rotation || time_rotation)
            }
        }
    }

    /// 轮转日志文件
    fn rotate_log_file(
        current_file: &Arc<Mutex<Option<BufWriter<File>>>>,
        current_file_path: &Arc<Mutex<PathBuf>>,
        current_file_size: &Arc<Mutex<u64>>,
        last_rotation_time: &Arc<Mutex<SystemTime>>,
        config: &LocalLogConfig,
    ) -> Result<()> {
        // 关闭当前文件
        if let Some(ref mut writer) = *current_file.lock().unwrap() {
            writer.flush()?;
        }
        *current_file.lock().unwrap() = None;

        // 生成新的文件路径
        let new_path = Self::generate_log_file_path(config)?;
        let old_path = current_file_path.lock().unwrap().clone();

        // 重命名当前文件
        if old_path.exists() {
            let timestamp = Local::now().format("%Y%m%d_%H%M%S").to_string();
            let rotated_path = old_path.with_extension(format!("{}.log", timestamp));
            rename(&old_path, &rotated_path)?;
            info!("Rotated log file: {:?} -> {:?}", old_path, rotated_path);
        }

        // 更新文件路径和大小
        *current_file_path.lock().unwrap() = new_path.clone();
        *current_file_size.lock().unwrap() = 0;
        *last_rotation_time.lock().unwrap() = SystemTime::now();

        // 打开新文件
        let file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&new_path)?;
        let writer = BufWriter::new(file);
        *current_file.lock().unwrap() = Some(writer);

        // 清理旧文件
        Self::cleanup_old_files(&config.log_dir, &config.file_prefix, config.max_files)?;

        info!("Log file rotated to: {:?}", new_path);
        Ok(())
    }

    /// 清理旧文件
    fn cleanup_old_files(log_dir: &Path, file_prefix: &str, max_files: u32) -> Result<()> {
        let mut log_files = Vec::new();

        for entry in std::fs::read_dir(log_dir)? {
            let entry = entry?;
            let path = entry.path();

            if path.is_file()
                && let Some(filename) = path.file_name().and_then(|n| n.to_str())
                    && filename.starts_with(file_prefix) && filename.ends_with(".log")
                        && let Ok(metadata) = entry.metadata() {
                            log_files.push((path, metadata.modified()?));
                        }
        }

        // 按修改时间排序（最新的在前）
        log_files.sort_by(|a, b| b.1.cmp(&a.1));

        // 删除超出限制的文件
        for (path, _) in log_files.into_iter().skip(max_files as usize) {
            if let Err(e) = remove_file(&path) {
                warn!("Failed to remove old log file {:?}: {}", path, e);
            } else {
                info!("Removed old log file: {:?}", path);
            }
        }

        Ok(())
    }

    /// 格式化日志条目
    fn format_log_entry(entry: &LocalLogEntry, config: &LocalLogConfig) -> Result<String> {
        match config.format {
            LogFormat::Json => Ok(serde_json::to_string(entry)?),
            LogFormat::Text => {
                let mut formatted = String::new();

                if config.include_timestamp {
                    formatted.push_str(&format!(
                        "[{}] ",
                        entry.timestamp.format("%Y-%m-%d %H:%M:%S%.3f")
                    ));
                }

                formatted.push_str(&format!("{} ", entry.level));

                if let Some(ref module) = entry.module {
                    formatted.push_str(&format!("[{}] ", module));
                }

                if config.include_thread_id
                    && let Some(ref thread_id) = entry.thread_id {
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
            }
            LogFormat::Compact => {
                let mut formatted = String::new();
                formatted.push_str(&format!(
                    "{} {} {}",
                    entry.timestamp.format("%H:%M:%S%.3f"),
                    entry.level,
                    entry.message
                ));

                if !entry.fields.is_empty() {
                    formatted.push_str(" |");
                    for (key, value) in &entry.fields {
                        formatted.push_str(&format!(" {}={}", key, value));
                    }
                }

                Ok(formatted)
            }
        }
    }

    /// 启动压缩工作线程
    fn start_compression_worker(&mut self) -> Result<()> {
        let log_dir = self.config.log_dir.clone();
        let compression_strategy = self.config.compression_strategy.clone();
        let file_prefix = self.config.file_prefix.clone();

        let handle = thread::spawn(move || {
            Self::compression_worker(log_dir, compression_strategy, file_prefix);
        });

        self.compression_handle = Some(handle);
        Ok(())
    }

    /// 压缩工作线程
    fn compression_worker(
        log_dir: PathBuf,
        compression_strategy: CompressionStrategy,
        file_prefix: String,
    ) {
        let mut last_compression = Instant::now();
        let compression_interval = Duration::from_secs(3600); // 每小时检查一次

        loop {
            thread::sleep(Duration::from_secs(60)); // 每分钟检查一次

            if last_compression.elapsed() >= compression_interval {
                if let Err(e) =
                    Self::compress_log_files(&log_dir, &compression_strategy, &file_prefix)
                {
                    eprintln!("Failed to compress log files: {}", e);
                }
                last_compression = Instant::now();
            }
        }
    }

    /// 压缩日志文件
    fn compress_log_files(
        log_dir: &Path,
        compression_strategy: &CompressionStrategy,
        file_prefix: &str,
    ) -> Result<()> {
        match compression_strategy {
            CompressionStrategy::None => return Ok(()),
            CompressionStrategy::Immediate => {
                Self::compress_eligible_files(log_dir, file_prefix, Duration::from_secs(0))?;
            }
            CompressionStrategy::Delayed { days } => {
                let delay = Duration::from_secs(*days as u64 * 24 * 3600);
                Self::compress_eligible_files(log_dir, file_prefix, delay)?;
            }
        }
        Ok(())
    }

    /// 压缩符合条件的文件
    fn compress_eligible_files(log_dir: &Path, file_prefix: &str, delay: Duration) -> Result<()> {
        for entry in std::fs::read_dir(log_dir)? {
            let entry = entry?;
            let path = entry.path();

            if path.is_file()
                && let Some(filename) = path.file_name().and_then(|n| n.to_str())
                    && filename.starts_with(file_prefix)
                        && filename.ends_with(".log")
                        && !filename.ends_with(".gz")
                        && let Ok(metadata) = entry.metadata() {
                            let modified = metadata.modified()?;
                            let now = SystemTime::now();

                            if now.duration_since(modified)? >= delay {
                                Self::compress_file(&path)?;
                            }
                        }
        }
        Ok(())
    }

    /// 压缩单个文件
    fn compress_file(file_path: &Path) -> Result<()> {
        let compressed_path = file_path.with_extension("log.gz");

        // 读取原文件
        let file = File::open(file_path)?;
        let reader = BufReader::new(file);

        // 创建压缩文件
        let compressed_file = File::create(&compressed_path)?;
        let mut encoder = GzEncoder::new(compressed_file, Compression::default());

        // 压缩内容
        for line in reader.lines() {
            let line = line?;
            writeln!(encoder, "{}", line)?;
        }

        encoder.finish()?;

        // 删除原文件
        remove_file(file_path)?;

        info!(
            "Compressed log file: {:?} -> {:?}",
            file_path, compressed_path
        );
        Ok(())
    }

    /// 记录日志
    pub fn log(
        &self,
        level: LocalLogLevel,
        message: &str,
        fields: Option<HashMap<String, String>>,
    ) {
        if level < self.config.level {
            return;
        }

        let entry = LocalLogEntry {
            timestamp: Local::now(),
            level,
            message: message.to_string(),
            module: None,
            thread_id: if self.config.include_thread_id {
                Some(format!("{:?}", thread::current().id()))
            } else {
                None
            },
            fields: fields.unwrap_or_default(),
        };

        // 控制台输出
        if self.config.enable_console {
            match level {
                LocalLogLevel::Debug => debug!("{}", message),
                LocalLogLevel::Info => info!("{}", message),
                LocalLogLevel::Warn => warn!("{}", message),
                LocalLogLevel::Error => error!("{}", message),
            }
        }

        // 文件输出
        if self.config.enable_file {
            if let Some(ref sender) = self.sender {
                if let Err(e) = sender.send(entry) {
                    eprintln!("Failed to send log entry: {}", e);
                }
            } else {
                // 同步写入
                if let Err(e) = self.write_entry_sync(entry) {
                    eprintln!("Failed to write log entry: {}", e);
                }
            }
        }
    }

    /// 同步写入日志条目
    fn write_entry_sync(&self, entry: LocalLogEntry) -> Result<()> {
        let formatted = Self::format_log_entry(&entry, &self.config)?;

        // 同步路径也需要进行滚动检查
        if Self::should_rotate(
            &self.current_file_size,
            &self.last_rotation_time,
            &self.config,
        )? {
            Self::rotate_log_file(
                &self.current_file,
                &self.current_file_path,
                &self.current_file_size,
                &self.last_rotation_time,
                &self.config,
            )?;
        }

        if let Some(ref mut writer) = *self.current_file.lock().unwrap() {
            writeln!(writer, "{}", formatted)?;
            writer.flush()?;

            // 更新文件大小
            *self.current_file_size.lock().unwrap() += formatted.len() as u64 + 1;
        }

        Ok(())
    }

    /// 获取日志统计信息
    pub fn get_stats(&self) -> LogStats {
        let cache_guard = self.cache.lock().unwrap();
        let current_size = *self.current_file_size.lock().unwrap();

        LogStats {
            cache_entries: cache_guard.len(),
            cache_size_bytes: cache_guard.current_size,
            current_file_size_bytes: current_size,
            current_file_path: self.current_file_path.lock().unwrap().clone(),
        }
    }

    /// 强制刷新所有缓存
    pub fn flush(&self) -> Result<()> {
        let mut cache_guard = self.cache.lock().unwrap();
        let entries = cache_guard.take_entries();
        drop(cache_guard);

        if !entries.is_empty() {
            Self::write_entries_to_file(
                &entries,
                &self.current_file,
                &self.current_file_path,
                &self.current_file_size,
                &self.last_rotation_time,
                &self.config,
            )?;
        }

        // 刷新文件缓冲区
        if let Some(ref mut writer) = *self.current_file.lock().unwrap() {
            writer.flush()?;
        }

        Ok(())
    }

    /// 关闭日志管理器
    pub fn shutdown(mut self) -> Result<()> {
        // 刷新所有缓存
        self.flush()?;

        // 关闭异步写入器
        if let Some(sender) = self.sender.take() {
            drop(sender);
        }

        if let Some(handle) = self.worker_handle.take() {
            handle
                .join()
                .map_err(|_| anyhow::anyhow!("Failed to join async writer thread"))?;
        }

        // 关闭压缩器
        if let Some(handle) = self.compression_handle.take() {
            handle
                .join()
                .map_err(|_| anyhow::anyhow!("Failed to join compression thread"))?;
        }

        info!("Local log manager shutdown completed");
        Ok(())
    }
}

/// 日志统计信息
#[derive(Debug, Clone)]
pub struct LogStats {
    pub cache_entries: usize,
    pub cache_size_bytes: usize,
    pub current_file_size_bytes: u64,
    pub current_file_path: PathBuf,
}

impl Drop for LocalLogManager {
    fn drop(&mut self) {
        if let Err(e) = self.flush() {
            eprintln!("Failed to flush logs on drop: {}", e);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::tempdir;

    #[test]
    fn test_local_log_manager_creation() {
        let temp_dir = tempdir().unwrap();
        let config = LocalLogConfig {
            log_dir: temp_dir.path().to_path_buf(),
            ..Default::default()
        };

        let manager = LocalLogManager::new(config);
        assert!(manager.is_ok());
    }

    #[test]
    fn test_log_rotation_by_size() {
        let temp_dir = tempdir().unwrap();
        let config = LocalLogConfig {
            log_dir: temp_dir.path().to_path_buf(),
            rotation_strategy: RotationStrategy::Size {
                max_size_bytes: 200,
            },
            async_write: false,
            ..Default::default()
        };

        let manager = LocalLogManager::new(config).unwrap();

        // 写入日志以触发轮转（同步写入每条都会检查大小）
        for i in 0..200 {
            manager.log(
                LocalLogLevel::Info,
                &format!("Test message {} - some payload to increase size", i),
                None,
            );
        }

        manager.flush().unwrap();

        // 检查是否创建了多个日志文件
        let entries: Vec<_> = fs::read_dir(temp_dir.path()).unwrap().collect();
        assert!(entries.len() > 1);
    }

    #[test]
    fn test_log_compression() {
        let temp_dir = tempdir().unwrap();
        let config = LocalLogConfig {
            log_dir: temp_dir.path().to_path_buf(),
            compression_strategy: CompressionStrategy::Immediate,
            ..Default::default()
        };

        let manager = LocalLogManager::new(config).unwrap();
        manager.log(LocalLogLevel::Info, "Test message", None);
        manager.flush().unwrap();
        manager.shutdown().unwrap();

        // 检查是否创建了压缩文件
        let entries: Vec<_> = fs::read_dir(temp_dir.path()).unwrap().collect();
        let has_gz_file = entries.iter().any(|entry| {
            entry
                .as_ref()
                .unwrap()
                .path()
                .extension()
                .and_then(|s| s.to_str())
                == Some("gz")
        });
        assert!(has_gz_file);
    }

    #[test]
    fn test_log_levels() {
        let temp_dir = tempdir().unwrap();
        let config = LocalLogConfig {
            log_dir: temp_dir.path().to_path_buf(),
            level: LocalLogLevel::Warn,
            async_write: false,
            ..Default::default()
        };

        let manager = LocalLogManager::new(config).unwrap();

        manager.log(LocalLogLevel::Debug, "Debug message", None);
        manager.log(LocalLogLevel::Info, "Info message", None);
        manager.log(LocalLogLevel::Warn, "Warn message", None);
        manager.log(LocalLogLevel::Error, "Error message", None);

        manager.flush().unwrap();

        // 刷新后缓存会被清空，改为检查文件中的有效行数（至少应包含 Warn 与 Error 两条）
        let stats = manager.get_stats();
        let file = File::open(stats.current_file_path).unwrap();
        let reader = BufReader::new(file);
        let lines: Vec<_> = reader.lines().collect::<std::io::Result<_>>().unwrap();
        assert!(lines.len() >= 2);
    }
}
