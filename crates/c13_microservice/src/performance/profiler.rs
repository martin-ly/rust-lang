//! 性能分析器模块
//!
//! 提供性能事件记录和分析功能

use std::collections::HashMap;
use std::time::{Duration, Instant, SystemTime};
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// 性能分析器
#[derive(Debug)]
pub struct PerformanceProfiler {
    config: ProfilerConfig,
    events: Vec<ProfilerEvent>,
    start_time: Option<Instant>,
    is_running: bool,
    stats: ProfilerStats,
}

impl PerformanceProfiler {
    /// 创建新的性能分析器
    pub fn new(config: ProfilerConfig) -> Self {
        Self {
            config,
            events: Vec::new(),
            start_time: None,
            is_running: false,
            stats: ProfilerStats::default(),
        }
    }

    /// 开始性能分析
    pub fn start(&mut self) -> ProfilerResult<()> {
        if self.is_running {
            return Err(ProfilerError::AlreadyRunning);
        }

        self.start_time = Some(Instant::now());
        self.is_running = true;
        self.events.clear();
        self.stats = ProfilerStats::default();

        // 记录开始事件
        self.record_event(ProfilerEvent::new(
            "profiler_start".to_string(),
            "system".to_string(),
            ProfilerEventType::System,
        ))?;

        Ok(())
    }

    /// 停止性能分析
    pub fn stop(&mut self) -> ProfilerResult<ProfilerStats> {
        if !self.is_running {
            return Err(ProfilerError::NotRunning);
        }

        // 记录停止事件
        self.record_event(ProfilerEvent::new(
            "profiler_stop".to_string(),
            "system".to_string(),
            ProfilerEventType::System,
        ))?;

        self.is_running = false;
        
        // 计算统计信息
        self.calculate_stats();
        
        Ok(self.stats.clone())
    }

    /// 记录性能事件
    pub fn record_event(&mut self, mut event: ProfilerEvent) -> ProfilerResult<()> {
        if !self.is_running {
            return Err(ProfilerError::NotRunning);
        }

        // 设置时间戳
        if let Some(start_time) = self.start_time {
            event.timestamp = Some(SystemTime::now());
            event.relative_time = Some(Instant::now().duration_since(start_time));
        }

        // 检查事件数量限制
        if self.events.len() >= self.config.max_events {
            return Err(ProfilerError::MaxEventsExceeded);
        }

        self.events.push(event);
        Ok(())
    }

    /// 记录函数执行时间
    pub fn record_function_execution(&mut self, function_name: String, duration: Duration) -> ProfilerResult<()> {
        let event = ProfilerEvent {
            name: format!("function_{}", function_name),
            category: "function".to_string(),
            event_type: ProfilerEventType::Function,
            timestamp: Some(SystemTime::now()),
            relative_time: self.start_time.map(|start| Instant::now().duration_since(start)),
            duration: Some(duration),
            metadata: HashMap::new(),
            tags: Vec::new(),
        };

        self.record_event(event)
    }

    /// 记录内存使用情况
    pub fn record_memory_usage(&mut self, memory_usage: usize) -> ProfilerResult<()> {
        let mut metadata = HashMap::new();
        metadata.insert("memory_bytes".to_string(), memory_usage.to_string());

        let event = ProfilerEvent {
            name: "memory_usage".to_string(),
            category: "memory".to_string(),
            event_type: ProfilerEventType::Memory,
            timestamp: Some(SystemTime::now()),
            relative_time: self.start_time.map(|start| Instant::now().duration_since(start)),
            duration: None,
            metadata,
            tags: Vec::new(),
        };

        self.record_event(event)
    }

    /// 记录网络请求
    pub fn record_network_request(&mut self, url: String, method: String, status_code: u16, duration: Duration) -> ProfilerResult<()> {
        let mut metadata = HashMap::new();
        metadata.insert("url".to_string(), url);
        metadata.insert("method".to_string(), method);
        metadata.insert("status_code".to_string(), status_code.to_string());

        let event = ProfilerEvent {
            name: "network_request".to_string(),
            category: "network".to_string(),
            event_type: ProfilerEventType::Network,
            timestamp: Some(SystemTime::now()),
            relative_time: self.start_time.map(|start| Instant::now().duration_since(start)),
            duration: Some(duration),
            metadata,
            tags: Vec::new(),
        };

        self.record_event(event)
    }

    /// 记录数据库查询
    pub fn record_database_query(&mut self, query: String, duration: Duration, rows_affected: Option<usize>) -> ProfilerResult<()> {
        let mut metadata = HashMap::new();
        metadata.insert("query".to_string(), query);
        if let Some(rows) = rows_affected {
            metadata.insert("rows_affected".to_string(), rows.to_string());
        }

        let event = ProfilerEvent {
            name: "database_query".to_string(),
            category: "database".to_string(),
            event_type: ProfilerEventType::Database,
            timestamp: Some(SystemTime::now()),
            relative_time: self.start_time.map(|start| Instant::now().duration_since(start)),
            duration: Some(duration),
            metadata,
            tags: Vec::new(),
        };

        self.record_event(event)
    }

    /// 获取性能统计信息
    pub fn get_stats(&self) -> ProfilerResult<ProfilerStats> {
        if self.is_running {
            // 如果正在运行，计算当前统计信息
            let mut stats = self.stats.clone();
            self.calculate_current_stats(&mut stats);
            Ok(stats)
        } else {
            Ok(self.stats.clone())
        }
    }

    /// 获取所有事件
    pub fn get_events(&self) -> &[ProfilerEvent] {
        &self.events
    }

    /// 按类别获取事件
    pub fn get_events_by_category(&self, category: &str) -> Vec<&ProfilerEvent> {
        self.events.iter().filter(|event| event.category == category).collect()
    }

    /// 按类型获取事件
    pub fn get_events_by_type(&self, event_type: ProfilerEventType) -> Vec<&ProfilerEvent> {
        self.events.iter().filter(|event| event.event_type == event_type).collect()
    }

    /// 重置分析器
    pub fn reset(&mut self) -> ProfilerResult<()> {
        if self.is_running {
            return Err(ProfilerError::StillRunning);
        }

        self.events.clear();
        self.stats = ProfilerStats::default();
        self.start_time = None;
        Ok(())
    }

    /// 计算统计信息
    fn calculate_stats(&mut self) {
        self.stats.total_events = self.events.len();
        self.stats.categories = self.calculate_category_stats();
        self.stats.event_types = self.calculate_event_type_stats();
        self.stats.timing_stats = self.calculate_timing_stats();
        self.stats.memory_stats = self.calculate_memory_stats();
    }

    /// 计算当前统计信息
    fn calculate_current_stats(&self, stats: &mut ProfilerStats) {
        stats.total_events = self.events.len();
        stats.categories = self.calculate_category_stats();
        stats.event_types = self.calculate_event_type_stats();
        stats.timing_stats = self.calculate_timing_stats();
        stats.memory_stats = self.calculate_memory_stats();
    }

    /// 计算类别统计信息
    fn calculate_category_stats(&self) -> HashMap<String, CategoryStats> {
        let mut category_counts: HashMap<String, usize> = HashMap::new();
        let mut category_durations: HashMap<String, Vec<Duration>> = HashMap::new();

        for event in &self.events {
            *category_counts.entry(event.category.clone()).or_insert(0) += 1;
            
            if let Some(duration) = event.duration {
                category_durations.entry(event.category.clone())
                    .or_insert_with(Vec::new)
                    .push(duration);
            }
        }

        let mut category_stats = HashMap::new();
        for (category, count) in category_counts {
            let durations = category_durations.remove(&category).unwrap_or_default();
            category_stats.insert(category, CategoryStats {
                count,
                total_duration: durations.iter().sum(),
                average_duration: if durations.is_empty() {
                    Duration::ZERO
                } else {
                    Duration::from_nanos(
                        durations.iter().map(|d| d.as_nanos()).sum::<u128>() as u64 / durations.len() as u64
                    )
                },
                min_duration: durations.iter().min().copied().unwrap_or(Duration::ZERO),
                max_duration: durations.iter().max().copied().unwrap_or(Duration::ZERO),
            });
        }

        category_stats
    }

    /// 计算事件类型统计信息
    fn calculate_event_type_stats(&self) -> HashMap<ProfilerEventType, usize> {
        let mut type_counts: HashMap<ProfilerEventType, usize> = HashMap::new();
        
        for event in &self.events {
            *type_counts.entry(event.event_type.clone()).or_insert(0) += 1;
        }

        type_counts
    }

    /// 计算时间统计信息
    fn calculate_timing_stats(&self) -> TimingStats {
        let mut total_duration = Duration::ZERO;
        let mut durations = Vec::new();

        for event in &self.events {
            if let Some(duration) = event.duration {
                total_duration += duration;
                durations.push(duration);
            }
        }

        durations.sort();

        TimingStats {
            total_duration,
            average_duration: if durations.is_empty() {
                Duration::ZERO
            } else {
                Duration::from_nanos(
                    durations.iter().map(|d| d.as_nanos()).sum::<u128>() as u64 / durations.len() as u64
                )
            },
            min_duration: durations.first().copied().unwrap_or(Duration::ZERO),
            max_duration: durations.last().copied().unwrap_or(Duration::ZERO),
            median_duration: if durations.is_empty() {
                Duration::ZERO
            } else {
                durations[durations.len() / 2]
            },
            percentile_95: if durations.len() >= 20 {
                durations[(durations.len() as f64 * 0.95) as usize]
            } else {
                durations.last().copied().unwrap_or(Duration::ZERO)
            },
            percentile_99: if durations.len() >= 100 {
                durations[(durations.len() as f64 * 0.99) as usize]
            } else {
                durations.last().copied().unwrap_or(Duration::ZERO)
            },
        }
    }

    /// 计算内存统计信息
    fn calculate_memory_stats(&self) -> MemoryStats {
        let memory_events = self.get_events_by_type(ProfilerEventType::Memory);
        let mut memory_usage_values = Vec::new();
        let mut total_memory = 0;

        for event in memory_events {
            if let Some(memory_str) = event.metadata.get("memory_bytes") {
                if let Ok(memory_bytes) = memory_str.parse::<usize>() {
                    memory_usage_values.push(memory_bytes);
                    total_memory += memory_bytes;
                }
            }
        }

        memory_usage_values.sort();

        MemoryStats {
            total_memory,
            average_memory: if memory_usage_values.is_empty() {
                0
            } else {
                total_memory / memory_usage_values.len()
            },
            min_memory: memory_usage_values.first().copied().unwrap_or(0),
            max_memory: memory_usage_values.last().copied().unwrap_or(0),
            memory_samples: memory_usage_values.len(),
        }
    }
}

/// 性能分析器配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProfilerConfig {
    pub max_events: usize,
    pub enable_memory_profiling: bool,
    pub enable_cpu_profiling: bool,
    pub enable_network_profiling: bool,
    pub sampling_rate: f64, // 0.0 - 1.0
    pub buffer_size: usize,
}

impl Default for ProfilerConfig {
    fn default() -> Self {
        Self {
            max_events: 10000,
            enable_memory_profiling: true,
            enable_cpu_profiling: true,
            enable_network_profiling: true,
            sampling_rate: 1.0,
            buffer_size: 1000,
        }
    }
}

/// 性能事件
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProfilerEvent {
    pub name: String,
    pub category: String,
    pub event_type: ProfilerEventType,
    pub timestamp: Option<SystemTime>,
    pub relative_time: Option<Duration>,
    pub duration: Option<Duration>,
    pub metadata: HashMap<String, String>,
    pub tags: Vec<String>,
}

impl ProfilerEvent {
    /// 创建新的性能事件
    pub fn new(name: String, category: String, event_type: ProfilerEventType) -> Self {
        Self {
            name,
            category,
            event_type,
            timestamp: None,
            relative_time: None,
            duration: None,
            metadata: HashMap::new(),
            tags: Vec::new(),
        }
    }

    /// 添加元数据
    pub fn with_metadata(mut self, key: String, value: String) -> Self {
        self.metadata.insert(key, value);
        self
    }

    /// 添加标签
    pub fn with_tag(mut self, tag: String) -> Self {
        self.tags.push(tag);
        self
    }

    /// 设置持续时间
    pub fn with_duration(mut self, duration: Duration) -> Self {
        self.duration = Some(duration);
        self
    }
}

/// 性能事件类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ProfilerEventType {
    Function,
    Memory,
    Network,
    Database,
    System,
    Custom,
}

/// 性能统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProfilerStats {
    pub total_events: usize,
    pub categories: HashMap<String, CategoryStats>,
    pub event_types: HashMap<ProfilerEventType, usize>,
    pub timing_stats: TimingStats,
    pub memory_stats: MemoryStats,
}

impl Default for ProfilerStats {
    fn default() -> Self {
        Self {
            total_events: 0,
            categories: HashMap::new(),
            event_types: HashMap::new(),
            timing_stats: TimingStats::default(),
            memory_stats: MemoryStats::default(),
        }
    }
}

/// 类别统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CategoryStats {
    pub count: usize,
    pub total_duration: Duration,
    pub average_duration: Duration,
    pub min_duration: Duration,
    pub max_duration: Duration,
}

/// 时间统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TimingStats {
    pub total_duration: Duration,
    pub average_duration: Duration,
    pub min_duration: Duration,
    pub max_duration: Duration,
    pub median_duration: Duration,
    pub percentile_95: Duration,
    pub percentile_99: Duration,
}

impl Default for TimingStats {
    fn default() -> Self {
        Self {
            total_duration: Duration::ZERO,
            average_duration: Duration::ZERO,
            min_duration: Duration::ZERO,
            max_duration: Duration::ZERO,
            median_duration: Duration::ZERO,
            percentile_95: Duration::ZERO,
            percentile_99: Duration::ZERO,
        }
    }
}

/// 内存统计信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryStats {
    pub total_memory: usize,
    pub average_memory: usize,
    pub min_memory: usize,
    pub max_memory: usize,
    pub memory_samples: usize,
}

impl Default for MemoryStats {
    fn default() -> Self {
        Self {
            total_memory: 0,
            average_memory: 0,
            min_memory: 0,
            max_memory: 0,
            memory_samples: 0,
        }
    }
}

/// 性能分析器错误
#[derive(Error, Debug)]
pub enum ProfilerError {
    #[error("分析器已经在运行")]
    AlreadyRunning,
    #[error("分析器没有运行")]
    NotRunning,
    #[error("分析器仍在运行")]
    StillRunning,
    #[error("超过最大事件数量限制")]
    MaxEventsExceeded,
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    #[error("事件记录错误: {0}")]
    EventRecordingError(String),
}

/// 性能分析器结果类型别名
pub type ProfilerResult<T> = Result<T, ProfilerError>;
