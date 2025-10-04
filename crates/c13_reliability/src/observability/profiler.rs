//! # 性能剖析器（Profiler）
//!
//! 提供CPU、内存和IO性能剖析功能。

use crate::prelude::*;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

/// 性能剖析类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ProfileType {
    /// CPU剖析
    Cpu,
    /// 内存剖析
    Memory,
    /// IO剖析
    Io,
    /// 锁竞争剖析
    LockContention,
}

/// CPU采样数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CpuSample {
    #[serde(skip, default = "Instant::now")]
    pub timestamp: Instant,
    pub function_name: String,
    #[serde(with = "crate::utils::serde_duration")]
    pub duration: Duration,
    pub call_stack: Vec<String>,
}

/// 内存采样数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemorySample {
    #[serde(skip, default = "Instant::now")]
    pub timestamp: Instant,
    pub location: String,
    pub allocated_bytes: usize,
    pub freed_bytes: usize,
    pub total_allocations: usize,
}

/// IO采样数据
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IoSample {
    #[serde(skip, default = "Instant::now")]
    pub timestamp: Instant,
    pub operation_type: IoOperationType,
    pub bytes_transferred: usize,
    #[serde(with = "crate::utils::serde_duration")]
    pub duration: Duration,
    pub file_path: Option<String>,
}

/// IO操作类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum IoOperationType {
    Read,
    Write,
    Seek,
    Flush,
}

/// 函数调用统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FunctionStats {
    pub function_name: String,
    pub call_count: u64,
    #[serde(with = "crate::utils::serde_duration")]
    pub total_duration: Duration,
    #[serde(with = "crate::utils::serde_duration")]
    pub avg_duration: Duration,
    #[serde(with = "crate::utils::serde_duration")]
    pub min_duration: Duration,
    #[serde(with = "crate::utils::serde_duration")]
    pub max_duration: Duration,
    #[serde(with = "crate::utils::serde_duration")]
    pub self_time: Duration, // 不包括子函数调用的时间
}

/// 内存分配统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MemoryStats {
    pub location: String,
    pub total_allocated: usize,
    pub total_freed: usize,
    pub current_usage: usize,
    pub peak_usage: usize,
    pub allocation_count: usize,
}

/// 性能剖析报告
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProfileReport {
    pub profile_type: ProfileType,
    #[serde(with = "crate::utils::serde_duration")]
    pub duration: Duration,
    pub sample_count: usize,
    pub top_functions: Vec<FunctionStats>,
    pub memory_hotspots: Vec<MemoryStats>,
    pub recommendations: Vec<String>,
}

/// 性能剖析器
pub struct Profiler {
    profile_type: ProfileType,
    is_running: Arc<RwLock<bool>>,
    cpu_samples: Arc<RwLock<Vec<CpuSample>>>,
    memory_samples: Arc<RwLock<Vec<MemorySample>>>,
    io_samples: Arc<RwLock<Vec<IoSample>>>,
    function_stats: Arc<RwLock<HashMap<String, FunctionStats>>>,
    start_time: Arc<RwLock<Option<Instant>>>,
}

impl Profiler {
    /// 创建新的性能剖析器
    pub fn new(profile_type: ProfileType) -> Self {
        Self {
            profile_type,
            is_running: Arc::new(RwLock::new(false)),
            cpu_samples: Arc::new(RwLock::new(Vec::new())),
            memory_samples: Arc::new(RwLock::new(Vec::new())),
            io_samples: Arc::new(RwLock::new(Vec::new())),
            function_stats: Arc::new(RwLock::new(HashMap::new())),
            start_time: Arc::new(RwLock::new(None)),
        }
    }

    /// 开始剖析
    pub async fn start(&self) -> Result<()> {
        let mut is_running = self.is_running.write().await;
        if *is_running {
            return Err(anyhow::anyhow!("Profiler is already running"));
        }

        *is_running = true;
        *self.start_time.write().await = Some(Instant::now());

        // 清空之前的数据
        self.cpu_samples.write().await.clear();
        self.memory_samples.write().await.clear();
        self.io_samples.write().await.clear();
        self.function_stats.write().await.clear();

        Ok(())
    }

    /// 停止剖析
    pub async fn stop(&self) -> Result<()> {
        let mut is_running = self.is_running.write().await;
        if !*is_running {
            return Err(anyhow::anyhow!("Profiler is not running"));
        }

        *is_running = false;
        Ok(())
    }

    /// 记录CPU采样
    pub async fn record_cpu_sample(&self, sample: CpuSample) -> Result<()> {
        let is_running = *self.is_running.read().await;
        if !is_running {
            return Ok(());
        }

        let mut samples = self.cpu_samples.write().await;
        samples.push(sample.clone());

        // 更新函数统计
        let mut stats = self.function_stats.write().await;
        let entry = stats
            .entry(sample.function_name.clone())
            .or_insert(FunctionStats {
                function_name: sample.function_name.clone(),
                call_count: 0,
                total_duration: Duration::ZERO,
                avg_duration: Duration::ZERO,
                min_duration: sample.duration,
                max_duration: sample.duration,
                self_time: Duration::ZERO,
            });

        entry.call_count += 1;
        entry.total_duration += sample.duration;
        entry.avg_duration = entry.total_duration / entry.call_count as u32;
        entry.min_duration = entry.min_duration.min(sample.duration);
        entry.max_duration = entry.max_duration.max(sample.duration);
        entry.self_time += sample.duration;

        Ok(())
    }

    /// 记录内存采样
    pub async fn record_memory_sample(&self, sample: MemorySample) -> Result<()> {
        let is_running = *self.is_running.read().await;
        if !is_running {
            return Ok(());
        }

        self.memory_samples.write().await.push(sample);
        Ok(())
    }

    /// 记录IO采样
    pub async fn record_io_sample(&self, sample: IoSample) -> Result<()> {
        let is_running = *self.is_running.read().await;
        if !is_running {
            return Ok(());
        }

        self.io_samples.write().await.push(sample);
        Ok(())
    }

    /// 生成剖析报告
    pub async fn generate_report(&self) -> Result<ProfileReport> {
        let start_time = self.start_time.read().await;
        let duration = start_time
            .map(|t| t.elapsed())
            .unwrap_or(Duration::ZERO);

        let sample_count = match self.profile_type {
            ProfileType::Cpu => self.cpu_samples.read().await.len(),
            ProfileType::Memory => self.memory_samples.read().await.len(),
            ProfileType::Io => self.io_samples.read().await.len(),
            ProfileType::LockContention => 0,
        };

        // 获取Top函数
        let stats = self.function_stats.read().await;
        let mut top_functions: Vec<FunctionStats> = stats.values().cloned().collect();
        top_functions.sort_by(|a, b| b.total_duration.cmp(&a.total_duration));
        top_functions.truncate(20); // Top 20

        // 生成建议
        let recommendations = self.generate_recommendations(&top_functions).await;

        // 内存热点分析
        let memory_hotspots = self.analyze_memory_hotspots().await?;

        Ok(ProfileReport {
            profile_type: self.profile_type,
            duration,
            sample_count,
            top_functions,
            memory_hotspots,
            recommendations,
        })
    }

    /// 分析内存热点
    async fn analyze_memory_hotspots(&self) -> Result<Vec<MemoryStats>> {
        let samples = self.memory_samples.read().await;
        let mut stats_map: HashMap<String, MemoryStats> = HashMap::new();

        for sample in samples.iter() {
            let entry = stats_map
                .entry(sample.location.clone())
                .or_insert(MemoryStats {
                    location: sample.location.clone(),
                    total_allocated: 0,
                    total_freed: 0,
                    current_usage: 0,
                    peak_usage: 0,
                    allocation_count: 0,
                });

            entry.total_allocated += sample.allocated_bytes;
            entry.total_freed += sample.freed_bytes;
            entry.current_usage = entry.total_allocated - entry.total_freed;
            entry.peak_usage = entry.peak_usage.max(entry.current_usage);
            entry.allocation_count += sample.total_allocations;
        }

        let mut hotspots: Vec<MemoryStats> = stats_map.into_values().collect();
        hotspots.sort_by(|a, b| b.peak_usage.cmp(&a.peak_usage));
        hotspots.truncate(10); // Top 10

        Ok(hotspots)
    }

    /// 生成优化建议
    async fn generate_recommendations(&self, top_functions: &[FunctionStats]) -> Vec<String> {
        let mut recommendations = Vec::new();

        // 检查是否有耗时过长的函数
        for func in top_functions.iter().take(5) {
            if func.avg_duration > Duration::from_millis(100) {
                recommendations.push(format!(
                    "函数 '{}' 平均耗时 {:?}，建议优化",
                    func.function_name, func.avg_duration
                ));
            }

            if func.call_count > 10000 {
                recommendations.push(format!(
                    "函数 '{}' 调用次数过多 ({}次)，考虑缓存或批处理",
                    func.function_name, func.call_count
                ));
            }
        }

        // 检查IO操作
        let io_samples = self.io_samples.read().await;
        let slow_io_count = io_samples
            .iter()
            .filter(|s| s.duration > Duration::from_millis(50))
            .count();

        if slow_io_count > 0 {
            recommendations.push(format!(
                "检测到 {} 次慢速IO操作 (>50ms)，建议优化IO策略或使用异步IO",
                slow_io_count
            ));
        }

        // 检查内存使用
        let memory_samples = self.memory_samples.read().await;
        let total_allocated: usize = memory_samples.iter().map(|s| s.allocated_bytes).sum();
        let total_freed: usize = memory_samples.iter().map(|s| s.freed_bytes).sum();

        if total_allocated > total_freed * 2 {
            recommendations.push(
                "检测到较高的内存分配率，考虑使用对象池或减少临时对象创建".to_string(),
            );
        }

        if recommendations.is_empty() {
            recommendations.push("性能表现良好，未发现明显瓶颈".to_string());
        }

        recommendations
    }

    /// 获取实时统计
    pub async fn get_realtime_stats(&self) -> Result<HashMap<String, f64>> {
        let mut stats = HashMap::new();

        let cpu_samples = self.cpu_samples.read().await;
        let memory_samples = self.memory_samples.read().await;
        let io_samples = self.io_samples.read().await;

        stats.insert("cpu_samples".to_string(), cpu_samples.len() as f64);
        stats.insert("memory_samples".to_string(), memory_samples.len() as f64);
        stats.insert("io_samples".to_string(), io_samples.len() as f64);

        if let Some(start) = *self.start_time.read().await {
            let elapsed = start.elapsed().as_secs_f64();
            stats.insert("elapsed_seconds".to_string(), elapsed);
            stats.insert(
                "cpu_samples_per_second".to_string(),
                cpu_samples.len() as f64 / elapsed,
            );
        }

        Ok(stats)
    }
}

// 注意：为了简化使用，建议用户直接调用 record_cpu_sample
// 而不是使用宏，因为宏的跨crate导出比较复杂

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_profiler_lifecycle() {
        let profiler = Profiler::new(ProfileType::Cpu);

        // 开始剖析
        assert!(profiler.start().await.is_ok());
        assert!(*profiler.is_running.read().await);

        // 不能重复开始
        assert!(profiler.start().await.is_err());

        // 停止剖析
        assert!(profiler.stop().await.is_ok());
        assert!(!*profiler.is_running.read().await);
    }

    #[tokio::test]
    async fn test_cpu_sampling() {
        let profiler = Profiler::new(ProfileType::Cpu);
        profiler.start().await.unwrap();

        // 记录CPU采样
        let sample = CpuSample {
            timestamp: Instant::now(),
            function_name: "test_function".to_string(),
            duration: Duration::from_millis(10),
            call_stack: vec!["main".to_string(), "test_function".to_string()],
        };

        profiler.record_cpu_sample(sample).await.unwrap();

        let samples = profiler.cpu_samples.read().await;
        assert_eq!(samples.len(), 1);
    }

    #[tokio::test]
    async fn test_memory_sampling() {
        let profiler = Profiler::new(ProfileType::Memory);
        profiler.start().await.unwrap();

        // 记录内存采样
        let sample = MemorySample {
            timestamp: Instant::now(),
            location: "test_location".to_string(),
            allocated_bytes: 1024,
            freed_bytes: 512,
            total_allocations: 10,
        };

        profiler.record_memory_sample(sample).await.unwrap();

        let samples = profiler.memory_samples.read().await;
        assert_eq!(samples.len(), 1);
    }

    #[tokio::test]
    async fn test_report_generation() {
        let profiler = Profiler::new(ProfileType::Cpu);
        profiler.start().await.unwrap();

        // 记录多个采样
        for i in 0..10 {
            let sample = CpuSample {
                timestamp: Instant::now(),
                function_name: format!("function_{}", i % 3),
                duration: Duration::from_millis(i * 10),
                call_stack: vec![format!("function_{}", i % 3)],
            };
            profiler.record_cpu_sample(sample).await.unwrap();
        }

        // 生成报告
        let report = profiler.generate_report().await.unwrap();
        assert_eq!(report.profile_type, ProfileType::Cpu);
        assert_eq!(report.sample_count, 10);
        assert!(!report.top_functions.is_empty());
    }

    #[tokio::test]
    async fn test_recommendations() {
        let profiler = Profiler::new(ProfileType::Cpu);
        profiler.start().await.unwrap();

        // 记录一个慢函数
        let sample = CpuSample {
            timestamp: Instant::now(),
            function_name: "slow_function".to_string(),
            duration: Duration::from_millis(200),
            call_stack: vec!["slow_function".to_string()],
        };
        profiler.record_cpu_sample(sample).await.unwrap();

        let report = profiler.generate_report().await.unwrap();
        assert!(!report.recommendations.is_empty());
    }
}

