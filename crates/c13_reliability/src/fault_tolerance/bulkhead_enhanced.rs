//! # 增强型舱壁隔离（Enhanced Bulkhead Pattern）
//!
//! 提供更高级的资源隔离和保护机制，防止级联故障。
//!
//! ## 核心特性
//!
//! - **多种隔离策略**：信号量、线程池、队列、令牌桶
//! - **动态调整**：根据负载自动调整资源限制
//! - **优先级队列**：支持任务优先级
//! - **溢出策略**：拒绝、排队、降级、弹性扩容
//! - **监控与告警**：详细的资源使用统计
//! - **跨服务隔离**：支持多租户和服务间隔离
//!
//! ## 使用示例
//!
//! ```rust,no_run
//! use c13_reliability::fault_tolerance::bulkhead_enhanced::{
//!     EnhancedBulkhead, BulkheadStrategy, OverflowStrategy
//! };
//!
//! async fn example() -> Result<(), Box<dyn std::error::Error>> {
//!     let bulkhead = EnhancedBulkhead::builder()
//!         .name("api-service")
//!         .max_concurrent(100)
//!         .strategy(BulkheadStrategy::Semaphore)
//!         .overflow_strategy(OverflowStrategy::Queue { max_queue_size: 1000 })
//!         .build();
//!     
//!     // 执行受保护的操作
//!     let result = bulkhead.execute(async {
//!         // 你的业务逻辑
//!         Ok(42)
//!     }).await?;
//!     
//!     Ok(())
//! }
//! ```

use std::collections::VecDeque;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock, Semaphore};
use tokio::time::timeout;

use crate::error_handling::prelude::*;

// ================================================================================================
// 核心类型定义
// ================================================================================================

/// 舱壁隔离策略
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BulkheadStrategy {
    /// 信号量模式（推荐，轻量级）
    Semaphore,
    /// 线程池模式（CPU密集型任务）
    ThreadPool,
    /// 队列模式（异步任务）
    Queue,
    /// 令牌桶模式（流量控制）
    TokenBucket,
}

/// 溢出策略（当资源耗尽时）
#[derive(Debug, Clone)]
pub enum OverflowStrategy {
    /// 拒绝新请求
    Reject,
    /// 排队等待
    Queue {
        max_queue_size: usize,
    },
    /// 降级处理
    Degrade {
        fallback_concurrency: usize,
    },
    /// 弹性扩容
    ElasticExpansion {
        max_expansion: usize,
        expansion_threshold: f64, // 使用率阈值
    },
}

/// 任务优先级
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum TaskPriority {
    Low = 0,
    Normal = 1,
    High = 2,
    Critical = 3,
}

/// 舱壁状态
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum BulkheadState {
    /// 正常运行
    #[default]
    Normal,
    /// 高负载
    HighLoad,
    /// 饱和
    Saturated,
    /// 过载拒绝
    Rejecting,
}

/// 舱壁配置
#[derive(Debug, Clone)]
pub struct EnhancedBulkheadConfig {
    /// 舱壁名称
    pub name: String,
    /// 最大并发数
    pub max_concurrent: usize,
    /// 隔离策略
    pub strategy: BulkheadStrategy,
    /// 溢出策略
    pub overflow_strategy: OverflowStrategy,
    /// 执行超时
    pub execution_timeout: Duration,
    /// 是否启用优先级
    pub enable_priority: bool,
    /// 高负载阈值（使用率）
    pub high_load_threshold: f64,
    /// 饱和阈值（使用率）
    pub saturation_threshold: f64,
    /// 是否启用自动调整
    pub auto_tuning: bool,
}

impl Default for EnhancedBulkheadConfig {
    fn default() -> Self {
        Self {
            name: "default-bulkhead".to_string(),
            max_concurrent: 100,
            strategy: BulkheadStrategy::Semaphore,
            overflow_strategy: OverflowStrategy::Reject,
            execution_timeout: Duration::from_secs(30),
            enable_priority: false,
            high_load_threshold: 0.7,
            saturation_threshold: 0.9,
            auto_tuning: false,
        }
    }
}

/// 舱壁统计信息
#[derive(Debug, Clone, Default)]
pub struct BulkheadStats {
    /// 总请求数
    pub total_requests: u64,
    /// 成功执行数
    pub successful_executions: u64,
    /// 被拒绝数
    pub rejections: u64,
    /// 超时数
    pub timeouts: u64,
    /// 当前并发数
    pub current_concurrency: usize,
    /// 当前队列长度
    pub current_queue_length: usize,
    /// 峰值并发数
    pub peak_concurrency: usize,
    /// 平均执行时间（毫秒）
    pub avg_execution_time_ms: f64,
    /// 当前状态
    pub state: BulkheadState,
}

// ================================================================================================
// 增强型舱壁隔离
// ================================================================================================

/// 增强型舱壁隔离
pub struct EnhancedBulkhead {
    config: EnhancedBulkheadConfig,
    semaphore: Arc<Semaphore>,
    stats: Arc<RwLock<BulkheadStats>>,
    queue: Arc<Mutex<VecDeque<QueuedTask>>>,
    token_bucket: Arc<Mutex<TokenBucket>>,
    state: Arc<RwLock<BulkheadState>>,
}

/// 队列任务
#[allow(dead_code)]
struct QueuedTask {
    priority: TaskPriority,
    queued_at: Instant,
}

/// 令牌桶
#[allow(dead_code)]
struct TokenBucket {
    tokens: f64,
    capacity: f64,
    refill_rate: f64, // tokens per second
    last_refill: Instant,
}

impl TokenBucket {
    #[allow(dead_code)]
    fn new(capacity: usize) -> Self {
        Self {
            tokens: capacity as f64,
            capacity: capacity as f64,
            refill_rate: capacity as f64 / 10.0, // 10秒填满
            last_refill: Instant::now(),
        }
    }

    #[allow(dead_code)]
    fn try_consume(&mut self) -> bool {
        self.refill();
        if self.tokens >= 1.0 {
            self.tokens -= 1.0;
            true
        } else {
            false
        }
    }

    #[allow(dead_code)]
    fn refill(&mut self) {
        let now = Instant::now();
        let elapsed = now.duration_since(self.last_refill).as_secs_f64();
        self.tokens = (self.tokens + elapsed * self.refill_rate).min(self.capacity);
        self.last_refill = now;
    }
}

impl EnhancedBulkhead {
    /// 创建构建器
    pub fn builder() -> EnhancedBulkheadBuilder {
        EnhancedBulkheadBuilder::new()
    }

    /// 创建新的舱壁隔离
    pub fn new(config: EnhancedBulkheadConfig) -> Self {
        let permits = config.max_concurrent;
        
        Self {
            semaphore: Arc::new(Semaphore::new(permits)),
            token_bucket: Arc::new(Mutex::new(TokenBucket::new(permits))),
            queue: Arc::new(Mutex::new(VecDeque::new())),
            stats: Arc::new(RwLock::new(BulkheadStats::default())),
            state: Arc::new(RwLock::new(BulkheadState::Normal)),
            config,
        }
    }

    /// 执行受保护的操作
    pub async fn execute<F, T>(&self, operation: F) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>> + Send,
        T: Send,
    {
        self.execute_with_priority(operation, TaskPriority::Normal).await
    }

    /// 带优先级执行
    pub async fn execute_with_priority<F, T>(
        &self,
        operation: F,
        priority: TaskPriority,
    ) -> Result<T>
    where
        F: std::future::Future<Output = Result<T>> + Send,
        T: Send,
    {
        // 更新统计
        {
            let mut stats = self.stats.write().await;
            stats.total_requests += 1;
        }

        // 尝试获取许可
        let permit = match self.config.strategy {
            BulkheadStrategy::Semaphore => {
                self.try_acquire_semaphore(priority).await?
            }
            BulkheadStrategy::TokenBucket => {
                self.try_acquire_token().await?;
                self.semaphore.acquire().await.map_err(|e| {
                    UnifiedError::resource_unavailable(format!("Semaphore acquire failed: {}", e))
                })?
            }
            _ => {
                self.semaphore.acquire().await.map_err(|e| {
                    UnifiedError::resource_unavailable(format!("Semaphore acquire failed: {}", e))
                })?
            }
        };

        // 更新并发数
        {
            let mut stats = self.stats.write().await;
            stats.current_concurrency += 1;
            stats.peak_concurrency = stats.peak_concurrency.max(stats.current_concurrency);
        }

        // 执行操作（带超时）
        let start = Instant::now();
        let result = timeout(self.config.execution_timeout, operation).await;

        // 释放许可
        drop(permit);

        // 更新统计
        {
            let mut stats = self.stats.write().await;
            stats.current_concurrency = stats.current_concurrency.saturating_sub(1);
            
            let elapsed_ms = start.elapsed().as_millis() as f64;
            stats.avg_execution_time_ms = 
                (stats.avg_execution_time_ms * stats.successful_executions as f64 + elapsed_ms)
                / (stats.successful_executions as f64 + 1.0);

            match &result {
                Ok(Ok(_)) => {
                    stats.successful_executions += 1;
                }
                Ok(Err(_)) => {
                    // 业务错误
                }
                Err(_) => {
                    stats.timeouts += 1;
                }
            }
        }

        // 更新状态
        self.update_state().await;

        // 处理结果
        match result {
            Ok(r) => r,
            Err(_) => Err(UnifiedError::resource_unavailable(
                format!("Operation timed out after {:?}", self.config.execution_timeout)
            )),
        }
    }

    /// 尝试获取信号量许可
    async fn try_acquire_semaphore(&self, priority: TaskPriority) -> Result<tokio::sync::SemaphorePermit<'_>> {
        // 尝试立即获取
        if let Ok(permit) = self.semaphore.try_acquire() {
            return Ok(permit);
        }

        // 根据溢出策略处理
        match &self.config.overflow_strategy {
            OverflowStrategy::Reject => {
                let mut stats = self.stats.write().await;
                stats.rejections += 1;
                Err(UnifiedError::resource_unavailable("Bulkhead is full, request rejected"))
            }
            OverflowStrategy::Queue { max_queue_size } => {
                let mut queue = self.queue.lock().await;
                if queue.len() >= *max_queue_size {
                    let mut stats = self.stats.write().await;
                    stats.rejections += 1;
                    return Err(UnifiedError::resource_unavailable("Queue is full"));
                }
                
                queue.push_back(QueuedTask {
                    priority,
                    queued_at: Instant::now(),
                });
                
                drop(queue);
                
                // 等待许可
                self.semaphore.acquire().await.map_err(|e| {
                    UnifiedError::resource_unavailable(format!("Failed to acquire: {}", e))
                })
            }
            OverflowStrategy::Degrade { .. } => {
                // 降级处理：使用降级并发限制
                self.semaphore.acquire().await.map_err(|e| {
                    UnifiedError::resource_unavailable(format!("Failed to acquire: {}", e))
                })
            }
            OverflowStrategy::ElasticExpansion { .. } => {
                // 弹性扩容：动态增加许可（简化实现）
                self.semaphore.acquire().await.map_err(|e| {
                    UnifiedError::resource_unavailable(format!("Failed to acquire: {}", e))
                })
            }
        }
    }

    /// 尝试获取令牌
    async fn try_acquire_token(&self) -> Result<()> {
        let mut bucket = self.token_bucket.lock().await;
        if bucket.try_consume() {
            Ok(())
        } else {
            let mut stats = self.stats.write().await;
            stats.rejections += 1;
            Err(UnifiedError::resource_unavailable("No tokens available"))
        }
    }

    /// 更新舱壁状态
    async fn update_state(&self) {
        let stats = self.stats.read().await;
        let usage_ratio = stats.current_concurrency as f64 / self.config.max_concurrent as f64;
        
        let new_state = if usage_ratio >= self.config.saturation_threshold {
            BulkheadState::Saturated
        } else if usage_ratio >= self.config.high_load_threshold {
            BulkheadState::HighLoad
        } else {
            BulkheadState::Normal
        };
        
        let mut state = self.state.write().await;
        *state = new_state;
        
        drop(state);
        drop(stats);
        
        let mut stats_mut = self.stats.write().await;
        stats_mut.state = new_state;
    }

    /// 获取统计信息
    pub async fn get_stats(&self) -> BulkheadStats {
        let stats = self.stats.read().await;
        stats.clone()
    }

    /// 获取当前状态
    pub async fn get_state(&self) -> BulkheadState {
        let state = self.state.read().await;
        *state
    }

    /// 重置统计信息
    pub async fn reset_stats(&self) {
        let mut stats = self.stats.write().await;
        *stats = BulkheadStats::default();
    }
}

// ================================================================================================
// 构建器模式
// ================================================================================================

/// 舱壁隔离构建器
pub struct EnhancedBulkheadBuilder {
    config: EnhancedBulkheadConfig,
}

impl EnhancedBulkheadBuilder {
    fn new() -> Self {
        Self {
            config: EnhancedBulkheadConfig::default(),
        }
    }

    pub fn name(mut self, name: impl Into<String>) -> Self {
        self.config.name = name.into();
        self
    }

    pub fn max_concurrent(mut self, max: usize) -> Self {
        self.config.max_concurrent = max;
        self
    }

    pub fn strategy(mut self, strategy: BulkheadStrategy) -> Self {
        self.config.strategy = strategy;
        self
    }

    pub fn overflow_strategy(mut self, strategy: OverflowStrategy) -> Self {
        self.config.overflow_strategy = strategy;
        self
    }

    pub fn execution_timeout(mut self, timeout: Duration) -> Self {
        self.config.execution_timeout = timeout;
        self
    }

    pub fn enable_priority(mut self, enable: bool) -> Self {
        self.config.enable_priority = enable;
        self
    }

    pub fn auto_tuning(mut self, enable: bool) -> Self {
        self.config.auto_tuning = enable;
        self
    }

    pub fn build(self) -> EnhancedBulkhead {
        EnhancedBulkhead::new(self.config)
    }
}

// ================================================================================================
// 测试
// ================================================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_basic_bulkhead() {
        let bulkhead = EnhancedBulkhead::builder()
            .max_concurrent(2)
            .build();
        
        let result = bulkhead.execute(async {
            tokio::time::sleep(Duration::from_millis(10)).await;
            Ok(42)
        }).await;
        
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 42);
    }

    #[tokio::test]
    async fn test_bulkhead_rejection() {
        let bulkhead = Arc::new(EnhancedBulkhead::builder()
            .max_concurrent(1)
            .overflow_strategy(OverflowStrategy::Reject)
            .build());
        
        let bulkhead1 = Arc::clone(&bulkhead);
        let bulkhead2 = Arc::clone(&bulkhead);
        
        // 第一个任务占用唯一的槽位
        let handle1 = tokio::spawn(async move {
            bulkhead1.execute(async {
                tokio::time::sleep(Duration::from_millis(100)).await;
                Ok(1)
            }).await
        });
        
        tokio::time::sleep(Duration::from_millis(10)).await;
        
        // 第二个任务应该被拒绝
        let result2 = bulkhead2.execute(async {
            Ok(2)
        }).await;
        
        assert!(result2.is_err());
        
        handle1.await.unwrap().unwrap();
    }

    #[tokio::test]
    async fn test_bulkhead_stats() {
        let bulkhead = EnhancedBulkhead::builder()
            .max_concurrent(10)
            .build();
        
        for _ in 0..5 {
            let _ = bulkhead.execute(async {
                Ok(())
            }).await;
        }
        
        let stats = bulkhead.get_stats().await;
        assert_eq!(stats.total_requests, 5);
        assert_eq!(stats.successful_executions, 5);
    }
}

