/// 策略模式 (Strategy Pattern)
///
/// 定义一系列算法，把它们封装起来，并使它们可以相互替换
///
/// # 应用场景
///
/// - 负载均衡策略选择
/// - 重试策略配置
/// - 序列化/反序列化策略
/// - 缓存淘汰策略

use crate::prelude::*;
//use crate::error_handling::{ErrorContext, ErrorSeverity};
use std::sync::Arc;
use std::collections::HashMap;
use serde::{Serialize, Deserialize};

// Helper function to create validation errors  
fn validation_error(msg: impl Into<String>) -> anyhow::Error {
    anyhow::anyhow!(msg.into())
}

/// 策略 trait
#[async_trait::async_trait]
pub trait Strategy<Input, Output>: Send + Sync {
    /// 执行策略
    async fn execute(&self, input: Input) -> Result<Output>;
    
    /// 策略名称
    fn name(&self) -> &str;
    
    /// 策略描述
    fn description(&self) -> &str {
        "No description"
    }
}

/// 策略上下文
pub struct Context<Input, Output> {
    /// 当前策略
    strategy: Arc<dyn Strategy<Input, Output>>,
    /// 策略注册表
    strategies: HashMap<String, Arc<dyn Strategy<Input, Output>>>,
}

impl<Input, Output> Context<Input, Output>
where
    Input: Send + 'static,
    Output: Send + 'static,
{
    /// 创建新的上下文
    pub fn new(strategy: Arc<dyn Strategy<Input, Output>>) -> Self {
        let name = strategy.name().to_string();
        let mut strategies = HashMap::new();
        strategies.insert(name, strategy.clone());
        
        Self {
            strategy,
            strategies,
        }
    }
    
    /// 注册新策略
    pub fn register_strategy(&mut self, strategy: Arc<dyn Strategy<Input, Output>>) {
        let name = strategy.name().to_string();
        self.strategies.insert(name, strategy);
    }
    
    /// 切换策略
    pub fn set_strategy(&mut self, name: &str) -> Result<()> {
        let strategy = self.strategies.get(name)
            .ok_or_else(|| UnifiedError::not_found(format!("Strategy not found: {}", name)))?
            .clone();
        self.strategy = strategy;
        Ok(())
    }
    
    /// 获取当前策略名称
    pub fn current_strategy(&self) -> &str {
        self.strategy.name()
    }
    
    /// 列出所有可用策略
    pub fn list_strategies(&self) -> Vec<String> {
        self.strategies.keys().cloned().collect()
    }
    
    /// 执行当前策略
    pub async fn execute(&self, input: Input) -> Result<Output> {
        self.strategy.execute(input).await
    }
}

// ============================================================================
// 重试策略示例
// ============================================================================

/// 重试策略输入
#[derive(Debug, Clone)]
pub struct RetryInput {
    /// 已重试次数
    pub attempt: u32,
    /// 上次错误
    pub last_error: Option<String>,
}

/// 重试策略输出
#[derive(Debug, Clone)]
pub struct RetryDecision {
    /// 是否应该重试
    pub should_retry: bool,
    /// 等待时间（毫秒）
    pub wait_ms: u64,
}

/// 固定延迟重试策略
pub struct FixedDelayRetry {
    max_attempts: u32,
    delay_ms: u64,
}

impl FixedDelayRetry {
    pub fn new(max_attempts: u32, delay_ms: u64) -> Self {
        Self {
            max_attempts,
            delay_ms,
        }
    }
}

#[async_trait::async_trait]
impl Strategy<RetryInput, RetryDecision> for FixedDelayRetry {
    async fn execute(&self, input: RetryInput) -> Result<RetryDecision> {
        Ok(RetryDecision {
            should_retry: input.attempt < self.max_attempts,
            wait_ms: self.delay_ms,
        })
    }
    
    fn name(&self) -> &str {
        "fixed_delay"
    }
    
    fn description(&self) -> &str {
        "Fixed delay between retries"
    }
}

/// 指数退避重试策略
pub struct ExponentialBackoffRetry {
    max_attempts: u32,
    base_delay_ms: u64,
    max_delay_ms: u64,
}

impl ExponentialBackoffRetry {
    pub fn new(max_attempts: u32, base_delay_ms: u64, max_delay_ms: u64) -> Self {
        Self {
            max_attempts,
            base_delay_ms,
            max_delay_ms,
        }
    }
}

#[async_trait::async_trait]
impl Strategy<RetryInput, RetryDecision> for ExponentialBackoffRetry {
    async fn execute(&self, input: RetryInput) -> Result<RetryDecision> {
        if input.attempt >= self.max_attempts {
            return Ok(RetryDecision {
                should_retry: false,
                wait_ms: 0,
            });
        }
        
        let delay = self.base_delay_ms * 2u64.pow(input.attempt);
        let delay = delay.min(self.max_delay_ms);
        
        Ok(RetryDecision {
            should_retry: true,
            wait_ms: delay,
        })
    }
    
    fn name(&self) -> &str {
        "exponential_backoff"
    }
    
    fn description(&self) -> &str {
        "Exponential backoff with maximum delay"
    }
}

// ============================================================================
// 序列化策略示例
// ============================================================================

/// 序列化策略
#[async_trait::async_trait]
pub trait SerializationStrategy: Send + Sync {
    /// 序列化
    async fn serialize<T: Serialize + Send + Sync>(&self, value: &T) -> Result<Vec<u8>>;
    
    /// 反序列化
    async fn deserialize<T: for<'de> Deserialize<'de> + Send>(&self, data: &[u8]) -> Result<T>;
    
    /// 策略名称
    fn name(&self) -> &str;
}

/// JSON序列化策略
pub struct JsonSerialization;

#[async_trait::async_trait]
impl SerializationStrategy for JsonSerialization {
    async fn serialize<T: Serialize + Send + Sync>(&self, value: &T) -> Result<Vec<u8>> {
        serde_json::to_vec(value)
            .map_err(|e| validation_error(e.to_string()))
    }
    
    async fn deserialize<T: for<'de> Deserialize<'de> + Send>(&self, data: &[u8]) -> Result<T> {
        serde_json::from_slice(data)
            .map_err(|e| validation_error(e.to_string()))
    }
    
    fn name(&self) -> &str {
        "json"
    }
}

// NOTE: Bincode序列化需要添加bincode依赖，这里暂时注释掉
// /// Bincode序列化策略
// pub struct BincodeSerialization;

// ============================================================================
// 负载均衡策略（重用微服务模块的策略）
// ============================================================================

/// 选择策略输入
#[derive(Debug, Clone)]
pub struct SelectionInput<T> {
    /// 可选项列表
    pub options: Vec<T>,
}

/// 选择策略输出
#[derive(Debug, Clone)]
pub struct SelectionOutput<T> {
    /// 选中的项
    pub selected: Option<T>,
    /// 选中索引
    pub index: Option<usize>,
}

/// 轮询选择策略
pub struct RoundRobinSelection {
    counter: std::sync::atomic::AtomicUsize,
}

impl RoundRobinSelection {
    pub fn new() -> Self {
        Self {
            counter: std::sync::atomic::AtomicUsize::new(0),
        }
    }
}

impl Default for RoundRobinSelection {
    fn default() -> Self {
        Self::new()
    }
}

#[async_trait::async_trait]
impl<T: Clone + Send + Sync + 'static> Strategy<SelectionInput<T>, SelectionOutput<T>> for RoundRobinSelection {
    async fn execute(&self, input: SelectionInput<T>) -> Result<SelectionOutput<T>> {
        if input.options.is_empty() {
            return Ok(SelectionOutput {
                selected: None,
                index: None,
            });
        }
        
        let index = self.counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed) 
            % input.options.len();
        
        Ok(SelectionOutput {
            selected: Some(input.options[index].clone()),
            index: Some(index),
        })
    }
    
    fn name(&self) -> &str {
        "round_robin"
    }
    
    fn description(&self) -> &str {
        "Round-robin selection"
    }
}

/// 随机选择策略
pub struct RandomSelection;

#[async_trait::async_trait]
impl<T: Clone + Send + Sync + 'static> Strategy<SelectionInput<T>, SelectionOutput<T>> for RandomSelection {
    async fn execute(&self, input: SelectionInput<T>) -> Result<SelectionOutput<T>> {
        if input.options.is_empty() {
            return Ok(SelectionOutput {
                selected: None,
                index: None,
            });
        }
        
        use rand::Rng;
        let mut rng = rand::rng();
        let index = rng.random_range(0..input.options.len());
        
        Ok(SelectionOutput {
            selected: Some(input.options[index].clone()),
            index: Some(index),
        })
    }
    
    fn name(&self) -> &str {
        "random"
    }
    
    fn description(&self) -> &str {
        "Random selection"
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_retry_strategy() {
        let fixed = Arc::new(FixedDelayRetry::new(3, 1000));
        let exponential = Arc::new(ExponentialBackoffRetry::new(5, 100, 10000));
        
        let mut ctx = Context::new(fixed);
        ctx.register_strategy(exponential);
        
        // Test fixed delay
        let decision = ctx.execute(RetryInput {
            attempt: 0,
            last_error: None,
        }).await.unwrap();
        assert!(decision.should_retry);
        assert_eq!(decision.wait_ms, 1000);
        
        // Switch to exponential
        ctx.set_strategy("exponential_backoff").unwrap();
        let decision = ctx.execute(RetryInput {
            attempt: 2,
            last_error: None,
        }).await.unwrap();
        assert!(decision.should_retry);
        assert_eq!(decision.wait_ms, 400); // 100 * 2^2
    }
    
    #[tokio::test]
    async fn test_selection_strategy() {
        let options = vec!["a", "b", "c"];
        let input = SelectionInput { options: options.clone() };
        
        let rr = RoundRobinSelection::new();
        let output1 = rr.execute(input.clone()).await.unwrap();
        let output2 = rr.execute(input.clone()).await.unwrap();
        
        assert_ne!(output1.index, output2.index);
    }
}

