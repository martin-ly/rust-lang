//! # Saga 事务模式实现
//!
//! Saga 是一种长事务管理模式，将事务分解为多个本地事务步骤，
//! 每个步骤都有对应的补偿操作。

use async_trait::async_trait;
use std::collections::HashMap;
use std::sync::Arc;
use parking_lot::RwLock;
use serde::{Deserialize, Serialize};
use chrono::Utc;

use crate::error_handling::{UnifiedError, ErrorSeverity, ErrorContext};
use super::{
    DistributedTransaction, TransactionId, TransactionState, TransactionStep,
    TransactionContext, StepExecution, StepResult, TransactionMetrics,
};

/// Saga 编排模式
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum SagaOrchestrationMode {
    /// 编排式 Saga - 中心化协调器
    Orchestration,
    /// 编舞式 Saga - 去中心化事件驱动
    Choreography,
}

/// Saga 配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SagaConfig {
    /// 编排模式
    pub orchestration_mode: SagaOrchestrationMode,
    /// 自动补偿
    pub auto_compensate: bool,
    /// 最大重试次数
    pub max_retries: u32,
    /// 并行执行
    pub parallel_execution: bool,
    /// 超时时间 (毫秒)
    pub timeout_ms: u64,
}

impl Default for SagaConfig {
    fn default() -> Self {
        Self {
            orchestration_mode: SagaOrchestrationMode::Orchestration,
            auto_compensate: true,
            max_retries: 3,
            parallel_execution: false,
            timeout_ms: 30000,
        }
    }
}

/// Saga 协调器
pub struct SagaCoordinator {
    /// 配置
    config: SagaConfig,
    /// 事务步骤
    steps: Vec<Box<dyn TransactionStep>>,
    /// 活动事务
    active_transactions: Arc<RwLock<HashMap<TransactionId, SagaTransaction>>>,
    /// 指标
    metrics: Arc<RwLock<TransactionMetrics>>,
}

/// Saga 事务
#[derive(Debug, Clone, Serialize, Deserialize)]
struct SagaTransaction {
    /// 事务 ID
    tx_id: TransactionId,
    /// 当前状态
    state: TransactionState,
    /// 上下文
    context: TransactionContext,
    /// 开始时间
    start_time: chrono::DateTime<Utc>,
    /// 结束时间
    end_time: Option<chrono::DateTime<Utc>>,
}

impl SagaCoordinator {
    /// 创建新的 Saga 协调器
    pub fn new(config: SagaConfig) -> Self {
        Self {
            config,
            steps: Vec::new(),
            active_transactions: Arc::new(RwLock::new(HashMap::new())),
            metrics: Arc::new(RwLock::new(TransactionMetrics::default())),
        }
    }
    
    /// 添加事务步骤
    pub fn add_step(&mut self, step: Box<dyn TransactionStep>) {
        self.steps.push(step);
    }
    
    /// 执行 Saga (编排式)
    async fn execute_orchestration(
        &mut self,
        tx_id: &TransactionId,
    ) -> Result<(), UnifiedError> {
        let mut context = {
            let transactions = self.active_transactions.read();
            transactions.get(tx_id)
                .map(|tx| tx.context.clone())
                .ok_or_else(|| UnifiedError::new(
                    "事务不存在",
                    ErrorSeverity::High,
                    "saga",
                    ErrorContext::new(
                        "saga", "execute_orchestration", file!(), line!(),
                        ErrorSeverity::High, "saga"
                    ),
                ))?
        };
        
        let mut executed_steps = 0;
        
        // 更新状态为提交中（在循环外）
        self.update_transaction_state(tx_id, TransactionState::Committing);
        
        // 顺序执行步骤
        for step in &mut self.steps {
            // 执行步骤
            match step.execute(&context).await {
                Ok(result) => {
                    // 记录步骤执行
                    context.step_history.push(StepExecution {
                        step_name: step.name().to_string(),
                        result: result.clone(),
                        timestamp: Utc::now(),
                        compensated: false,
                    });
                    
                    // 更新上下文数据
                    if let StepResult::Success { data } = result {
                        context.data.extend(data);
                    }
                    
                    executed_steps += 1;
                }
                Err(e) => {
                    // 步骤失败，需要补偿
                    if self.config.auto_compensate {
                        self.compensate_steps(&mut context, executed_steps).await?;
                    }
                    
                    self.update_transaction_state(tx_id, TransactionState::Failed);
                    return Err(e);
                }
            }
        }
        
        // 所有步骤执行成功
        self.update_transaction_state(tx_id, TransactionState::Committed);
        self.update_context(tx_id, context)?;
        
        Ok(())
    }
    
    /// 补偿已执行的步骤
    async fn compensate_steps(
        &mut self,
        context: &mut TransactionContext,
        executed_count: usize,
    ) -> Result<(), UnifiedError> {
        // 逆序补偿
        for i in (0..executed_count).rev() {
            if let Some(step) = self.steps.get_mut(i) {
                if let Err(e) = step.compensate(context).await {
                    tracing::error!(
                        "补偿步骤 {} 失败: {:?}",
                        step.name(),
                        e
                    );
                    // 继续补偿其他步骤
                }
                
                // 标记步骤为已补偿
                if let Some(execution) = context.step_history.get_mut(i) {
                    execution.compensated = true;
                }
            }
        }
        
        Ok(())
    }
    
    /// 更新事务状态
    fn update_transaction_state(&self, tx_id: &TransactionId, state: TransactionState) {
        let mut transactions = self.active_transactions.write();
        if let Some(tx) = transactions.get_mut(tx_id) {
            tx.state = state;
        }
    }
    
    /// 更新事务上下文
    fn update_context(
        &self,
        tx_id: &TransactionId,
        context: TransactionContext,
    ) -> Result<(), UnifiedError> {
        let mut transactions = self.active_transactions.write();
        transactions.get_mut(tx_id)
            .map(|tx| {
                tx.context = context;
            })
            .ok_or_else(|| UnifiedError::new(
                "事务不存在",
                ErrorSeverity::High,
                "saga",
                ErrorContext::new(
                    "saga", "update_context", file!(), line!(),
                    ErrorSeverity::High, "saga"
                ),
            ))
    }
    
    /// 获取指标
    pub fn metrics(&self) -> TransactionMetrics {
        self.metrics.read().clone()
    }
}

#[async_trait]
impl DistributedTransaction for SagaCoordinator {
    async fn begin(&mut self) -> Result<TransactionId, UnifiedError> {
        let tx_id = TransactionId::new();
        
        let context = TransactionContext {
            tx_id: tx_id.clone(),
            data: HashMap::new(),
            step_history: Vec::new(),
        };
        
        let transaction = SagaTransaction {
            tx_id: tx_id.clone(),
            state: TransactionState::Initialized,
            context,
            start_time: Utc::now(),
            end_time: None,
        };
        
        self.active_transactions.write().insert(tx_id.clone(), transaction);
        
        // 更新指标
        let mut metrics = self.metrics.write();
        metrics.total_transactions += 1;
        metrics.active_transactions += 1;
        
        Ok(tx_id)
    }
    
    async fn commit(&mut self, tx_id: &TransactionId) -> Result<(), UnifiedError> {
        // 执行 Saga
        match self.config.orchestration_mode {
            SagaOrchestrationMode::Orchestration => {
                self.execute_orchestration(tx_id).await?;
            }
            SagaOrchestrationMode::Choreography => {
                // TODO: 实现编舞式 Saga
                return Err(UnifiedError::new(
                    "编舞式 Saga 尚未实现",
                    ErrorSeverity::Medium,
                    "saga",
                    ErrorContext::new(
                        "saga", "commit", file!(), line!(),
                        ErrorSeverity::Medium, "saga"
                    ),
                ));
            }
        }
        
        // 更新指标
        let mut metrics = self.metrics.write();
        metrics.successful_transactions += 1;
        metrics.active_transactions -= 1;
        
        // 计算持续时间
        if let Some(tx) = self.active_transactions.read().get(tx_id) {
            let duration = Utc::now().signed_duration_since(tx.start_time);
            let duration_ms = duration.num_milliseconds() as f64;
            
            // 更新平均持续时间
            let total = metrics.successful_transactions + metrics.failed_transactions;
            metrics.avg_duration_ms = 
                (metrics.avg_duration_ms * (total - 1) as f64 + duration_ms) / total as f64;
        }
        
        Ok(())
    }
    
    async fn rollback(&mut self, tx_id: &TransactionId) -> Result<(), UnifiedError> {
        let mut context = {
            let transactions = self.active_transactions.read();
            transactions.get(tx_id)
                .map(|tx| tx.context.clone())
                .ok_or_else(|| UnifiedError::new(
                    "事务不存在",
                    ErrorSeverity::High,
                    "saga",
                    ErrorContext::new(
                        "saga", "rollback", file!(), line!(),
                        ErrorSeverity::High, "saga"
                    ),
                ))?
        };
        
        // 补偿所有已执行的步骤
        let executed_count = context.step_history.len();
        self.compensate_steps(&mut context, executed_count).await?;
        
        // 更新状态
        self.update_transaction_state(tx_id, TransactionState::Compensated);
        
        // 更新指标
        let mut metrics = self.metrics.write();
        metrics.failed_transactions += 1;
        metrics.active_transactions -= 1;
        
        Ok(())
    }
    
    fn get_state(&self, tx_id: &TransactionId) -> Option<TransactionState> {
        self.active_transactions.read()
            .get(tx_id)
            .map(|tx| tx.state.clone())
    }
    
    fn list_transactions(&self) -> Vec<TransactionId> {
        self.active_transactions.read()
            .keys()
            .cloned()
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    // 测试步骤实现
    struct TestStep {
        name: String,
        should_fail: bool,
    }
    
    #[async_trait]
    impl TransactionStep for TestStep {
        async fn execute(&mut self, _context: &TransactionContext) -> Result<StepResult, UnifiedError> {
            if self.should_fail {
                Err(UnifiedError::new(
                    "测试失败",
                    ErrorSeverity::Medium,
                    "test",
                    ErrorContext::new(
                        "test", "execute", file!(), line!(),
                        ErrorSeverity::Medium, "test"
                    ),
                ))
            } else {
                Ok(StepResult::Success {
                    data: HashMap::new(),
                })
            }
        }
        
        async fn compensate(&mut self, _context: &TransactionContext) -> Result<(), UnifiedError> {
            Ok(())
        }
        
        fn name(&self) -> &str {
            &self.name
        }
    }
    
    #[tokio::test]
    async fn test_saga_success() {
        let config = SagaConfig::default();
        let mut coordinator = SagaCoordinator::new(config);
        
        coordinator.add_step(Box::new(TestStep {
            name: "step1".to_string(),
            should_fail: false,
        }));
        
        coordinator.add_step(Box::new(TestStep {
            name: "step2".to_string(),
            should_fail: false,
        }));
        
        let tx_id = coordinator.begin().await.unwrap();
        let result = coordinator.commit(&tx_id).await;
        
        assert!(result.is_ok());
        assert_eq!(coordinator.get_state(&tx_id), Some(TransactionState::Committed));
    }
    
    #[tokio::test]
    async fn test_saga_compensation() {
        let config = SagaConfig::default();
        let mut coordinator = SagaCoordinator::new(config);
        
        coordinator.add_step(Box::new(TestStep {
            name: "step1".to_string(),
            should_fail: false,
        }));
        
        coordinator.add_step(Box::new(TestStep {
            name: "step2".to_string(),
            should_fail: true, // 这个步骤会失败
        }));
        
        let tx_id = coordinator.begin().await.unwrap();
        let result = coordinator.commit(&tx_id).await;
        
        assert!(result.is_err());
        // 应该触发自动补偿
    }
}

