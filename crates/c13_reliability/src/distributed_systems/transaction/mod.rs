//! # 分布式事务模块
//!
//! 提供多种分布式事务模式实现。

pub mod saga;
pub mod tcc;
pub mod two_phase_commit;
pub mod three_phase_commit;

pub use saga::*;
pub use tcc::*;
pub use two_phase_commit::*;
pub use three_phase_commit::*;

use async_trait::async_trait;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use crate::error_handling::UnifiedError;

/// 事务 ID
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TransactionId(pub String);

impl TransactionId {
    pub fn new() -> Self {
        Self(uuid::Uuid::new_v4().to_string())
    }
    
    pub fn from_string(id: String) -> Self {
        Self(id)
    }
}

/// 事务状态
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum TransactionState {
    /// 初始化
    Initialized,
    /// 准备中
    Preparing,
    /// 已准备
    Prepared,
    /// 提交中
    Committing,
    /// 已提交
    Committed,
    /// 中止中
    Aborting,
    /// 已中止
    Aborted,
    /// 补偿中 (Saga)
    Compensating,
    /// 已补偿 (Saga)
    Compensated,
    /// 失败
    Failed,
}

/// 分布式事务接口
#[async_trait]
pub trait DistributedTransaction: Send + Sync {
    /// 开始事务
    async fn begin(&mut self) -> Result<TransactionId, UnifiedError>;
    
    /// 提交事务
    async fn commit(&mut self, tx_id: &TransactionId) -> Result<(), UnifiedError>;
    
    /// 回滚事务
    async fn rollback(&mut self, tx_id: &TransactionId) -> Result<(), UnifiedError>;
    
    /// 获取事务状态
    fn get_state(&self, tx_id: &TransactionId) -> Option<TransactionState>;
    
    /// 获取所有事务
    fn list_transactions(&self) -> Vec<TransactionId>;
}

/// 事务参与者接口
#[async_trait]
pub trait TransactionParticipant: Send + Sync {
    /// 准备阶段
    async fn prepare(&mut self, tx_id: &TransactionId) -> Result<bool, UnifiedError>;
    
    /// 提交阶段
    async fn commit(&mut self, tx_id: &TransactionId) -> Result<(), UnifiedError>;
    
    /// 中止阶段
    async fn abort(&mut self, tx_id: &TransactionId) -> Result<(), UnifiedError>;
}

/// 事务步骤
#[async_trait]
pub trait TransactionStep: Send + Sync {
    /// 执行步骤
    async fn execute(&mut self, context: &TransactionContext) -> Result<StepResult, UnifiedError>;
    
    /// 补偿步骤 (仅 Saga)
    async fn compensate(&mut self, context: &TransactionContext) -> Result<(), UnifiedError>;
    
    /// 步骤名称
    fn name(&self) -> &str;
}

/// 事务上下文
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TransactionContext {
    /// 事务 ID
    pub tx_id: TransactionId,
    /// 事务数据
    pub data: HashMap<String, serde_json::Value>,
    /// 步骤历史
    pub step_history: Vec<StepExecution>,
}

/// 步骤执行记录
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StepExecution {
    /// 步骤名称
    pub step_name: String,
    /// 执行结果
    pub result: StepResult,
    /// 执行时间戳
    pub timestamp: chrono::DateTime<chrono::Utc>,
    /// 补偿状态
    pub compensated: bool,
}

/// 步骤结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StepResult {
    /// 成功
    Success {
        data: HashMap<String, serde_json::Value>,
    },
    /// 失败
    Failure {
        error: String,
        retryable: bool,
    },
}

/// 事务指标
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct TransactionMetrics {
    /// 总事务数
    pub total_transactions: u64,
    /// 成功事务数
    pub successful_transactions: u64,
    /// 失败事务数
    pub failed_transactions: u64,
    /// 平均持续时间 (毫秒)
    pub avg_duration_ms: f64,
    /// 活动事务数
    pub active_transactions: u64,
}

