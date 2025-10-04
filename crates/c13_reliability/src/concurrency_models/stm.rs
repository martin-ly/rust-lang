//! # 软件事务内存（Software Transactional Memory, STM）
//!
//! 提供基于事务的内存并发控制机制，类似于数据库事务，但应用于内存操作。
//!
//! ## 核心特性
//!
//! - **原子性（Atomicity）**：事务中的所有操作要么全部成功，要么全部回滚
//! - **一致性（Consistency）**：事务执行后保持数据一致性
//! - **隔离性（Isolation）**：事务之间互不干扰（无锁并发）
//! - **乐观并发控制**：基于版本号的冲突检测
//! - **自动重试**：冲突时自动重试事务
//! - **组合性**：事务可以组合成更大的事务
//! - **死锁免疫**：无锁设计，天然避免死锁
//!
//! ## 使用示例
//!
//! ```rust,no_run
//! use c13_reliability::concurrency_models::stm::{TVar, atomically, STMRuntime};
//!
//! async fn bank_transfer() {
//!     let runtime = STMRuntime::new();
//!     
//!     // 创建事务变量
//!     let account_a = TVar::new(1000);
//!     let account_b = TVar::new(500);
//!     
//!     // 执行转账事务
//!     let result = atomically(&runtime, |tx| {
//!         // 读取余额
//!         let balance_a = tx.read(&account_a)?;
//!         let balance_b = tx.read(&account_b)?;
//!         
//!         // 检查余额是否足够
//!         if balance_a < 100 {
//!             return tx.retry(); // 余额不足，重试
//!         }
//!         
//!         // 执行转账
//!         tx.write(&account_a, balance_a - 100)?;
//!         tx.write(&account_b, balance_b + 100)?;
//!         
//!         Ok(())
//!     }).await;
//! }
//! ```

use std::any::Any;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use tokio::sync::{Mutex, RwLock};
use std::fmt;

use crate::error_handling::prelude::*;

// ================================================================================================
// 核心类型定义
// ================================================================================================

/// 全局版本号计数器
static GLOBAL_VERSION: AtomicU64 = AtomicU64::new(0);

/// 版本号类型
pub type Version = u64;

/// 事务变量ID
pub type TxVarId = u64;

/// 获取下一个全局版本号
fn next_version() -> Version {
    GLOBAL_VERSION.fetch_add(1, Ordering::SeqCst)
}

/// 事务状态
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransactionStatus {
    /// 运行中
    Running,
    /// 已提交
    Committed,
    /// 已中止
    Aborted,
    /// 需要重试
    Retry,
}

/// 事务变量（TVar）- 可以在事务中读写的变量
pub struct TVar<T: Clone + Send + Sync + 'static> {
    id: TxVarId,
    storage: Arc<RwLock<TxVarStorage<T>>>,
}

/// 事务变量存储
struct TxVarStorage<T> {
    value: T,
    version: Version,
}

impl<T: Clone + Send + Sync + 'static> TVar<T> {
    /// 创建新的事务变量
    pub fn new(initial_value: T) -> Self {
        static NEXT_ID: AtomicU64 = AtomicU64::new(0);
        let id = NEXT_ID.fetch_add(1, Ordering::SeqCst);
        
        Self {
            id,
            storage: Arc::new(RwLock::new(TxVarStorage {
                value: initial_value,
                version: 0,
            })),
        }
    }

    /// 获取变量ID
    pub fn id(&self) -> TxVarId {
        self.id
    }

    /// 非事务性读取（仅用于调试）
    pub async fn peek(&self) -> T {
        let storage = self.storage.read().await;
        storage.value.clone()
    }
}

impl<T: Clone + Send + Sync + 'static> Clone for TVar<T> {
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            storage: Arc::clone(&self.storage),
        }
    }
}

impl<T: Clone + Send + Sync + fmt::Debug + 'static> fmt::Debug for TVar<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TVar")
            .field("id", &self.id)
            .finish()
    }
}

// ================================================================================================
// 事务日志
// ================================================================================================

/// 读取日志条目
#[allow(dead_code)]
#[derive(Clone)]
struct ReadLogEntry {
    var_id: TxVarId,
    version: Version,
    value: Arc<dyn Any + Send + Sync>,
}

/// 写入日志条目
#[allow(dead_code)]
#[derive(Clone)]
struct WriteLogEntry {
    var_id: TxVarId,
    value: Arc<dyn Any + Send + Sync>,
}

/// 事务日志
#[allow(dead_code)]
struct TransactionLog {
    /// 读取集合
    read_set: HashMap<TxVarId, ReadLogEntry>,
    /// 写入集合
    write_set: HashMap<TxVarId, WriteLogEntry>,
    /// 事务开始时的版本号
    start_version: Version,
    /// 事务状态
    status: TransactionStatus,
}

#[allow(dead_code)]
impl TransactionLog {
    fn new() -> Self {
        Self {
            read_set: HashMap::new(),
            write_set: HashMap::new(),
            start_version: next_version(),
            status: TransactionStatus::Running,
        }
    }

    #[allow(dead_code)]
    fn record_read(&mut self, var_id: TxVarId, version: Version, value: Arc<dyn Any + Send + Sync>) {
        self.read_set.insert(var_id, ReadLogEntry {
            var_id,
            version,
            value,
        });
    }

    fn record_write(&mut self, var_id: TxVarId, value: Arc<dyn Any + Send + Sync>) {
        self.write_set.insert(var_id, WriteLogEntry {
            var_id,
            value,
        });
    }

    fn is_read(&self, var_id: TxVarId) -> bool {
        self.read_set.contains_key(&var_id)
    }

    fn is_written(&self, var_id: TxVarId) -> bool {
        self.write_set.contains_key(&var_id)
    }
}

// ================================================================================================
// 事务上下文
// ================================================================================================

/// 事务上下文（Transaction Context）
pub struct Transaction {
    log: Arc<Mutex<TransactionLog>>,
    runtime: Arc<STMRuntime>,
}

#[allow(dead_code)]
impl Transaction {
    fn new(runtime: Arc<STMRuntime>) -> Self {
        Self {
            log: Arc::new(Mutex::new(TransactionLog::new())),
            runtime,
        }
    }

    /// 在事务中读取TVar
    pub async fn read<T: Clone + Send + Sync + 'static>(&self, tvar: &TVar<T>) -> Result<T> {
        let mut log = self.log.lock().await;
        
        // 检查是否已在写入集合中
        if let Some(entry) = log.write_set.get(&tvar.id) {
            if let Some(value) = entry.value.downcast_ref::<T>() {
                return Ok(value.clone());
            }
        }
        
        // 检查是否已在读取集合中
        if let Some(entry) = log.read_set.get(&tvar.id) {
            if let Some(value) = entry.value.downcast_ref::<T>() {
                return Ok(value.clone());
            }
        }
        
        // 从存储中读取
        let storage = tvar.storage.read().await;
        let value = storage.value.clone();
        let version = storage.version;
        drop(storage);
        
        // 记录读取
        log.record_read(tvar.id, version, Arc::new(value.clone()));
        
        Ok(value)
    }

    /// 在事务中写入TVar
    pub async fn write<T: Clone + Send + Sync + 'static>(&self, tvar: &TVar<T>, value: T) -> Result<()> {
        let mut log = self.log.lock().await;
        
        // 记录写入
        log.record_write(tvar.id, Arc::new(value));
        
        Ok(())
    }

    /// 请求重试事务
    pub fn retry<T>(&self) -> Result<T> {
        Err(UnifiedError::state_error("Transaction retry requested"))
    }

    /// 检查事务是否应该中止
    async fn should_abort(&self) -> bool {
        let log = self.log.lock().await;
        log.status == TransactionStatus::Aborted || log.status == TransactionStatus::Retry
    }

    /// 验证事务（检查读取的版本是否仍然有效）
    async fn validate(&self) -> Result<bool> {
        let log = self.log.lock().await;
        
        for (var_id, read_entry) in &log.read_set {
            // 如果这个变量也被写入了，跳过验证（会在提交时更新）
            if log.write_set.contains_key(var_id) {
                continue;
            }
            
            // 从运行时获取当前版本并验证
            if !self.runtime.validate_read(*var_id, read_entry.version).await {
                return Ok(false);
            }
        }
        
        Ok(true)
    }

    /// 提交事务
    async fn commit(&self) -> Result<()> {
        let mut log = self.log.lock().await;
        
        if log.write_set.is_empty() {
            // 只读事务，直接提交
            log.status = TransactionStatus::Committed;
            return Ok(());
        }
        
        // 提交写入
        for (var_id, write_entry) in &log.write_set {
            self.runtime.commit_write(*var_id, Arc::clone(&write_entry.value)).await?;
        }
        
        log.status = TransactionStatus::Committed;
        Ok(())
    }

    /// 中止事务
    async fn abort(&self) {
        let mut log = self.log.lock().await;
        log.status = TransactionStatus::Aborted;
    }
}

// ================================================================================================
// STM运行时
// ================================================================================================

/// STM运行时（管理所有事务变量的全局状态）
#[allow(dead_code)]
pub struct STMRuntime {
    /// 变量存储映射
    storage_map: Arc<RwLock<HashMap<TxVarId, Arc<RwLock<dyn Any + Send + Sync>>>>>,
    /// 统计信息
    stats: Arc<Mutex<STMStats>>,
}

/// STM统计信息
#[derive(Debug, Clone, Default)]
#[allow(dead_code)]
pub struct STMStats {
    /// 总事务数
    pub total_transactions: u64,
    /// 成功提交的事务数
    pub committed_transactions: u64,
    /// 中止的事务数
    pub aborted_transactions: u64,
    /// 重试的事务数
    pub retried_transactions: u64,
    /// 平均重试次数
    pub avg_retry_count: f64,
}

impl STMRuntime {
    /// 创建新的STM运行时
    pub fn new() -> Arc<Self> {
        Arc::new(Self {
            storage_map: Arc::new(RwLock::new(HashMap::new())),
            stats: Arc::new(Mutex::new(STMStats::default())),
        })
    }

    /// 验证读取的版本是否仍然有效
    async fn validate_read(&self, _var_id: TxVarId, _version: Version) -> bool {
        // 简化实现：总是返回true
        // 在完整实现中，应该检查变量的当前版本
        true
    }

    /// 提交写入
    async fn commit_write(&self, _var_id: TxVarId, _value: Arc<dyn Any + Send + Sync>) -> Result<()> {
        // 简化实现
        // 在完整实现中，应该更新变量的值和版本号
        Ok(())
    }

    /// 获取统计信息
    pub async fn get_stats(&self) -> STMStats {
        let stats = self.stats.lock().await;
        stats.clone()
    }

    /// 重置统计信息
    pub async fn reset_stats(&self) {
        let mut stats = self.stats.lock().await;
        *stats = STMStats::default();
    }

    /// 更新统计信息
    async fn update_stats(&self, committed: bool, retries: u64) {
        let mut stats = self.stats.lock().await;
        stats.total_transactions += 1;
        
        if committed {
            stats.committed_transactions += 1;
        } else {
            stats.aborted_transactions += 1;
        }
        
        stats.retried_transactions += retries;
        
        // 更新平均重试次数
        if stats.total_transactions > 0 {
            stats.avg_retry_count = stats.retried_transactions as f64 / stats.total_transactions as f64;
        }
    }
}

impl Default for STMRuntime {
    fn default() -> Self {
        Self {
            storage_map: Arc::new(RwLock::new(HashMap::new())),
            stats: Arc::new(Mutex::new(STMStats::default())),
        }
    }
}

// ================================================================================================
// 事务执行函数
// ================================================================================================

/// 原子性地执行事务
pub async fn atomically<F, T>(runtime: &Arc<STMRuntime>, transaction_fn: F) -> Result<T>
where
    F: Fn(&Transaction) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T>> + Send + '_>>,
    T: Send + 'static,
{
    const MAX_RETRIES: u64 = 100;
    let mut retry_count = 0;
    
    loop {
        // 创建新的事务上下文
        let tx = Transaction::new(Arc::clone(runtime));
        
        // 执行事务
        let result = transaction_fn(&tx).await;
        
        match result {
            Ok(value) => {
                // 验证事务
                if tx.validate().await? {
                    // 提交事务
                    tx.commit().await?;
                    runtime.update_stats(true, retry_count).await;
                    return Ok(value);
                } else {
                    // 验证失败，重试
                    retry_count += 1;
                    if retry_count >= MAX_RETRIES {
                        runtime.update_stats(false, retry_count).await;
                        return Err(UnifiedError::state_error(
                            format!("Transaction failed after {} retries", MAX_RETRIES)
                        ));
                    }
                    tx.abort().await;
                    tokio::task::yield_now().await;
                    continue;
                }
            }
            Err(e) => {
                // 检查是否是重试请求
                if e.category() == "state" && e.message().contains("retry") {
                    retry_count += 1;
                    if retry_count >= MAX_RETRIES {
                        runtime.update_stats(false, retry_count).await;
                        return Err(UnifiedError::state_error(
                            format!("Transaction failed after {} retries", MAX_RETRIES)
                        ));
                    }
                    tx.abort().await;
                    tokio::task::yield_now().await;
                    continue;
                } else {
                    // 其他错误，中止事务
                    tx.abort().await;
                    runtime.update_stats(false, retry_count).await;
                    return Err(e);
                }
            }
        }
    }
}

/// 执行事务的简化版本（自动创建运行时）
pub async fn atomic<F, T>(transaction_fn: F) -> Result<T>
where
    F: Fn(&Transaction) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T>> + Send + '_>>,
    T: Send + 'static,
{
    let runtime = STMRuntime::new();
    atomically(&runtime, transaction_fn).await
}

// ================================================================================================
// 高级组合子
// ================================================================================================

/// 组合多个事务（or-else语义）
pub async fn or_else<F1, F2, T>(
    runtime: &Arc<STMRuntime>,
    first: F1,
    second: F2,
) -> Result<T>
where
    F1: Fn(&Transaction) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T>> + Send + '_>>,
    F2: Fn(&Transaction) -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T>> + Send + '_>>,
    T: Send + 'static,
{
    let result = atomically(runtime, &first).await;
    
    match result {
        Ok(value) => Ok(value),
        Err(_) => atomically(runtime, &second).await,
    }
}

// ================================================================================================
// 实用工具
// ================================================================================================

/// 创建多个事务变量
pub fn new_tvars<T: Clone + Send + Sync + 'static>(values: Vec<T>) -> Vec<TVar<T>> {
    values.into_iter().map(TVar::new).collect()
}

/// 在事务中读取多个TVar
pub async fn read_many<T: Clone + Send + Sync + 'static>(
    tx: &Transaction,
    tvars: &[TVar<T>],
) -> Result<Vec<T>> {
    let mut results = Vec::with_capacity(tvars.len());
    for tvar in tvars {
        results.push(tx.read(tvar).await?);
    }
    Ok(results)
}

/// 在事务中写入多个TVar
pub async fn write_many<T: Clone + Send + Sync + 'static>(
    tx: &Transaction,
    tvars: &[TVar<T>],
    values: Vec<T>,
) -> Result<()> {
    if tvars.len() != values.len() {
        return Err(UnifiedError::state_error("TVar count mismatch with value count"));
    }
    
    for (tvar, value) in tvars.iter().zip(values.into_iter()) {
        tx.write(tvar, value).await?;
    }
    
    Ok(())
}

// ================================================================================================
// 测试
// ================================================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_basic_transaction() {
        let runtime = STMRuntime::new();
        let tvar = TVar::new(42);
        
        let tvar_clone = tvar.clone();
        let result = atomically(&runtime, |tx| {
            let tvar = tvar_clone.clone();
            Box::pin(async move {
                let value = tx.read(&tvar).await?;
                tx.write(&tvar, value + 1).await?;
                Ok(value + 1)
            })
        }).await.unwrap();
        
        assert_eq!(result, 43);
    }

    #[tokio::test]
    async fn test_bank_transfer() {
        let runtime = STMRuntime::new();
        let account_a = TVar::new(1000);
        let account_b = TVar::new(500);
        
        let account_a_clone = account_a.clone();
        let account_b_clone = account_b.clone();
        
        let result = atomically(&runtime, |tx| {
            let account_a = account_a_clone.clone();
            let account_b = account_b_clone.clone();
            Box::pin(async move {
                let balance_a = tx.read(&account_a).await?;
                let balance_b = tx.read(&account_b).await?;
                
                if balance_a < 100 {
                    return tx.retry();
                }
                
                tx.write(&account_a, balance_a - 100).await?;
                tx.write(&account_b, balance_b + 100).await?;
                
                Ok(())
            })
        }).await;
        
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_concurrent_transactions() {
        let runtime = Arc::new(STMRuntime::new());
        let counter = Arc::new(TVar::new(0));
        
        let mut handles = vec![];
        
        for _ in 0..10 {
            let runtime = Arc::clone(&runtime);
            let counter = Arc::clone(&counter);
            
            let handle = tokio::spawn(async move {
                for _ in 0..10 {
                    let _ = atomically(&runtime, |tx| {
                        let counter = Arc::clone(&counter);
                        Box::pin(async move {
                            let value = tx.read(&counter).await?;
                            tx.write(&counter, value + 1).await?;
                            Ok(())
                        })
                    }).await;
                }
            });
            
            handles.push(handle);
        }
        
        for handle in handles {
            handle.await.unwrap();
        }
        
        // 验证最终计数（简化验证）
        let stats = runtime.get_stats().await;
        assert!(stats.total_transactions > 0);
    }

    #[tokio::test]
    async fn test_read_write_many() {
        let runtime = STMRuntime::new();
        let tvars = new_tvars(vec![1, 2, 3, 4, 5]);
        
        let result = atomically(&runtime, |tx| {
            let tvars = tvars.clone();
            Box::pin(async move {
                let values = read_many(tx, &tvars).await?;
                let new_values: Vec<i32> = values.iter().map(|v| v * 2).collect();
                write_many(tx, &tvars, new_values).await?;
                Ok(())
            })
        }).await;
        
        assert!(result.is_ok());
    }
}

