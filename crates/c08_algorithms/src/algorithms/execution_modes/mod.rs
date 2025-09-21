//! # 算法执行模式
//! 
//! 本模块定义了算法的不同执行模式，充分利用 Rust 1.90 的特性：
//! - 同步执行：传统的单线程执行
//! - 异步执行：基于 tokio 的异步执行
//! - 并行执行：基于 rayon 的多线程并行执行
//! - 分布式执行：跨节点的分布式计算

pub mod sync;
pub mod async_exec;
pub mod parallel;
pub mod distributed;

// 重新导出执行器类型
pub use sync::SyncExecutor;
pub use async_exec::AsyncExecutor;
pub use parallel::ParallelExecutor;
pub use distributed::DistributedExecutor;

// 执行模式特征定义
use std::future::Future;
use std::pin::Pin;

/// 算法执行结果
#[derive(Debug, Clone)]
pub struct ExecutionResult<T> {
    pub result: T,
    pub execution_time: std::time::Duration,
    pub memory_usage: usize,
    pub thread_count: usize,
}

/// 同步算法特征
pub trait SyncAlgorithm<T, R> {
    fn execute(&self, input: T) -> Result<R, Box<dyn std::error::Error + Send + Sync>>;
}

/// 异步算法特征
pub trait AsyncAlgorithm<T, R>: Send + Sync {
    fn execute(
        &self,
        input: T,
    ) -> Pin<Box<dyn Future<Output = Result<R, Box<dyn std::error::Error + Send + Sync>>> + Send + '_>>;
}

/// 并行算法特征
pub trait ParallelAlgorithm<T, R> {
    fn execute(&self, input: T) -> Result<R, Box<dyn std::error::Error + Send + Sync>>;
    fn execute_with_threads(&self, input: T, thread_count: usize) -> Result<R, Box<dyn std::error::Error + Send + Sync>>;
}

/// 分布式算法特征
pub trait DistributedAlgorithm<T, R> {
    fn execute(&self, input: T, nodes: Vec<String>) -> Result<R, Box<dyn std::error::Error + Send + Sync>>;
}

/// 算法执行器
pub struct AlgorithmExecutor;

impl AlgorithmExecutor {
    /// 执行同步算法
    pub fn execute_sync<A, T, R>(algorithm: A, input: T) -> Result<ExecutionResult<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: SyncAlgorithm<T, R>,
        T: Clone,
    {
        let start = std::time::Instant::now();
        let result = algorithm.execute(input)?;
        let execution_time = start.elapsed();
        let memory_usage = std::mem::size_of_val(&result);
        
        Ok(ExecutionResult {
            result,
            execution_time,
            memory_usage,
            thread_count: 1,
        })
    }

    /// 执行异步算法
    pub async fn execute_async<A, T, R>(algorithm: A, input: T) -> Result<ExecutionResult<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: AsyncAlgorithm<T, R>,
        T: Send + 'static,
        R: Send + 'static,
    {
        let start = std::time::Instant::now();
        let result = algorithm.execute(input).await?;
        let execution_time = start.elapsed();
        let memory_usage = std::mem::size_of_val(&result);
        
        Ok(ExecutionResult {
            result,
            execution_time,
            memory_usage,
            thread_count: 1,
        })
    }

    /// 执行并行算法
    pub fn execute_parallel<A, T, R>(algorithm: A, input: T) -> Result<ExecutionResult<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: ParallelAlgorithm<T, R>,
        T: Clone,
    {
        let start = std::time::Instant::now();
        let result = algorithm.execute(input)?;
        let execution_time = start.elapsed();
        let memory_usage = std::mem::size_of_val(&result);
        
        Ok(ExecutionResult {
            result,
            execution_time,
            memory_usage,
            thread_count: num_cpus::get(),
        })
    }

    /// 执行分布式算法
    pub fn execute_distributed<A, T, R>(algorithm: A, input: T, nodes: Vec<String>) -> Result<ExecutionResult<R>, Box<dyn std::error::Error + Send + Sync>>
    where
        A: DistributedAlgorithm<T, R>,
        T: Clone,
    {
        let start = std::time::Instant::now();
        let result = algorithm.execute(input, nodes.clone())?;
        let execution_time = start.elapsed();
        let memory_usage = std::mem::size_of_val(&result);
        
        Ok(ExecutionResult {
            result,
            execution_time,
            memory_usage,
            thread_count: nodes.len(),
        })
    }
}
