//! Glommio 运行时抽象层
//! 
//! 本模块提供了 Glommio 高性能异步运行时的抽象接口，
//! 支持基于 io_uring 的高性能 I/O 操作。

#[cfg(all(feature = "glommio", target_os = "linux"))]
use glommio::prelude::*;
use std::future::Future;
use std::pin::Pin;
use std::time::Duration;

use crate::error::{Error, Result};

/// 运行时类型枚举
#[derive(Debug, Clone, Copy)]
pub enum RuntimeType {
    #[cfg(feature = "tokio")]
    Tokio,
    #[cfg(all(feature = "glommio", target_os = "linux"))]
    Glommio,
}

/// Glommio 运行时实现
#[cfg(all(feature = "glommio", target_os = "linux"))]
pub struct GlommioRuntime {
    executor: LocalExecutor,
}

#[cfg(all(feature = "glommio", target_os = "linux"))]
impl GlommioRuntime {
    /// 创建新的 Glommio 运行时
    pub fn new() -> Result<Self> {
        let executor = LocalExecutorBuilder::new()
            .spawn(|| async {})
            .map_err(|e| Error::Other(format!("Failed to create Glommio executor: {}", e)))?;
        
        Ok(Self { executor })
    }
    
    /// 创建带有自定义配置的运行时
    pub fn with_config<F>(config_fn: F) -> Result<Self>
    where
        F: FnOnce(&mut LocalExecutorBuilder) -> &mut LocalExecutorBuilder,
    {
        let mut builder = LocalExecutorBuilder::new();
        let builder = config_fn(&mut builder);
        
        let executor = builder
            .spawn(|| async {})
            .map_err(|e| Error::Other(format!("Failed to create Glommio executor: {}", e)))?;
        
        Ok(Self { executor })
    }
    
    /// 阻塞等待异步任务完成
    pub fn block_on<F, T>(&self, future: F) -> T
    where
        F: Future<Output = T>,
    {
        self.executor.run(future)
    }
    
    /// 生成一个新的异步任务
    pub fn spawn<F, T>(&self, future: F) -> glommio::task::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        glommio::task::spawn_local(future)
    }
    
    /// 异步睡眠
    pub fn sleep(&self, duration: Duration) -> Pin<Box<dyn Future<Output = ()> + Send>> {
        Box::pin(glommio::timer::sleep(duration))
    }
}

#[cfg(all(feature = "glommio", target_os = "linux"))]
impl Default for GlommioRuntime {
    fn default() -> Self {
        Self::new().expect("Failed to create default Glommio runtime")
    }
}

/// Tokio 运行时实现（用于对比）
#[cfg(feature = "tokio")]
pub struct TokioRuntime {
    handle: tokio::runtime::Handle,
}

#[cfg(feature = "tokio")]
impl TokioRuntime {
    /// 创建新的 Tokio 运行时
    pub fn new() -> Result<Self> {
        let rt = tokio::runtime::Runtime::new()
            .map_err(|e| Error::Other(format!("Failed to create Tokio runtime: {}", e)))?;
        
        Ok(Self {
            handle: rt.handle().clone(),
        })
    }
    
    /// 使用当前 Tokio 运行时
    pub fn current() -> Result<Self> {
        let handle = tokio::runtime::Handle::current();
        Ok(Self { handle })
    }
    
    /// 阻塞等待异步任务完成
    pub fn block_on<F, T>(&self, future: F) -> T
    where
        F: Future<Output = T>,
    {
        self.handle.block_on(future)
    }
    
    /// 生成一个新的异步任务
    pub fn spawn<F, T>(&self, future: F) -> tokio::task::JoinHandle<T>
    where
        F: Future<Output = T> + Send + 'static,
        T: Send + 'static,
    {
        self.handle.spawn(future)
    }
    
    /// 异步睡眠
    pub fn sleep(&self, duration: Duration) -> Pin<Box<dyn Future<Output = ()> + Send>> {
        Box::pin(tokio::time::sleep(duration))
    }
}

#[cfg(feature = "tokio")]
impl Default for TokioRuntime {
    fn default() -> Self {
        Self::current().expect("Failed to create default Tokio runtime")
    }
}

/// 运行时工厂
pub struct RuntimeFactory;

impl RuntimeFactory {
    /// 创建指定类型的运行时
    pub fn create(runtime_type: RuntimeType) -> Result<RuntimeBox> {
        #[cfg(feature = "tokio")]
        match runtime_type {
            RuntimeType::Tokio => {
                let runtime = TokioRuntime::new()?;
                Ok(RuntimeBox::Tokio(runtime))
            }
            #[cfg(all(feature = "glommio", target_os = "linux"))]
            RuntimeType::Glommio => {
                let runtime = GlommioRuntime::new()?;
                Ok(RuntimeBox::Glommio(runtime))
            }
        }
        
        #[cfg(not(feature = "tokio"))]
        {
            #[cfg(all(feature = "glommio", target_os = "linux"))]
            match runtime_type {
                RuntimeType::Glommio => {
                    let runtime = GlommioRuntime::new()?;
                    Ok(RuntimeBox::Glommio(runtime))
                }
            }
            
            #[cfg(not(all(feature = "glommio", target_os = "linux")))]
            {
                let _ = runtime_type; // 使用参数以避免未使用警告
                Err(Error::Other("Runtime not available on this platform".to_string()))
            }
        }
    }
    
    /// 根据系统环境自动选择最佳运行时
    pub fn create_optimal() -> Result<RuntimeBox> {
        // 检查是否支持 Glommio（需要 Linux 5.8+）
        #[cfg(all(feature = "glommio", target_os = "linux"))]
        {
            if Self::supports_glommio() {
                return Self::create(RuntimeType::Glommio);
            }
        }
        
        // 回退到 Tokio
        #[cfg(feature = "tokio")]
        {
            Self::create(RuntimeType::Tokio)
        }
        
        #[cfg(not(feature = "tokio"))]
        {
            Err(Error::Other("No async runtime available".to_string()))
        }
    }
    
    /// 检查系统是否支持 Glommio
    #[cfg(all(feature = "glommio", target_os = "linux"))]
    #[allow(dead_code)]
    fn supports_glommio() -> bool {
        // 简化的检查逻辑，实际应用中需要检查内核版本和 io_uring 支持
        true
    }
    
    #[cfg(not(all(feature = "glommio", target_os = "linux")))]
    #[allow(dead_code)]
    fn supports_glommio() -> bool {
        false
    }
}

/// 运行时盒子，用于统一不同运行时的接口
pub enum RuntimeBox {
    #[cfg(feature = "tokio")]
    Tokio(TokioRuntime),
    #[cfg(all(feature = "glommio", target_os = "linux"))]
    Glommio(GlommioRuntime),
}

impl RuntimeBox {
    /// 阻塞等待异步任务完成
    #[allow(dead_code)]
    #[allow(unused_variables)]
    pub fn block_on<F, T>(&self, future: F) -> T
    where
        F: Future<Output = T>,
    {
        match self {
            #[cfg(feature = "tokio")]
            RuntimeBox::Tokio(runtime) => runtime.block_on(future),
            #[cfg(all(feature = "glommio", target_os = "linux"))]
            RuntimeBox::Glommio(runtime) => runtime.block_on(future),
            #[cfg(not(any(feature = "tokio", all(feature = "glommio", target_os = "linux"))))]
            _ => panic!("No runtime available"),
        }
    }
    
    /// 异步睡眠
    #[allow(dead_code)]
    #[allow(unused_variables)]
    pub fn sleep(&self, duration: Duration) -> Pin<Box<dyn Future<Output = ()> + Send>> {
        match self {
            #[cfg(feature = "tokio")]
            RuntimeBox::Tokio(runtime) => runtime.sleep(duration),
            #[cfg(all(feature = "glommio", target_os = "linux"))]
            RuntimeBox::Glommio(runtime) => runtime.sleep(duration),
            #[cfg(not(any(feature = "tokio", all(feature = "glommio", target_os = "linux"))))]
            _ => panic!("No runtime available"),
        }
    }
}

/// 运行时性能基准测试
pub struct RuntimeBenchmarker;

impl RuntimeBenchmarker {
    /// 运行性能对比测试
    #[allow(dead_code)]
    #[allow(unused_variables)]
    #[allow(unused_mut)]
    pub async fn compare_runtimes<F, T>(
        _operation: F,
        _iterations: usize,
    ) -> Result<RuntimeComparison>
    where
        F: Fn() -> Pin<Box<dyn Future<Output = T> + Send>> + Clone + Send + Sync + 'static,
        T: Send + 'static,
    {
        let results = Vec::new();
        
        let mut results = results;
        
        #[cfg(feature = "tokio")]
        {
            let tokio_result = Self::benchmark_tokio(_operation.clone(), _iterations).await?;
            results.push(("tokio".to_string(), tokio_result));
        }
        
        #[cfg(all(feature = "glommio", target_os = "linux"))]
        {
            let glommio_result = Self::benchmark_glommio(_operation, _iterations).await?;
            results.push(("glommio".to_string(), glommio_result));
        }
        
        Ok(RuntimeComparison { results })
    }
    
    #[cfg(feature = "tokio")]
    #[allow(dead_code)]
    #[allow(unused_variables)]
    #[allow(unused_mut)]
    async fn benchmark_tokio<F, T>(
        operation: F,
        iterations: usize,
    ) -> Result<BenchmarkResult>
    where
        F: Fn() -> Pin<Box<dyn Future<Output = T> + Send>> + Send + Sync + 'static,
        T: Send + 'static,
    {
        let start = std::time::Instant::now();
        let mut handles = Vec::new();
        
        for _ in 0..iterations {
            let op = operation();
            let handle = tokio::spawn(async move { op.await });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.await.map_err(|e| Error::Other(format!("Tokio task failed: {}", e)))?;
        }
        
        let duration = start.elapsed();
        
        Ok(BenchmarkResult {
            duration,
            iterations,
            throughput: iterations as f64 / duration.as_secs_f64(),
        })
    }
    
    #[cfg(all(feature = "glommio", target_os = "linux"))]
    #[allow(dead_code)]
    #[allow(unused_variables)]
    #[allow(unused_mut)]
    async fn benchmark_glommio<F, T>(
        operation: F,
        iterations: usize,
    ) -> Result<BenchmarkResult>
    where
        F: Fn() -> Pin<Box<dyn Future<Output = T> + Send>> + Send + Sync + 'static,
        T: Send + 'static,
    {
        let start = std::time::Instant::now();
        let mut handles = Vec::new();
        
        for _ in 0..iterations {
            let op = operation();
            let handle = glommio::task::spawn_local(async move { op.await });
            handles.push(handle);
        }
        
        for handle in handles {
            handle.await.map_err(|e| Error::Other(format!("Glommio task failed: {}", e)))?;
        }
        
        let duration = start.elapsed();
        
        Ok(BenchmarkResult {
            duration,
            iterations,
            throughput: iterations as f64 / duration.as_secs_f64(),
        })
    }
}

/// 基准测试结果
#[derive(Debug, Clone)]
pub struct BenchmarkResult {
    pub duration: Duration,
    pub iterations: usize,
    pub throughput: f64,
}

/// 运行时对比结果
#[derive(Debug)]
pub struct RuntimeComparison {
    pub results: Vec<(String, BenchmarkResult)>,
}

impl RuntimeComparison {
    /// 获取最佳性能结果
    pub fn get_best(&self) -> Option<(&String, &BenchmarkResult)> {
        self.results
            .iter()
            .map(|(name, result)| (name, result))
            .max_by(|(_, a), (_, b)| a.throughput.partial_cmp(&b.throughput).unwrap())
    }
    
    /// 生成对比报告
    pub fn generate_report(&self) -> String {
        let mut report = String::new();
        report.push_str("# 运行时性能对比报告\n\n");
        
        for (name, result) in &self.results {
            report.push_str(&format!("## {}\n", name));
            report.push_str(&format!("- 持续时间: {:?}\n", result.duration));
            report.push_str(&format!("- 迭代次数: {}\n", result.iterations));
            report.push_str(&format!("- 吞吐量: {:.2} ops/sec\n\n", result.throughput));
        }
        
        if let Some((best_name, best_result)) = self.get_best() {
            report.push_str(&format!("## 最佳性能\n"));
            report.push_str(&format!("**{}** 表现最佳，吞吐量: {:.2} ops/sec\n", 
                                   best_name, best_result.throughput));
        }
        
        report
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;
    
    #[cfg(feature = "tokio")]
    #[tokio::test]
    async fn test_tokio_runtime() {
        let runtime = TokioRuntime::new().unwrap();
        
        let handle = runtime.spawn(async {
            tokio::time::sleep(Duration::from_millis(10)).await;
            42
        });
        
        let result = handle.await.unwrap();
        assert_eq!(result, 42);
    }
    
    #[cfg(all(feature = "glommio", target_os = "linux"))]
    #[test]
    fn test_glommio_runtime() {
        let runtime = GlommioRuntime::new().unwrap();
        
        let handle = runtime.spawn(async {
            glommio::timer::sleep(Duration::from_millis(10)).await;
            42
        });
        
        let result = runtime.block_on(handle).unwrap();
        assert_eq!(result, 42);
    }
    
    #[test]
    fn test_runtime_factory() {
        #[cfg(feature = "tokio")]
        {
            let runtime = RuntimeFactory::create(RuntimeType::Tokio).unwrap();
            assert!(runtime.block_on(async { 42 }) == 42);
        }
        
        #[cfg(all(feature = "glommio", target_os = "linux"))]
        {
            let runtime = RuntimeFactory::create(RuntimeType::Glommio).unwrap();
            assert!(runtime.block_on(async { 42 }) == 42);
        }
    }
    
    #[test]
    fn test_benchmark_result() {
        let result = BenchmarkResult {
            duration: Duration::from_secs(1),
            iterations: 1000,
            throughput: 1000.0,
        };
        
        assert_eq!(result.iterations, 1000);
        assert_eq!(result.throughput, 1000.0);
    }
}