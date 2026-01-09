//! Rust 1.90 异步特性综合演示程序 - 最终版本 (历史版本)
//!
//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features_demo.rs`
//! 
//! 本程序全面展示了Rust 1.90版本中异步编程的新特性和改进，
//! 结合Tokio、Smol等异步运行时库的最佳实践

use std::sync::Arc;
use std::time::Duration;
use tokio::time::sleep;
use tokio::sync::{Mutex, Semaphore, mpsc};
use std::collections::HashMap;
use anyhow::Result;
use tracing::{info, error, warn};

/// Rust 1.90 异步特性演示结构
pub struct Rust190AsyncDemo {
    /// 异步资源管理器
    resource_manager: Arc<Mutex<HashMap<String, String>>>,
    /// 并发控制器
    concurrency_controller: Arc<Semaphore>,
    /// 性能指标收集器
    metrics: Arc<Mutex<PerformanceMetrics>>,
}

#[derive(Debug, Clone)]
pub struct PerformanceMetrics {
    pub operations_completed: usize,
    pub average_latency_ms: f64,
    pub error_count: usize,
    pub throughput_ops_per_sec: f64,
}

impl Default for PerformanceMetrics {
    fn default() -> Self {
        Self {
            operations_completed: 0,
            average_latency_ms: 0.0,
            error_count: 0,
            throughput_ops_per_sec: 0.0,
        }
    }
}

impl Rust190AsyncDemo {
    /// 创建新的演示实例
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            resource_manager: Arc::new(Mutex::new(HashMap::new())),
            concurrency_controller: Arc::new(Semaphore::new(max_concurrent)),
            metrics: Arc::new(Mutex::new(PerformanceMetrics::default())),
        }
    }

    /// 演示 Rust 1.90 的异步资源管理
    pub async fn demonstrate_async_resource_management(&self) -> Result<()> {
        info!("🚀 演示 Rust 1.90 异步资源管理");

        // 1. 异步资源创建和管理
        let resource_id = "demo_resource_001".to_string();
        let resource_data = "重要业务数据".to_string();

        // 使用改进的借用检查器进行复杂操作
        let result = {
            let mut resources = self.resource_manager.lock().await;
            resources.insert(resource_id.clone(), resource_data.clone());
            
            // Polonius 借用检查器能够更好地理解这种模式
            let existing = resources.get(&resource_id).cloned();
            resources.insert(format!("{}_backup", resource_id), format!("backup_{}", resource_data));
            
            existing
        };

        if let Some(data) = result {
            info!("资源创建成功: {}", data);
        }

        // 2. 异步资源清理
        self.cleanup_resource(&resource_id).await?;

        Ok(())
    }

    /// 异步资源清理
    async fn cleanup_resource(&self, resource_id: &str) -> Result<()> {
        info!("开始清理资源: {}", resource_id);
        
        // 模拟异步清理过程
        sleep(Duration::from_millis(10)).await;
        
        {
            let mut resources = self.resource_manager.lock().await;
            resources.remove(resource_id);
        }
        
        info!("资源清理完成: {}", resource_id);
        Ok(())
    }

    /// 演示并发控制和背压管理
    pub async fn demonstrate_concurrency_control(&self, task_count: usize) -> Result<()> {
        info!("🔄 演示并发控制和背压管理");

        let (tx, mut rx) = mpsc::channel::<usize>(100); // 有界通道控制背压
        let demo = self.clone();

        // 启动生产者任务
        let producer = tokio::spawn(async move {
            for i in 0..task_count {
                if tx.send(i).await.is_err() {
                    warn!("生产者停止: 通道已关闭");
                    break;
                }
                sleep(Duration::from_millis(1)).await;
            }
        });

        // 启动消费者任务
        let consumer = tokio::spawn(async move {
            while let Some(task_id) = rx.recv().await {
                demo.process_task_with_limit(task_id).await;
            }
        });

        // 等待任务完成
        let (producer_result, consumer_result) = tokio::join!(producer, consumer);
        
        // 处理任务结果
        if let Err(e) = producer_result {
            error!("生产者任务失败: {}", e);
        }
        if let Err(e) = consumer_result {
            error!("消费者任务失败: {}", e);
        }

        // 更新性能指标
        self.update_metrics(task_count).await?;

        Ok(())
    }

    /// 使用信号量限制并发处理任务
    async fn process_task_with_limit(&self, task_id: usize) {
        let _permit = self.concurrency_controller.acquire().await.unwrap();
        
        let start = std::time::Instant::now();
        
        // 模拟异步任务处理
        sleep(Duration::from_millis(5)).await;
        
        let duration = start.elapsed();
        info!("任务 {} 完成，耗时: {:?}", task_id, duration);
    }

    /// 更新性能指标
    async fn update_metrics(&self, operations: usize) -> Result<()> {
        let mut metrics = self.metrics.lock().await;
        metrics.operations_completed += operations;
        metrics.throughput_ops_per_sec = metrics.operations_completed as f64 / 1.0; // 简化计算
        
        info!("性能指标更新: {:?}", *metrics);
        Ok(())
    }

    /// 演示错误处理和恢复
    pub async fn demonstrate_error_handling(&self) -> Result<()> {
        info!("⚠️ 演示错误处理和恢复");

        // 模拟可能失败的操作
        for i in 0..5 {
            match self.risky_operation(i).await {
                Ok(result) => {
                    info!("操作 {} 成功: {:?}", i, result);
                }
                Err(e) => {
                    warn!("操作 {} 失败: {}", i, e);
                    
                    // 实现重试逻辑
                    if let Ok(retry_result) = self.retry_operation(i).await {
                        info!("操作 {} 重试成功: {:?}", i, retry_result);
                    } else {
                        error!("操作 {} 重试失败", i);
                    }
                }
            }
        }

        Ok(())
    }

    /// 模拟可能失败的操作
    async fn risky_operation(&self, id: usize) -> Result<String> {
        sleep(Duration::from_millis(10)).await;
        
        // 模拟 30% 的失败率
        if id % 3 == 0 {
            Err(anyhow::anyhow!("模拟操作失败"))
        } else {
            Ok(format!("操作结果_{}", id))
        }
    }

    /// 重试操作
    async fn retry_operation(&self, id: usize) -> Result<String> {
        sleep(Duration::from_millis(5)).await;
        Ok(format!("重试结果_{}", id))
    }

    /// 演示结构化并发
    pub async fn demonstrate_structured_concurrency(&self) -> Result<()> {
        info!("🏗️ 演示结构化并发");

        use tokio::task::JoinSet;

        let mut join_set = JoinSet::new();

        // 添加多个并发任务
        for i in 0..10 {
            let demo = self.clone();
            join_set.spawn(async move {
                demo.concurrent_task(i).await
            });
        }

        // 统一收集结果
        let mut success_count = 0;
        let mut error_count = 0;

        while let Some(result) = join_set.join_next().await {
            match result? {
                Ok(_) => success_count += 1,
                Err(e) => {
                    error_count += 1;
                    error!("任务执行失败: {}", e);
                }
            }
        }

        info!("结构化并发完成 - 成功: {}, 失败: {}", success_count, error_count);
        Ok(())
    }

    /// 并发任务
    async fn concurrent_task(&self, task_id: usize) -> Result<()> {
        let start = std::time::Instant::now();
        
        // 模拟异步工作
        sleep(Duration::from_millis(20)).await;
        
        let duration = start.elapsed();
        info!("并发任务 {} 完成，耗时: {:?}", task_id, duration);
        
        Ok(())
    }

    /// 获取性能指标
    pub async fn get_metrics(&self) -> PerformanceMetrics {
        let metrics = self.metrics.lock().await;
        metrics.clone()
    }
}

impl Clone for Rust190AsyncDemo {
    fn clone(&self) -> Self {
        Self {
            resource_manager: Arc::clone(&self.resource_manager),
            concurrency_controller: Arc::clone(&self.concurrency_controller),
            metrics: Arc::clone(&self.metrics),
        }
    }
}

/// 主演示函数
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    info!("🚀 开始 Rust 1.90 异步特性综合演示");
    info!("==========================================");

    // 创建演示实例
    let demo = Rust190AsyncDemo::new(10); // 最大并发数: 10

    // 1. 异步资源管理演示
    demo.demonstrate_async_resource_management().await?;

    // 2. 并发控制和背压管理演示
    demo.demonstrate_concurrency_control(50).await?;

    // 3. 错误处理和恢复演示
    demo.demonstrate_error_handling().await?;

    // 4. 结构化并发演示
    demo.demonstrate_structured_concurrency().await?;

    // 5. 显示最终性能指标
    let final_metrics = demo.get_metrics().await;
    info!("📊 最终性能指标:");
    info!("  完成操作数: {}", final_metrics.operations_completed);
    info!("  平均延迟: {:.2}ms", final_metrics.average_latency_ms);
    info!("  错误数量: {}", final_metrics.error_count);
    info!("  吞吐量: {:.2} ops/sec", final_metrics.throughput_ops_per_sec);

    info!("✅ Rust 1.90 异步特性演示完成!");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_resource_management() {
        let demo = Rust190AsyncDemo::new(5);
        assert!(demo.demonstrate_async_resource_management().await.is_ok());
    }

    #[tokio::test]
    async fn test_concurrency_control() {
        let demo = Rust190AsyncDemo::new(3);
        assert!(demo.demonstrate_concurrency_control(10).await.is_ok());
    }

    #[tokio::test]
    async fn test_error_handling() {
        let demo = Rust190AsyncDemo::new(2);
        assert!(demo.demonstrate_error_handling().await.is_ok());
    }

    #[tokio::test]
    async fn test_structured_concurrency() {
        let demo = Rust190AsyncDemo::new(5);
        assert!(demo.demonstrate_structured_concurrency().await.is_ok());
    }

    #[tokio::test]
    async fn test_performance_metrics() {
        let demo = Rust190AsyncDemo::new(1);
        let metrics = demo.get_metrics().await;
        assert_eq!(metrics.operations_completed, 0);
        assert_eq!(metrics.error_count, 0);
    }
}
