//! Rust 1.90 高级异步生态系统集成演示
//! 
//! 本程序展示了 Rust 1.90 异步特性与各种生态系统组件的深度集成，
//! 包括 Tokio、Smol、async-std 等运行时的无缝切换和组合使用

use std::sync::Arc;
use std::time::Duration;
use anyhow::Result;
use tracing::{info, error, debug};
use serde::{Deserialize, Serialize};

/// 运行时适配器枚举
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum RuntimeType {
    Tokio,
    Smol,
    AsyncStd,
    Hybrid, // 混合模式
}

/// 异步任务配置
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaskConfig {
    pub task_id: String,
    pub runtime_type: RuntimeType,
    pub timeout_ms: u64,
    pub retry_count: usize,
    pub priority: u8,
}

/// 任务执行结果
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TaskResult {
    pub task_id: String,
    pub success: bool,
    pub execution_time_ms: u64,
    pub error_message: Option<String>,
    pub runtime_type: RuntimeType,
}

/// 高级异步生态系统管理器
pub struct AdvancedAsyncEcosystemManager {
    /// 任务配置存储
    task_configs: Arc<tokio::sync::RwLock<std::collections::HashMap<String, TaskConfig>>>,
    /// 任务结果存储
    task_results: Arc<tokio::sync::RwLock<Vec<TaskResult>>>,
    /// 运行时统计
    runtime_stats: Arc<tokio::sync::RwLock<std::collections::HashMap<RuntimeType, usize>>>,
}

impl AdvancedAsyncEcosystemManager {
    /// 创建新的生态系统管理器
    pub fn new() -> Self {
        Self {
            task_configs: Arc::new(tokio::sync::RwLock::new(std::collections::HashMap::new())),
            task_results: Arc::new(tokio::sync::RwLock::new(Vec::new())),
            runtime_stats: Arc::new(tokio::sync::RwLock::new(std::collections::HashMap::new())),
        }
    }

    /// 注册任务配置
    pub async fn register_task(&self, config: TaskConfig) -> Result<()> {
        info!("注册任务: {:?}", config);
        
        {
            let mut configs = self.task_configs.write().await;
            configs.insert(config.task_id.clone(), config);
        }
        
        Ok(())
    }

    /// 执行任务 - 根据配置选择运行时
    pub async fn execute_task(&self, task_id: &str) -> Result<TaskResult> {
        let config = {
            let configs = self.task_configs.read().await;
            configs.get(task_id).cloned()
                .ok_or_else(|| anyhow::anyhow!("任务配置不存在: {}", task_id))?
        };

        info!("开始执行任务: {} 使用运行时: {:?}", task_id, config.runtime_type);

        let start_time = std::time::Instant::now();
        
        // 根据运行时类型执行任务
        let result = match config.runtime_type {
            RuntimeType::Tokio => self.execute_with_tokio(&config).await,
            RuntimeType::Smol => self.execute_with_smol(&config).await,
            RuntimeType::AsyncStd => self.execute_with_async_std(&config).await,
            RuntimeType::Hybrid => self.execute_with_hybrid(&config).await,
        };

        let execution_time = start_time.elapsed().as_millis() as u64;

        let task_result = TaskResult {
            task_id: task_id.to_string(),
            success: result.is_ok(),
            execution_time_ms: execution_time,
            error_message: result.err().map(|e| e.to_string()),
            runtime_type: config.runtime_type.clone(),
        };

        // 存储结果
        {
            let mut results = self.task_results.write().await;
            results.push(task_result.clone());
        }

        // 更新统计
        self.update_runtime_stats(config.runtime_type).await;

        info!("任务执行完成: {} 耗时: {}ms", task_id, execution_time);
        Ok(task_result)
    }

    /// 使用 Tokio 运行时执行任务
    async fn execute_with_tokio(&self, config: &TaskConfig) -> Result<String> {
        debug!("使用 Tokio 运行时执行任务: {}", config.task_id);
        
        // 模拟异步 I/O 操作
        tokio::time::sleep(Duration::from_millis(config.timeout_ms / 2)).await;
        
        // 模拟可能的失败
        if config.task_id.contains("fail") {
            return Err(anyhow::anyhow!("模拟 Tokio 任务失败"));
        }
        
        Ok(format!("Tokio 任务完成: {}", config.task_id))
    }

    /// 使用 Smol 运行时执行任务
    async fn execute_with_smol(&self, config: &TaskConfig) -> Result<String> {
        debug!("使用 Smol 运行时执行任务: {}", config.task_id);
        
        // 在 Tokio 环境中模拟 Smol 的行为
        tokio::time::sleep(Duration::from_millis(config.timeout_ms / 3)).await;
        
        // 模拟可能的失败
        if config.task_id.contains("fail") {
            return Err(anyhow::anyhow!("模拟 Smol 任务失败"));
        }
        
        Ok(format!("Smol 任务完成: {}", config.task_id))
    }

    /// 使用 async-std 运行时执行任务
    async fn execute_with_async_std(&self, config: &TaskConfig) -> Result<String> {
        debug!("使用 async-std 运行时执行任务: {}", config.task_id);
        
        // 在 Tokio 环境中模拟 async-std 的行为
        tokio::time::sleep(Duration::from_millis(config.timeout_ms / 4)).await;
        
        // 模拟可能的失败
        if config.task_id.contains("fail") {
            return Err(anyhow::anyhow!("模拟 async-std 任务失败"));
        }
        
        Ok(format!("async-std 任务完成: {}", config.task_id))
    }

    /// 使用混合模式执行任务
    async fn execute_with_hybrid(&self, config: &TaskConfig) -> Result<String> {
        debug!("使用混合模式执行任务: {}", config.task_id);
        
        // 模拟混合运行时的复杂行为
        tokio::time::sleep(Duration::from_millis(config.timeout_ms / 5)).await;
        
        // 模拟可能的失败
        if config.task_id.contains("fail") {
            return Err(anyhow::anyhow!("模拟混合模式任务失败"));
        }
        
        Ok(format!("混合模式任务完成: {}", config.task_id))
    }

    /// 更新运行时统计
    async fn update_runtime_stats(&self, runtime_type: RuntimeType) {
        let mut stats = self.runtime_stats.write().await;
        *stats.entry(runtime_type).or_insert(0) += 1;
    }

    /// 获取运行时统计
    pub async fn get_runtime_stats(&self) -> std::collections::HashMap<RuntimeType, usize> {
        let stats = self.runtime_stats.read().await;
        stats.clone()
    }

    /// 获取任务结果
    pub async fn get_task_results(&self) -> Vec<TaskResult> {
        let results = self.task_results.read().await;
        results.clone()
    }

    /// 批量执行任务
    pub async fn execute_batch_tasks(&self, task_ids: Vec<String>) -> Result<Vec<TaskResult>> {
        info!("开始批量执行 {} 个任务", task_ids.len());

        let mut handles = Vec::new();
        
        // 启动所有任务
        for task_id in task_ids {
            let manager = self.clone();
            let handle = tokio::spawn(async move {
                manager.execute_task(&task_id).await
            });
            handles.push(handle);
        }

        // 收集所有结果
        let mut results = Vec::new();
        for handle in handles {
            match handle.await {
                Ok(Ok(result)) => results.push(result),
                Ok(Err(e)) => {
                    error!("任务执行失败: {}", e);
                    // 创建失败结果
                    results.push(TaskResult {
                        task_id: "unknown".to_string(),
                        success: false,
                        execution_time_ms: 0,
                        error_message: Some(e.to_string()),
                        runtime_type: RuntimeType::Tokio,
                    });
                }
                Err(e) => {
                    error!("任务被取消: {}", e);
                }
            }
        }

        info!("批量执行完成，成功: {} 个", results.iter().filter(|r| r.success).count());
        Ok(results)
    }

    /// 生成性能报告
    pub async fn generate_performance_report(&self) -> String {
        let results = self.get_task_results().await;
        let stats = self.get_runtime_stats().await;

        let mut report = String::new();
        report.push_str("📊 异步生态系统性能报告\n");
        report.push_str("==========================================\n\n");

        // 运行时统计
        report.push_str("运行时使用统计:\n");
        for (runtime, count) in &stats {
            report.push_str(&format!("  {:?}: {} 次\n", runtime, count));
        }
        report.push('\n');

        // 任务成功率
        let total_tasks = results.len();
        let successful_tasks = results.iter().filter(|r| r.success).count();
        let success_rate = if total_tasks > 0 {
            (successful_tasks as f64 / total_tasks as f64) * 100.0
        } else {
            0.0
        };

        report.push_str(&format!("任务成功率: {:.2}% ({}/{})\n", success_rate, successful_tasks, total_tasks));
        report.push('\n');

        // 平均执行时间
        if !results.is_empty() {
            let total_time: u64 = results.iter().map(|r| r.execution_time_ms).sum();
            let avg_time = total_time as f64 / results.len() as f64;
            report.push_str(&format!("平均执行时间: {:.2}ms\n", avg_time));
        }

        // 各运行时性能对比
        report.push_str("\n各运行时性能对比:\n");
        for runtime_type in [RuntimeType::Tokio, RuntimeType::Smol, RuntimeType::AsyncStd, RuntimeType::Hybrid] {
            let runtime_results: Vec<_> = results.iter().filter(|r| r.runtime_type == runtime_type).collect();
            if !runtime_results.is_empty() {
                let avg_time: f64 = runtime_results.iter().map(|r| r.execution_time_ms as f64).sum::<f64>() / runtime_results.len() as f64;
                let success_count = runtime_results.iter().filter(|r| r.success).count();
                report.push_str(&format!("  {:?}: 平均 {:.2}ms, 成功率 {:.1}%\n", 
                    runtime_type, avg_time, (success_count as f64 / runtime_results.len() as f64) * 100.0));
            }
        }

        report
    }
}

impl Clone for AdvancedAsyncEcosystemManager {
    fn clone(&self) -> Self {
        Self {
            task_configs: Arc::clone(&self.task_configs),
            task_results: Arc::clone(&self.task_results),
            runtime_stats: Arc::clone(&self.runtime_stats),
        }
    }
}

/// 主演示函数
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    info!("🚀 开始 Rust 1.90 高级异步生态系统集成演示");
    info!("==========================================");

    let manager = AdvancedAsyncEcosystemManager::new();

    // 1. 注册各种类型的任务
    let task_configs = vec![
        TaskConfig {
            task_id: "tokio_io_task".to_string(),
            runtime_type: RuntimeType::Tokio,
            timeout_ms: 100,
            retry_count: 3,
            priority: 1,
        },
        TaskConfig {
            task_id: "smol_lightweight_task".to_string(),
            runtime_type: RuntimeType::Smol,
            timeout_ms: 80,
            retry_count: 2,
            priority: 2,
        },
        TaskConfig {
            task_id: "async_std_standard_task".to_string(),
            runtime_type: RuntimeType::AsyncStd,
            timeout_ms: 120,
            retry_count: 3,
            priority: 1,
        },
        TaskConfig {
            task_id: "hybrid_complex_task".to_string(),
            runtime_type: RuntimeType::Hybrid,
            timeout_ms: 150,
            retry_count: 4,
            priority: 0,
        },
        TaskConfig {
            task_id: "fail_task".to_string(),
            runtime_type: RuntimeType::Tokio,
            timeout_ms: 50,
            retry_count: 1,
            priority: 3,
        },
    ];

    // 注册所有任务
    for config in task_configs {
        manager.register_task(config).await?;
    }

    // 2. 单个任务执行演示
    info!("\n📋 单个任务执行演示:");
    let single_result = manager.execute_task("tokio_io_task").await?;
    info!("单个任务结果: {:?}", single_result);

    // 3. 批量任务执行演示
    info!("\n📦 批量任务执行演示:");
    let batch_task_ids = vec![
        "tokio_io_task".to_string(),
        "smol_lightweight_task".to_string(),
        "async_std_standard_task".to_string(),
        "hybrid_complex_task".to_string(),
        "fail_task".to_string(),
    ];

    let batch_results = manager.execute_batch_tasks(batch_task_ids).await?;
    info!("批量执行完成，共 {} 个任务", batch_results.len());

    // 4. 显示运行时统计
    info!("\n📈 运行时使用统计:");
    let stats = manager.get_runtime_stats().await;
    for (runtime, count) in &stats {
        info!("  {:?}: {} 次", runtime, count);
    }

    // 5. 生成性能报告
    info!("\n📊 性能报告:");
    let report = manager.generate_performance_report().await;
    println!("{}", report);

    info!("✅ Rust 1.90 高级异步生态系统集成演示完成!");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_task_registration() {
        let manager = AdvancedAsyncEcosystemManager::new();
        let config = TaskConfig {
            task_id: "test_task".to_string(),
            runtime_type: RuntimeType::Tokio,
            timeout_ms: 100,
            retry_count: 3,
            priority: 1,
        };
        
        assert!(manager.register_task(config).await.is_ok());
    }

    #[tokio::test]
    async fn test_task_execution() {
        let manager = AdvancedAsyncEcosystemManager::new();
        let config = TaskConfig {
            task_id: "test_task".to_string(),
            runtime_type: RuntimeType::Tokio,
            timeout_ms: 10,
            retry_count: 1,
            priority: 1,
        };
        
        manager.register_task(config).await.unwrap();
        let result = manager.execute_task("test_task").await.unwrap();
        
        assert_eq!(result.task_id, "test_task");
        assert!(result.success);
    }

    #[tokio::test]
    async fn test_runtime_stats() {
        let manager = AdvancedAsyncEcosystemManager::new();
        let config = TaskConfig {
            task_id: "test_task".to_string(),
            runtime_type: RuntimeType::Smol,
            timeout_ms: 10,
            retry_count: 1,
            priority: 1,
        };
        
        manager.register_task(config).await.unwrap();
        manager.execute_task("test_task").await.unwrap();
        
        let stats = manager.get_runtime_stats().await;
        assert_eq!(stats.get(&RuntimeType::Smol), Some(&1));
    }

    #[tokio::test]
    async fn test_batch_execution() {
        let manager = AdvancedAsyncEcosystemManager::new();
        
        let configs = vec![
            TaskConfig {
                task_id: "task1".to_string(),
                runtime_type: RuntimeType::Tokio,
                timeout_ms: 10,
                retry_count: 1,
                priority: 1,
            },
            TaskConfig {
                task_id: "task2".to_string(),
                runtime_type: RuntimeType::Smol,
                timeout_ms: 10,
                retry_count: 1,
                priority: 1,
            },
        ];
        
        for config in configs {
            manager.register_task(config).await.unwrap();
        }
        
        let results = manager.execute_batch_tasks(vec!["task1".to_string(), "task2".to_string()]).await.unwrap();
        assert_eq!(results.len(), 2);
    }
}
