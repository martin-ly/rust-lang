//! # 工作流系统示例 / Workflow System Examples
//!
//! 本模块提供了各种工作流系统的使用示例，展示不同模式和中间件的用法。
//! This module provides various usage examples for workflow systems, demonstrating the usage of different patterns and middleware.

pub mod advanced_examples;
pub mod basic_workflow;
pub mod middleware_examples;
pub mod pattern_examples;
pub mod rust189_examples;

// 重新导出示例 / Re-export examples
pub use advanced_examples::*;
pub use basic_workflow::*;
pub use middleware_examples::*;
pub use pattern_examples::*;
pub use rust189_examples::*;

/// 运行所有示例 / Run all examples
pub async fn run_all_examples() -> Result<(), Box<dyn std::error::Error>> {
    tracing::info!("开始运行工作流系统示例 / Starting workflow system examples");

    // 运行基础工作流示例 / Run basic workflow examples
    run_basic_workflow_examples().await?;

    // 运行 Rust 1.89 特性示例 / Run Rust 1.89 features examples
    #[cfg(feature = "rust189")]
    run_rust189_examples().await?;

    // 运行设计模式示例 / Run design pattern examples
    #[cfg(feature = "patterns")]
    run_pattern_examples().await?;

    // 运行中间件示例 / Run middleware examples
    #[cfg(feature = "middleware")]
    run_middleware_examples().await?;

    // 运行高级示例 / Run advanced examples
    run_advanced_examples().await?;

    tracing::info!("所有工作流系统示例运行完成 / All workflow system examples completed");
    Ok(())
}

/// 示例配置 / Example Configuration
#[derive(Debug, Clone)]
pub struct ExampleConfig {
    pub enable_rust189_features: bool,
    pub enable_patterns: bool,
    pub enable_middleware: bool,
    pub enable_monitoring: bool,
    pub max_concurrent_workflows: usize,
    pub timeout_seconds: u64,
}

impl Default for ExampleConfig {
    fn default() -> Self {
        Self {
            enable_rust189_features: true,
            enable_patterns: true,
            enable_middleware: true,
            enable_monitoring: true,
            max_concurrent_workflows: 10,
            timeout_seconds: 30,
        }
    }
}

/// 示例结果 / Example Result
#[derive(Debug, Clone)]
pub struct ExampleResult {
    pub example_name: String,
    pub success: bool,
    pub execution_time: std::time::Duration,
    pub message: String,
    pub data: serde_json::Value,
}

impl ExampleResult {
    /// 创建成功结果 / Create success result
    pub fn success(
        example_name: String,
        execution_time: std::time::Duration,
        data: serde_json::Value,
    ) -> Self {
        Self {
            example_name,
            success: true,
            execution_time,
            message: "示例执行成功 / Example executed successfully".to_string(),
            data,
        }
    }

    /// 创建失败结果 / Create failure result
    pub fn failure(
        example_name: String,
        execution_time: std::time::Duration,
        message: String,
    ) -> Self {
        Self {
            example_name,
            success: false,
            execution_time,
            message,
            data: serde_json::json!({}),
        }
    }
}

/// 示例运行器 / Example Runner
pub struct ExampleRunner {
    config: ExampleConfig,
    results: Vec<ExampleResult>,
}

impl ExampleRunner {
    /// 创建示例运行器 / Create example runner
    pub fn new(config: ExampleConfig) -> Self {
        Self {
            config,
            results: Vec::new(),
        }
    }

    /// 运行示例 / Run example
    pub async fn run_example<F, Fut>(&mut self, name: String, example_fn: F) -> Result<(), String>
    where
        F: FnOnce(&ExampleConfig) -> Fut,
        Fut: std::future::Future<Output = Result<serde_json::Value, String>>,
    {
        let start_time = std::time::Instant::now();

        match example_fn(&self.config).await {
            Ok(data) => {
                let execution_time = start_time.elapsed();
                let result = ExampleResult::success(name.clone(), execution_time, data);
                self.results.push(result);
                tracing::info!(
                    "示例 {} 执行成功 / Example {} executed successfully",
                    name,
                    name
                );
                Ok(())
            }
            Err(error) => {
                let execution_time = start_time.elapsed();
                let result = ExampleResult::failure(name.clone(), execution_time, error.clone());
                self.results.push(result);
                tracing::error!(
                    "示例 {} 执行失败 / Example {} execution failed: {}",
                    name,
                    name,
                    error
                );
                Err(error)
            }
        }
    }

    /// 获取所有结果 / Get all results
    pub fn get_results(&self) -> &[ExampleResult] {
        &self.results
    }

    /// 获取成功结果 / Get success results
    pub fn get_success_results(&self) -> Vec<&ExampleResult> {
        self.results.iter().filter(|r| r.success).collect()
    }

    /// 获取失败结果 / Get failure results
    pub fn get_failure_results(&self) -> Vec<&ExampleResult> {
        self.results.iter().filter(|r| !r.success).collect()
    }

    /// 生成报告 / Generate report
    pub fn generate_report(&self) -> String {
        let total = self.results.len();
        let successful = self.get_success_results().len();
        let failed = self.get_failure_results().len();

        let total_time: std::time::Duration = self.results.iter().map(|r| r.execution_time).sum();

        format!(
            "工作流系统示例报告 / Workflow System Examples Report\n\
            ===========================================\n\
            总示例数 / Total Examples: {}\n\
            成功示例 / Successful: {}\n\
            失败示例 / Failed: {}\n\
            总执行时间 / Total Execution Time: {}ms\n\
            平均执行时间 / Average Execution Time: {}ms\n\
            ===========================================",
            total,
            successful,
            failed,
            total_time.as_millis(),
            if total > 0 {
                total_time.as_millis() / total as u128
            } else {
                0
            }
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_example_runner() {
        let config = ExampleConfig::default();
        let mut runner = ExampleRunner::new(config);

        let result = runner
            .run_example("test_example".to_string(), |_config| async {
                Ok(serde_json::json!({"test": "data"}))
            })
            .await;

        assert!(result.is_ok());
        assert_eq!(runner.get_results().len(), 1);
        assert!(runner.get_results()[0].success);
    }

    #[test]
    fn test_example_result() {
        let result = ExampleResult::success(
            "test".to_string(),
            std::time::Duration::from_millis(100),
            serde_json::json!({"test": "data"}),
        );

        assert!(result.success);
        assert_eq!(result.example_name, "test");
        assert_eq!(
            result.message,
            "示例执行成功 / Example executed successfully"
        );
    }

    #[test]
    fn test_example_config() {
        let config = ExampleConfig::default();
        assert!(config.enable_rust189_features);
        assert!(config.enable_patterns);
        assert!(config.enable_middleware);
        assert_eq!(config.max_concurrent_workflows, 10);
    }
}
