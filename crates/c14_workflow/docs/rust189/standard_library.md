# Rust 1.89 标准库增强在工作流系统中的应用

## 📋 概述

本文档详细介绍了 Rust 1.89 版本标准库的增强功能，以及如何在工作流系统中充分利用这些改进来提升代码质量、测试体验和开发效率。

## 🚀 核心标准库增强

### 1. 测试框架改进

Rust 1.89 对测试框架进行了多项改进，包括更好的错误提示、参数规范化和跨平台支持。

#### 改进的测试失败提示

```rust
#[cfg(test)]
mod workflow_tests {
    use super::*;
    use std::time::Duration;

    /// 测试工作流执行失败情况
    #[test]
    #[should_panic(expected = "Workflow execution failed")]
    fn test_workflow_execution_failure() {
        let mut engine = WorkflowEngine::new();
        let invalid_workflow = WorkflowDefinition {
            name: "invalid".to_string(),
            version: "1.0.0".to_string(),
            states: vec![],
            transitions: vec![],
            initial_state: "nonexistent".to_string(),
            final_states: vec![],
            metadata: std::collections::HashMap::new(),
        };
        
        // 这会触发 panic，新的错误提示更清晰
        engine.execute_workflow(invalid_workflow).unwrap();
    }

    /// 测试工作流超时处理
    #[test]
    #[should_panic(expected = "Workflow timeout exceeded")]
    fn test_workflow_timeout() {
        let mut engine = WorkflowEngine::new();
        let slow_workflow = create_slow_workflow();
        
        // 设置很短的超时时间
        engine.set_timeout(Duration::from_millis(1));
        engine.execute_workflow(slow_workflow).unwrap();
    }

    /// 测试并发工作流执行
    #[test]
    fn test_concurrent_workflow_execution() {
        let engine = Arc::new(WorkflowEngine::new());
        let mut handles = vec![];
        
        for i in 0..10 {
            let engine_clone = Arc::clone(&engine);
            let handle = std::thread::spawn(move || {
                let workflow = create_test_workflow(i);
                engine_clone.execute_workflow(workflow)
            });
            handles.push(handle);
        }
        
        // 等待所有工作流完成
        for handle in handles {
            let result = handle.join().unwrap();
            assert!(result.is_ok());
        }
    }

    /// 创建测试工作流
    fn create_test_workflow(id: usize) -> WorkflowDefinition {
        WorkflowDefinition {
            name: format!("test_workflow_{}", id),
            version: "1.0.0".to_string(),
            states: vec![
                WorkflowState {
                    name: "start".to_string(),
                    description: None,
                    is_final: false,
                    is_initial: true,
                    metadata: std::collections::HashMap::new(),
                },
                WorkflowState {
                    name: "end".to_string(),
                    description: None,
                    is_final: true,
                    is_initial: false,
                    metadata: std::collections::HashMap::new(),
                },
            ],
            transitions: vec![
                StateTransition {
                    from_state: "start".to_string(),
                    to_state: "end".to_string(),
                    condition: None,
                    action: None,
                    metadata: std::collections::HashMap::new(),
                },
            ],
            initial_state: "start".to_string(),
            final_states: vec!["end".to_string()],
            metadata: std::collections::HashMap::new(),
        }
    }

    /// 创建慢速工作流用于超时测试
    fn create_slow_workflow() -> WorkflowDefinition {
        let mut workflow = create_test_workflow(0);
        workflow.name = "slow_workflow".to_string();
        workflow
    }
}

/// 工作流引擎定义
pub struct WorkflowEngine {
    timeout: Duration,
}

impl WorkflowEngine {
    pub fn new() -> Self {
        Self {
            timeout: Duration::from_secs(30),
        }
    }

    pub fn set_timeout(&mut self, timeout: Duration) {
        self.timeout = timeout;
    }

    pub fn execute_workflow(&self, workflow: WorkflowDefinition) -> Result<(), WorkflowError> {
        // 验证工作流定义
        workflow.validate()?;
        
        // 模拟工作流执行
        std::thread::sleep(Duration::from_millis(100));
        
        // 检查超时
        if self.timeout < Duration::from_millis(50) {
            return Err(WorkflowError::Timeout);
        }
        
        Ok(())
    }
}

#[derive(Debug, thiserror::Error)]
pub enum WorkflowError {
    #[error("Workflow execution failed")]
    ExecutionFailed,
    #[error("Workflow timeout exceeded")]
    Timeout,
    #[error("Invalid workflow definition")]
    InvalidDefinition,
}
```

#### 测试参数规范化

```rust
#[cfg(test)]
mod parameter_normalization_tests {
    use super::*;

    /// 使用新的 --no-capture 参数（替代 --nocapture）
    #[test]
    fn test_workflow_output_capture() {
        let engine = WorkflowEngine::new();
        let workflow = create_verbose_workflow();
        
        // 这个测试会输出大量信息
        // 使用 cargo test --no-capture 来查看输出
        println!("开始执行工作流: {}", workflow.name);
        
        let result = engine.execute_workflow(workflow);
        
        println!("工作流执行结果: {:?}", result);
        assert!(result.is_ok());
    }

    /// 测试工作流性能指标
    #[test]
    fn test_workflow_performance_metrics() {
        let engine = WorkflowEngine::new();
        let workflow = create_performance_test_workflow();
        
        let start_time = std::time::Instant::now();
        let result = engine.execute_workflow(workflow);
        let duration = start_time.elapsed();
        
        println!("工作流执行时间: {:?}", duration);
        println!("执行结果: {:?}", result);
        
        assert!(result.is_ok());
        assert!(duration < Duration::from_secs(1));
    }

    fn create_verbose_workflow() -> WorkflowDefinition {
        // 创建会产生大量输出的工作流
        create_test_workflow(0)
    }

    fn create_performance_test_workflow() -> WorkflowDefinition {
        // 创建性能测试工作流
        create_test_workflow(0)
    }
}
```

### 2. 数组生成函数调用顺序保证

Rust 1.89 明确保证了 `std::array::from_fn` 的调用顺序，这对于依赖状态的闭包非常重要。

#### 在工作流系统中的应用

```rust
use std::collections::HashMap;

/// 使用数组生成函数创建工作流步骤
pub struct WorkflowStepGenerator;

impl WorkflowStepGenerator {
    /// 创建顺序依赖的工作流步骤
    pub fn create_sequential_workflow_steps<const N: usize>() -> [WorkflowStep; N] {
        std::array::from_fn(|i| {
            // 编译器保证 i 按递增顺序调用
            // 这对于依赖前一步骤状态的场景很重要
            WorkflowStep {
                id: format!("step_{}", i),
                name: format!("Step {}", i + 1),
                dependencies: if i > 0 {
                    vec![format!("step_{}", i - 1)]
                } else {
                    vec![]
                },
                status: StepStatus::Pending,
                execution_order: i,
                metadata: HashMap::new(),
            }
        })
    }

    /// 创建并行工作流步骤
    pub fn create_parallel_workflow_steps<const N: usize>() -> [WorkflowStep; N] {
        std::array::from_fn(|i| {
            // 所有步骤都没有依赖，可以并行执行
            WorkflowStep {
                id: format!("parallel_step_{}", i),
                name: format!("Parallel Step {}", i + 1),
                dependencies: vec![],
                status: StepStatus::Pending,
                execution_order: i,
                metadata: HashMap::new(),
            }
        })
    }

    /// 创建分层工作流步骤
    pub fn create_layered_workflow_steps<const LAYERS: usize, const STEPS_PER_LAYER: usize>() 
        -> [[WorkflowStep; STEPS_PER_LAYER]; LAYERS] 
    {
        std::array::from_fn(|layer| {
            std::array::from_fn(|step| {
                let global_step_id = layer * STEPS_PER_LAYER + step;
                let dependencies = if layer > 0 {
                    // 当前层的步骤依赖于前一层的所有步骤
                    (0..STEPS_PER_LAYER)
                        .map(|prev_step| format!("step_{}", (layer - 1) * STEPS_PER_LAYER + prev_step))
                        .collect()
                } else {
                    vec![]
                };

                WorkflowStep {
                    id: format!("step_{}", global_step_id),
                    name: format!("Layer {} Step {}", layer + 1, step + 1),
                    dependencies,
                    status: StepStatus::Pending,
                    execution_order: global_step_id,
                    metadata: HashMap::new(),
                }
            })
        })
    }

    /// 创建状态依赖的工作流步骤
    pub fn create_state_dependent_steps<const N: usize>(
        initial_state: &WorkflowState
    ) -> [WorkflowStep; N] {
        let mut current_state = initial_state.clone();
        
        std::array::from_fn(|i| {
            // 每个步骤都基于前一个步骤的状态
            let step = WorkflowStep {
                id: format!("state_dependent_step_{}", i),
                name: format!("State Dependent Step {}", i + 1),
                dependencies: if i > 0 {
                    vec![format!("state_dependent_step_{}", i - 1)]
                } else {
                    vec![]
                },
                status: StepStatus::Pending,
                execution_order: i,
                metadata: {
                    let mut meta = HashMap::new();
                    meta.insert("previous_state".to_string(), 
                        serde_json::Value::String(current_state.name.clone()));
                    meta.insert("state_transition_count".to_string(), 
                        serde_json::Value::Number(serde_json::Number::from(i)));
                    meta
                },
            };

            // 更新状态为下一步准备
            current_state.name = format!("state_after_step_{}", i);
            step
        })
    }
}

/// 工作流步骤定义
#[derive(Debug, Clone)]
pub struct WorkflowStep {
    pub id: String,
    pub name: String,
    pub dependencies: Vec<String>,
    pub status: StepStatus,
    pub execution_order: usize,
    pub metadata: HashMap<String, serde_json::Value>,
}

#[derive(Debug, Clone)]
pub enum StepStatus {
    Pending,
    Ready,
    Running,
    Completed,
    Failed,
}

/// 工作流状态定义
#[derive(Debug, Clone)]
pub struct WorkflowState {
    pub name: String,
    pub description: Option<String>,
    pub is_final: bool,
    pub is_initial: bool,
    pub metadata: HashMap<String, serde_json::Value>,
}

impl Default for WorkflowState {
    fn default() -> Self {
        Self {
            name: "default".to_string(),
            description: None,
            is_final: false,
            is_initial: true,
            metadata: HashMap::new(),
        }
    }
}
```

### 3. 浮点数 NaN 表现形式标准化

Rust 1.89 确保标准浮点类型中的 NaN 为 Quiet NaN，符合 IEEE 标准。

#### 在工作流数值计算中的应用

```rust
use std::f64;

/// 工作流数值计算器，使用标准化的 NaN 处理
pub struct WorkflowNumericalCalculator;

impl WorkflowNumericalCalculator {
    /// 计算工作流执行时间统计
    pub fn calculate_execution_statistics(
        &self, 
        execution_times: &[f64]
    ) -> ExecutionStatistics {
        let mut times = execution_times.to_vec();
        
        // 过滤掉 NaN 值
        times.retain(|&time| !time.is_nan());
        
        if times.is_empty() {
            return ExecutionStatistics::default();
        }

        let count = times.len() as f64;
        let sum: f64 = times.iter().sum();
        let mean = sum / count;

        // 计算方差
        let variance: f64 = times.iter()
            .map(|&time| (time - mean).powi(2))
            .sum::<f64>() / count;

        let std_dev = variance.sqrt();

        // 排序以计算中位数和百分位数
        times.sort_by(|a, b| a.partial_cmp(b).unwrap());

        let median = if times.len() % 2 == 0 {
            let mid = times.len() / 2;
            (times[mid - 1] + times[mid]) / 2.0
        } else {
            times[times.len() / 2]
        };

        ExecutionStatistics {
            count: times.len(),
            mean,
            median,
            std_dev,
            min: times[0],
            max: times[times.len() - 1],
            p95: self.calculate_percentile(&times, 0.95),
            p99: self.calculate_percentile(&times, 0.99),
        }
    }

    /// 计算百分位数
    fn calculate_percentile(&self, sorted_times: &[f64], percentile: f64) -> f64 {
        if sorted_times.is_empty() {
            return f64::NAN;
        }

        let index = (percentile * (sorted_times.len() - 1) as f64).round() as usize;
        sorted_times[index.min(sorted_times.len() - 1)]
    }

    /// 验证数值计算的正确性
    pub fn validate_calculation(&self, value: f64) -> bool {
        // 检查是否为 Quiet NaN（符合 IEEE 标准）
        if value.is_nan() {
            // 在 Rust 1.89 中，NaN 保证为 Quiet NaN
            return true;
        }

        // 检查是否为有限数
        if !value.is_finite() {
            return false;
        }

        // 检查是否在合理范围内
        value >= 0.0 && value <= 1e6
    }

    /// 计算工作流性能指标
    pub fn calculate_performance_metrics(
        &self, 
        metrics: &[PerformanceMetric]
    ) -> AggregatedPerformanceMetrics {
        let mut valid_metrics = Vec::new();
        
        for metric in metrics {
            if self.validate_calculation(metric.value) {
                valid_metrics.push(metric.clone());
            }
        }

        if valid_metrics.is_empty() {
            return AggregatedPerformanceMetrics::default();
        }

        let values: Vec<f64> = valid_metrics.iter().map(|m| m.value).collect();
        let stats = self.calculate_execution_statistics(&values);

        AggregatedPerformanceMetrics {
            statistics: stats,
            metric_count: valid_metrics.len(),
            invalid_count: metrics.len() - valid_metrics.len(),
        }
    }
}

/// 执行统计信息
#[derive(Debug, Clone)]
pub struct ExecutionStatistics {
    pub count: usize,
    pub mean: f64,
    pub median: f64,
    pub std_dev: f64,
    pub min: f64,
    pub max: f64,
    pub p95: f64,
    pub p99: f64,
}

impl Default for ExecutionStatistics {
    fn default() -> Self {
        Self {
            count: 0,
            mean: f64::NAN,
            median: f64::NAN,
            std_dev: f64::NAN,
            min: f64::NAN,
            max: f64::NAN,
            p95: f64::NAN,
            p99: f64::NAN,
        }
    }
}

/// 性能指标
#[derive(Debug, Clone)]
pub struct PerformanceMetric {
    pub name: String,
    pub value: f64,
    pub timestamp: chrono::DateTime<chrono::Utc>,
}

/// 聚合性能指标
#[derive(Debug, Clone)]
pub struct AggregatedPerformanceMetrics {
    pub statistics: ExecutionStatistics,
    pub metric_count: usize,
    pub invalid_count: usize,
}

impl Default for AggregatedPerformanceMetrics {
    fn default() -> Self {
        Self {
            statistics: ExecutionStatistics::default(),
            metric_count: 0,
            invalid_count: 0,
        }
    }
}
```

### 4. 跨平台文档测试支持

Rust 1.89 改进了跨平台文档测试支持，`cargo test --doc --target` 现在会真正运行测试。

#### 在工作流文档中的应用

```rust
/// 工作流执行器，支持跨平台文档测试
///
/// # 示例
///
/// ```rust
/// use c14_workflow::WorkflowExecutor;
/// 
/// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
/// let mut executor = WorkflowExecutor::new();
/// 
/// // 创建简单的工作流
/// let workflow = executor.create_simple_workflow("test_workflow")?;
/// 
/// // 执行工作流
/// let result = executor.execute(workflow).await?;
/// 
/// assert!(result.is_success());
/// # Ok(())
/// # }
/// ```
pub struct WorkflowExecutor {
    timeout: std::time::Duration,
    max_retries: usize,
}

impl WorkflowExecutor {
    /// 创建新的工作流执行器
    ///
    /// # 示例
    ///
    /// ```rust
    /// use c14_workflow::WorkflowExecutor;
    /// 
    /// let executor = WorkflowExecutor::new();
    /// assert_eq!(executor.timeout(), std::time::Duration::from_secs(30));
    /// ```
    pub fn new() -> Self {
        Self {
            timeout: std::time::Duration::from_secs(30),
            max_retries: 3,
        }
    }

    /// 获取当前超时设置
    pub fn timeout(&self) -> std::time::Duration {
        self.timeout
    }

    /// 设置超时时间
    ///
    /// # 示例
    ///
    /// ```rust
    /// use c14_workflow::WorkflowExecutor;
    /// use std::time::Duration;
    /// 
    /// let mut executor = WorkflowExecutor::new();
    /// executor.set_timeout(Duration::from_secs(60));
    /// 
    /// assert_eq!(executor.timeout(), Duration::from_secs(60));
    /// ```
    pub fn set_timeout(&mut self, timeout: std::time::Duration) {
        self.timeout = timeout;
    }

    /// 创建简单的工作流
    ///
    /// # 示例
    ///
    /// ```rust
    /// use c14_workflow::WorkflowExecutor;
    /// 
    /// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let executor = WorkflowExecutor::new();
    /// let workflow = executor.create_simple_workflow("my_workflow")?;
    /// 
    /// assert_eq!(workflow.name, "my_workflow");
    /// # Ok(())
    /// # }
    /// ```
    pub fn create_simple_workflow(&self, name: &str) -> Result<WorkflowDefinition, WorkflowError> {
        Ok(WorkflowDefinition {
            name: name.to_string(),
            version: "1.0.0".to_string(),
            states: vec![
                WorkflowState {
                    name: "start".to_string(),
                    description: None,
                    is_final: false,
                    is_initial: true,
                    metadata: std::collections::HashMap::new(),
                },
                WorkflowState {
                    name: "end".to_string(),
                    description: None,
                    is_final: true,
                    is_initial: false,
                    metadata: std::collections::HashMap::new(),
                },
            ],
            transitions: vec![
                StateTransition {
                    from_state: "start".to_string(),
                    to_state: "end".to_string(),
                    condition: None,
                    action: None,
                    metadata: std::collections::HashMap::new(),
                },
            ],
            initial_state: "start".to_string(),
            final_states: vec!["end".to_string()],
            metadata: std::collections::HashMap::new(),
        })
    }

    /// 执行工作流
    ///
    /// # 示例
    ///
    /// ```rust
    /// use c14_workflow::WorkflowExecutor;
    /// 
    /// # async fn example() -> Result<(), Box<dyn std::error::Error>> {
    /// let mut executor = WorkflowExecutor::new();
    /// let workflow = executor.create_simple_workflow("test")?;
    /// 
    /// let result = executor.execute(workflow).await?;
    /// assert!(result.is_success());
    /// # Ok(())
    /// # }
    /// ```
    pub async fn execute(&self, workflow: WorkflowDefinition) -> Result<ExecutionResult, WorkflowError> {
        // 验证工作流
        workflow.validate()?;
        
        // 模拟异步执行
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        
        Ok(ExecutionResult {
            workflow_id: workflow.name,
            status: ExecutionStatus::Success,
            execution_time: std::time::Duration::from_millis(10),
            steps_completed: 2,
        })
    }
}

/// 执行结果
#[derive(Debug, Clone)]
pub struct ExecutionResult {
    pub workflow_id: String,
    pub status: ExecutionStatus,
    pub execution_time: std::time::Duration,
    pub steps_completed: usize,
}

impl ExecutionResult {
    pub fn is_success(&self) -> bool {
        matches!(self.status, ExecutionStatus::Success)
    }
}

#[derive(Debug, Clone)]
pub enum ExecutionStatus {
    Success,
    Failed,
    Timeout,
}

/// 状态转换定义
#[derive(Debug, Clone)]
pub struct StateTransition {
    pub from_state: String,
    pub to_state: String,
    pub condition: Option<String>,
    pub action: Option<String>,
    pub metadata: std::collections::HashMap<String, serde_json::Value>,
}
```

## 🔧 最佳实践

### 1. 测试框架使用建议

- 使用新的 `--no-capture` 参数替代 `--nocapture`
- 利用改进的错误提示进行更好的调试
- 编写跨平台兼容的测试代码

### 2. 数组生成函数使用建议

- 依赖 `std::array::from_fn` 的调用顺序保证
- 在需要状态依赖的场景中使用顺序生成
- 利用编译器保证的顺序进行优化

### 3. 数值计算建议

- 依赖 Rust 1.89 的 Quiet NaN 保证
- 正确处理 NaN 值进行统计计算
- 使用标准化的浮点数处理

### 4. 文档测试建议

- 编写可跨平台运行的文档测试
- 使用 `cargo test --doc --target` 进行跨平台验证
- 确保文档示例在所有目标平台上都能运行

## 📊 性能改进

### 测试执行性能

```rust
/// 性能测试套件
#[cfg(test)]
mod performance_tests {
    use super::*;
    use std::time::Instant;

    #[test]
    fn test_array_generation_performance() {
        let start = Instant::now();
        
        // 测试数组生成性能
        let steps: [WorkflowStep; 1000] = WorkflowStepGenerator::create_sequential_workflow_steps();
        
        let duration = start.elapsed();
        println!("生成 1000 个工作流步骤耗时: {:?}", duration);
        
        // 验证顺序正确性
        for (i, step) in steps.iter().enumerate() {
            assert_eq!(step.execution_order, i);
        }
        
        assert!(duration < std::time::Duration::from_millis(100));
    }

    #[test]
    fn test_numerical_calculation_performance() {
        let calculator = WorkflowNumericalCalculator;
        let test_data: Vec<f64> = (0..10000).map(|i| i as f64).collect();
        
        let start = Instant::now();
        let stats = calculator.calculate_execution_statistics(&test_data);
        let duration = start.elapsed();
        
        println!("计算 10000 个数值的统计信息耗时: {:?}", duration);
        println!("统计结果: {:?}", stats);
        
        assert!(duration < std::time::Duration::from_millis(50));
    }
}
```

## 🎯 总结

Rust 1.89 的标准库增强为工作流系统带来了显著的改进：

1. **测试框架改进** - 更好的错误提示和参数规范化
2. **数组生成顺序保证** - 依赖状态的闭包可以安全使用
3. **浮点数标准化** - Quiet NaN 保证符合 IEEE 标准
4. **跨平台文档测试** - 真正的跨平台测试支持

这些改进使得工作流系统能够：

- 提供更好的测试体验和调试信息
- 安全地使用状态依赖的数组生成
- 进行可靠的数值计算和统计
- 确保文档示例在所有平台上都能运行

通过合理使用这些标准库增强，我们可以构建更可靠、更易测试、更跨平台兼容的工作流系统。
