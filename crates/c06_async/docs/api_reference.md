# API 参考文档

## 异步生态系统分析模块

### AsyncRuntimeAnalyzer

异步运行时分析器，用于分析和比较不同异步运行时的特性。

#### 方法

##### `new() -> Self`

创建新的异步运行时分析器实例。

```rust
let analyzer = AsyncRuntimeAnalyzer::new();
```

##### `get_runtime_analysis(&self, runtime_name: &str) -> Option<&AsyncEcosystemAnalysis>`

获取指定运行时的分析结果。

**参数：**

- `runtime_name`: 运行时名称（"std", "tokio", "async-std", "smol"）

**返回值：**

- `Some(analysis)`: 如果找到运行时分析
- `None`: 如果运行时不存在

```rust
if let Some(analysis) = analyzer.get_runtime_analysis("tokio") {
    println!("Tokio 特性: {:?}", analysis.core_features);
}
```

##### `get_all_analyses(&self) -> &HashMap<String, AsyncEcosystemAnalysis>`

获取所有运行时的分析结果。

```rust
let all_analyses = analyzer.get_all_analyses();
for (name, analysis) in all_analyses {
    println!("{}: {:?}", name, analysis.use_cases);
}
```

##### `compare_runtimes(&self, runtime1: &str, runtime2: &str) -> Option<RuntimeComparison>`

比较两个运行时的特性。

**参数：**

- `runtime1`: 第一个运行时名称
- `runtime2`: 第二个运行时名称

**返回值：**

- `Some(comparison)`: 运行时比较结果
- `None`: 如果任一运行时不存在

```rust
if let Some(comparison) = analyzer.compare_runtimes("tokio", "async-std") {
    println!("性能优势: {}", comparison.performance_winner);
    println!("生态系统优势: {}", comparison.ecosystem_winner);
}
```

### AsyncEcosystemAnalysis

异步生态系统分析结果结构体。

#### 字段

- `runtime_name: String` - 运行时名称
- `core_features: Vec<String>` - 核心特性列表
- `performance_characteristics: PerformanceCharacteristics` - 性能特征
- `use_cases: Vec<String>` - 适用场景
- `ecosystem_maturity: EcosystemMaturity` - 生态系统成熟度
- `learning_curve: LearningCurve` - 学习曲线

### PerformanceCharacteristics

性能特征结构体。

#### 字段1

- `memory_usage: String` - 内存使用情况
- `startup_time: String` - 启动时间
- `concurrency_performance: String` - 并发性能
- `latency_characteristics: String` - 延迟特征

## 异步集成框架模块

### AsyncIntegrationPatterns

异步集成模式演示器。

#### 方法1

##### `new(max_concurrent: usize) -> Self`

创建新的异步集成模式实例。

**参数：**

- `max_concurrent`: 最大并发任务数

```rust
let patterns = AsyncIntegrationPatterns::new(10);
```

##### `runtime_adapter_pattern(&self) -> Result<()>`

演示运行时适配器模式。

```rust
patterns.runtime_adapter_pattern().await?;
```

##### `task_composition_pattern(&self) -> Result<()>`

演示任务组合模式。

```rust
patterns.task_composition_pattern().await?;
```

##### `runtime_abstraction_pattern(&self) -> Result<()>`

演示运行时抽象模式。

```rust
patterns.runtime_abstraction_pattern().await?;
```

##### `async_sync_conversion_pattern(&self) -> Result<()>`

演示异步同步转换模式。

```rust
patterns.async_sync_conversion_pattern().await?;
```

##### `aggregation_composition_pattern(&self) -> Result<()>`

演示聚合组合设计模式。

```rust
patterns.aggregation_composition_pattern().await?;
```

## 简化异步运行时框架模块

### SimpleAsyncRuntimeFramework

简化的异步运行时集成框架。

#### 方法2

##### `new(config: RuntimeConfig) -> Self`

创建新的简化异步运行时框架实例。

```rust
let config = RuntimeConfig::default();
let framework = SimpleAsyncRuntimeFramework::new(config);
```

##### `execute_task(&self, task: Box<dyn AsyncTask>) -> Result<String>`

执行单个异步任务。

**参数：**

- `task`: 要执行的异步任务

**返回值：**

- `Ok(result)`: 任务执行成功，返回结果
- `Err(error)`: 任务执行失败

```rust
let task = Box::new(ExampleTask::new("my_task", TaskPriority::Normal, 100));
let result = framework.execute_task(task).await?;
```

##### `execute_batch(&self, tasks: Vec<Box<dyn AsyncTask>>) -> Result<Vec<String>>`

执行批量异步任务。

**参数：**

- `tasks`: 要执行的任务列表

**返回值：**

- `Ok(results)`: 所有任务执行成功，返回结果列表
- `Err(error)`: 任一任务执行失败

```rust
let tasks = vec![
    Box::new(ExampleTask::new("task1", TaskPriority::High, 50)),
    Box::new(ExampleTask::new("task2", TaskPriority::Normal, 100)),
];
let results = framework.execute_batch(tasks).await?;
```

##### `get_metrics(&self) -> RuntimeMetrics`

获取运行时性能指标。

```rust
let metrics = framework.get_metrics().await;
println!("任务总数: {}", metrics.task_count);
println!("成功数: {}", metrics.success_count);
```

##### `health_check(&self) -> Result<bool>`

执行健康检查。

**返回值：**

- `Ok(true)`: 健康检查通过
- `Ok(false)`: 健康检查失败
- `Err(error)`: 健康检查出错

```rust
let is_healthy = framework.health_check().await?;
if is_healthy {
    println!("运行时健康");
} else {
    println!("运行时异常");
}
```

### RuntimeConfig

运行时配置结构体。

#### 字段2

- `runtime_type: AsyncRuntimeType` - 运行时类型
- `max_concurrent_tasks: usize` - 最大并发任务数
- `timeout_duration: Duration` - 超时时间
- `enable_monitoring: bool` - 是否启用监控

#### 方法3

##### `default() -> Self`

创建默认配置。

```rust
let config = RuntimeConfig::default();
```

### AsyncRuntimeType

异步运行时类型枚举。

#### 变体

- `Std` - 标准库
- `Tokio` - Tokio运行时
- `AsyncStd` - async-std运行时
- `Smol` - smol运行时

### TaskPriority

任务优先级枚举。

#### 变体3

- `Low = 1` - 低优先级
- `Normal = 2` - 普通优先级
- `High = 3` - 高优先级
- `Critical = 4` - 关键优先级

### AsyncTask Trait

异步任务抽象trait。

#### 方法4

##### `execute(&self) -> Result<String>`

执行异步任务。

##### `get_name(&self) -> &str`

获取任务名称。

##### `get_priority(&self) -> TaskPriority`

获取任务优先级。

##### `get_timeout(&self) -> Duration`

获取任务超时时间。

### ExampleTask

示例任务实现。

#### 方法5

##### `new(name: &str, priority: TaskPriority, delay_ms: u64) -> Self`

创建新的示例任务。

**参数：**

- `name`: 任务名称
- `priority`: 任务优先级
- `delay_ms`: 执行延迟（毫秒）

```rust
let task = ExampleTask::new("my_task", TaskPriority::High, 100);
```

## 异步同步转换服务模块

### AsyncSyncConversionService

异步同步转换服务。

#### 方法6

##### `new(max_threads: usize) -> Self`

创建新的转换服务实例。

```rust
let service = AsyncSyncConversionService::new(10);
```

##### `async_to_sync<T, F>(&self, async_operation: F) -> Result<T>`

将异步操作转换为同步执行。

**参数：**

- `async_operation`: 异步操作

```rust
let result = service.async_to_sync(async {
    tokio::time::sleep(Duration::from_millis(100)).await;
    Ok("异步操作完成".to_string())
}).await?;
```

##### `sync_to_async<F, T>(&self, sync_operation: F) -> Result<T>`

将同步操作转换为异步执行。

**参数：**

- `sync_operation`: 同步操作

```rust
let result = service.sync_to_async(|| {
    std::thread::sleep(Duration::from_millis(100));
    Ok("同步操作完成".to_string())
}).await?;
```

##### `hybrid_conversion(&self) -> Result<(String, String)>`

执行混合转换模式。

```rust
let (async_result, sync_result) = service.hybrid_conversion().await?;
```

## 聚合组合服务模块

### AggregationCompositionService

聚合组合设计模式服务。

#### 方法7

##### 1`new() -> Self`

创建新的聚合组合服务实例。

```rust
let service = AggregationCompositionService::new();
```

##### `register_component(&self, component: Box<dyn AsyncComponent + Send + Sync>) -> Result<()>`

注册异步组件。

```rust
let component = Box::new(DataProcessingComponent::new("processor1", 100));
service.register_component(component).await?;
```

##### `sequential_aggregation(&self, component_names: Vec<String>, input: &str) -> Result<Vec<String>>`

执行顺序聚合。

**参数：**

- `component_names`: 组件名称列表
- `input`: 输入数据

```rust
let results = service.sequential_aggregation(
    vec!["processor1".to_string(), "processor2".to_string()],
    "input_data"
).await?;
```

##### `parallel_aggregation(&self, component_names: Vec<String>, input: &str) -> Result<Vec<String>>`

执行并行聚合。

```rust
let results = service.parallel_aggregation(
    vec!["processor1".to_string(), "processor2".to_string()],
    "input_data"
).await?;
```

### AsyncComponent Trait

异步组件抽象trait。

#### 方法8

##### `execute(&self, input: String) -> Result<String>`

执行组件处理。

##### 1`get_name(&self) -> &str`

获取组件名称。

### DataProcessingComponent

数据处理组件实现。

#### 方法9

##### `new(name: &str, delay_ms: u64) -> Self`

创建新的数据处理组件。

```rust
let component = DataProcessingComponent::new("processor", 100);
```

## 演示函数

### `demonstrate_async_ecosystem_comprehensive() -> Result<()>`

演示异步生态系统全面分析。

```rust
demonstrate_async_ecosystem_comprehensive().await?;
```

### `demonstrate_async_integration_framework() -> Result<()>`

演示异步集成框架。

```rust
demonstrate_async_integration_framework().await?;
```

### `demonstrate_simple_async_runtime_framework() -> Result<()>`

演示简化异步运行时框架。

```rust
demonstrate_simple_async_runtime_framework().await?;
```
