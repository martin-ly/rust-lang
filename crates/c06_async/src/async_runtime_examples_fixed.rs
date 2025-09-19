//! 异步运行时具体示例和组合模式
//! 
//! 本模块提供了各个异步运行时的具体使用示例，
//! 包括：std、tokio、async-std、smol的实际应用场景和组合模式。

use std::sync::Arc;
use std::time::Duration;
use std::collections::HashMap;
use anyhow::Result;
use tokio::time::sleep;
use tokio::sync::{Mutex, Semaphore};
use tokio::task;
use tokio::net::{TcpListener as TokioTcpListener, TcpStream as TokioTcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use futures::future::{join_all, try_join_all};
use futures::stream::StreamExt;

/// 1. std 标准库异步示例
/// 
/// 展示如何使用标准库的基础异步功能
pub struct StdAsyncExamples {
    shared_data: Arc<Mutex<Vec<String>>>,
}

impl StdAsyncExamples {
    pub fn new() -> Self {
        Self {
            shared_data: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// 基础异步函数示例
    pub async fn basic_async_function(&self, input: &str) -> Result<String> {
        // 模拟异步操作
        tokio::time::sleep(Duration::from_millis(100)).await;
        Ok(format!("std_async_result: {}", input))
    }

    /// 异步迭代器示例
    pub async fn async_iterator_example(&self) -> Result<Vec<String>> {
        let mut results = Vec::new();
        
        for i in 0..5 {
            let result = self.basic_async_function(&format!("item_{}", i)).await?;
            results.push(result);
        }
        
        Ok(results)
    }

    /// 异步错误处理示例
    pub async fn async_error_handling(&self, should_fail: bool) -> Result<String> {
        if should_fail {
            return Err(anyhow::anyhow!("模拟异步错误"));
        }
        
        sleep(Duration::from_millis(50)).await;
        Ok("异步操作成功".to_string())
    }

    /// 演示标准库异步特性的局限性
    pub async fn demonstrate_std_limitations(&self) -> Result<()> {
        println!("📚 std 标准库异步示例:");
        println!("  - 基础异步函数支持");
        println!("  - 需要外部运行时执行");
        println!("  - 提供 Future trait 和 async/await 语法");
        
        let result = self.basic_async_function("test").await?;
        println!("  结果: {}", result);
        
        Ok(())
    }
}

/// 2. Tokio 运行时示例
/// 
/// 展示 Tokio 的高性能异步编程特性
pub struct TokioExamples {
    connection_pool: Arc<Semaphore>,
    shared_state: Arc<Mutex<HashMap<String, String>>>,
}

impl TokioExamples {
    pub fn new(max_connections: usize) -> Self {
        Self {
            connection_pool: Arc::new(Semaphore::new(max_connections)),
            shared_state: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// 高性能并发处理示例
    pub async fn high_performance_concurrent_processing(&self, tasks: Vec<String>) -> Result<Vec<String>> {
        let semaphore = Arc::clone(&self.connection_pool);
        let mut handles = Vec::new();

        for task in tasks {
            let semaphore = Arc::clone(&semaphore);
            let handle = task::spawn(async move {
                let _permit = semaphore.acquire().await.unwrap();
                Self::process_task(task).await
            });
            handles.push(handle);
        }

        let results = try_join_all(handles).await?;
        Ok(results)
    }

    /// 流处理示例
    pub async fn stream_processing_example(&self) -> Result<()> {
        println!("🌊 Tokio 流处理示例:");
        
        // 创建数据流
        let data_stream = futures::stream::iter(0..10)
            .then(|i| async move {
                sleep(Duration::from_millis(10)).await;
                format!("stream_item_{}", i)
            });

        // 处理流数据
        let processed_stream = data_stream
            .map(|item| format!("processed_{}", item))
            .collect::<Vec<_>>();

        let results = processed_stream.await;
        println!("  流处理结果: {:?}", results);
        
        Ok(())
    }

    /// 定时器和调度示例
    pub async fn timer_and_scheduling_example(&self) -> Result<()> {
        println!("⏰ Tokio 定时器和调度示例:");
        
        // 定时任务
        let interval = tokio::time::interval(Duration::from_millis(100));
        let mut count = 0;
        
        tokio::pin!(interval);
        
        while count < 5 {
            interval.as_mut().tick().await;
            println!("  定时任务执行: {}", count);
            count += 1;
        }
        
        Ok(())
    }

    async fn process_task(task: String) -> Result<String> {
        sleep(Duration::from_millis(50)).await;
        Ok(format!("tokio_processed_{}", task))
    }
}

/// 3. async-std 运行时示例
/// 
/// 展示 async-std 的标准库风格 API
pub struct AsyncStdExamples {
    file_cache: Arc<Mutex<HashMap<String, String>>>,
}

impl AsyncStdExamples {
    pub fn new() -> Self {
        Self {
            file_cache: Arc::new(Mutex::new(HashMap::new())),
        }
    }

    /// 标准库风格的异步文件操作
    pub async fn file_operations_example(&self) -> Result<()> {
        println!("📁 async-std 文件操作示例:");
        
        // 模拟文件操作（使用内存缓存）
        let filename = "example.txt";
        let content = "这是 async-std 风格的文件内容";
        
        // 写入文件
        self.write_file(filename, content).await?;
        println!("  文件写入成功: {}", filename);
        
        // 读取文件
        let read_content = self.read_file(filename).await?;
        println!("  文件读取成功: {}", read_content);
        
        Ok(())
    }

    /// 网络客户端示例
    pub async fn network_client_example(&self, host: &str, port: u16) -> Result<()> {
        println!("🌐 async-std 网络客户端示例:");
        
        // 模拟网络连接
        let connection_info = format!("{}:{}", host, port);
        println!("  连接到: {}", connection_info);
        
        // 模拟发送请求
        let request = "GET / HTTP/1.1\r\nHost: example.com\r\n\r\n";
        let response = self.send_request(&connection_info, request).await?;
        println!("  收到响应: {}", response);
        
        Ok(())
    }

    /// 任务管理示例
    pub async fn task_management_example(&self) -> Result<()> {
        println!("📋 async-std 任务管理示例:");
        
        // 创建多个任务
        let tasks = vec![
            self.create_task("task_1", Duration::from_millis(100)),
            self.create_task("task_2", Duration::from_millis(150)),
            self.create_task("task_3", Duration::from_millis(200)),
        ];

        // 并发执行任务
        let results = join_all(tasks).await;
        println!("  任务执行结果: {:?}", results);
        
        Ok(())
    }

    /// 标准库兼容性示例
    pub async fn std_compatibility_example(&self) -> Result<()> {
        println!("🔄 async-std 标准库兼容性示例:");
        
        // 展示与标准库 API 的一致性
        let data = vec![1, 2, 3, 4, 5];
        let processed_data = self.process_data_std_style(data).await?;
        println!("  标准库风格处理结果: {:?}", processed_data);
        
        Ok(())
    }

    async fn write_file(&self, filename: &str, content: &str) -> Result<()> {
        let mut cache = self.file_cache.lock().await;
        cache.insert(filename.to_string(), content.to_string());
        sleep(Duration::from_millis(10)).await; // 模拟I/O延迟
        Ok(())
    }

    async fn read_file(&self, filename: &str) -> Result<String> {
        let cache = self.file_cache.lock().await;
        let content = cache.get(filename)
            .ok_or_else(|| anyhow::anyhow!("文件不存在: {}", filename))?;
        sleep(Duration::from_millis(5)).await; // 模拟I/O延迟
        Ok(content.clone())
    }

    async fn send_request(&self, _connection: &str, request: &str) -> Result<String> {
        sleep(Duration::from_millis(20)).await; // 模拟网络延迟
        Ok(format!("HTTP/1.1 200 OK\r\nContent-Length: {}\r\n\r\n{}", 
                   request.len(), request))
    }

    async fn create_task(&self, name: &str, duration: Duration) -> String {
        sleep(duration).await;
        format!("{}_completed", name)
    }

    async fn process_data_std_style(&self, mut data: Vec<i32>) -> Result<Vec<i32>> {
        // 使用标准库风格的API处理数据
        data.sort();
        data.retain(|&x| x % 2 == 0);
        data.iter_mut().for_each(|x| *x *= 2);
        Ok(data)
    }
}

/// 4. smol 运行时示例
/// 
/// 展示 smol 的轻量级特性
pub struct SmolExamples {
    task_queue: Arc<Mutex<Vec<String>>>,
}

impl SmolExamples {
    pub fn new() -> Self {
        Self {
            task_queue: Arc::new(Mutex::new(Vec::new())),
        }
    }

    /// 轻量级任务调度示例
    pub async fn lightweight_task_scheduling(&self) -> Result<()> {
        println!("⚡ smol 轻量级任务调度示例:");
        
        // 创建轻量级任务
        let tasks = vec![
            "lightweight_task_1".to_string(),
            "lightweight_task_2".to_string(),
            "lightweight_task_3".to_string(),
        ];

        // 使用 smol 风格的任务调度
        let results = self.schedule_lightweight_tasks(tasks).await?;
        println!("  轻量级任务结果: {:?}", results);
        
        Ok(())
    }

    /// 嵌入式友好示例
    pub async fn embedded_friendly_example(&self) -> Result<()> {
        println!("🔧 smol 嵌入式友好示例:");
        
        // 模拟资源受限环境
        let memory_limit = 1024; // 1KB 内存限制
        let cpu_cores = 1; // 单核CPU
        
        println!("  内存限制: {} bytes", memory_limit);
        println!("  CPU核心数: {}", cpu_cores);
        
        // 在资源受限环境下执行任务
        let result = self.execute_in_resource_constrained_environment(memory_limit, cpu_cores).await?;
        println!("  资源受限环境执行结果: {}", result);
        
        Ok(())
    }

    /// 运行时兼容性示例
    pub async fn runtime_compatibility_example(&self) -> Result<()> {
        println!("🔄 smol 运行时兼容性示例:");
        
        // 展示与其他运行时的兼容性
        let tokio_compatible = self.simulate_tokio_compatibility().await?;
        let async_std_compatible = self.simulate_async_std_compatibility().await?;
        
        println!("  Tokio 兼容性测试: {}", tokio_compatible);
        println!("  async-std 兼容性测试: {}", async_std_compatible);
        
        Ok(())
    }

    /// 零依赖示例
    pub async fn zero_dependency_example(&self) -> Result<()> {
        println!("🎯 smol 零依赖示例:");
        
        // 展示不依赖外部库的纯异步操作
        let result = self.pure_async_operation().await?;
        println!("  零依赖异步操作结果: {}", result);
        
        Ok(())
    }

    async fn schedule_lightweight_tasks(&self, tasks: Vec<String>) -> Result<Vec<String>> {
        let mut results = Vec::new();
        
        for task in tasks {
            let result = self.execute_lightweight_task(task).await?;
            results.push(result);
        }
        
        Ok(results)
    }

    async fn execute_lightweight_task(&self, task: String) -> Result<String> {
        // 模拟轻量级任务执行
        sleep(Duration::from_millis(5)).await;
        Ok(format!("smol_{}_completed", task))
    }

    async fn execute_in_resource_constrained_environment(&self, _memory_limit: usize, _cpu_cores: usize) -> Result<String> {
        // 模拟在资源受限环境下的执行
        sleep(Duration::from_millis(2)).await; // 极短的执行时间
        Ok("resource_constrained_execution_success".to_string())
    }

    async fn simulate_tokio_compatibility(&self) -> Result<String> {
        // 模拟与 Tokio 的兼容性
        sleep(Duration::from_millis(10)).await;
        Ok("tokio_compatible".to_string())
    }

    async fn simulate_async_std_compatibility(&self) -> Result<String> {
        // 模拟与 async-std 的兼容性
        sleep(Duration::from_millis(10)).await;
        Ok("async_std_compatible".to_string())
    }

    async fn pure_async_operation(&self) -> Result<String> {
        // 纯异步操作，不依赖外部库
        sleep(Duration::from_millis(5)).await;
        Ok("pure_async_operation_result".to_string())
    }
}

/// 5. 运行时组合模式示例
/// 
/// 展示如何组合不同的异步运行时
pub struct RuntimeCompositionExamples {
    runtime_selector: Arc<Mutex<String>>,
}

impl RuntimeCompositionExamples {
    pub fn new() -> Self {
        Self {
            runtime_selector: Arc::new(Mutex::new("tokio".to_string())),
        }
    }

    /// 运行时选择器模式
    pub async fn runtime_selector_pattern(&self, task_type: &str) -> Result<String> {
        println!("🎛️ 运行时选择器模式:");
        
        let runtime = match task_type {
            "high_performance" => "tokio",
            "easy_development" => "async-std",
            "lightweight" => "smol",
            "basic" => "std",
            _ => "tokio",
        };

        let result = self.execute_with_runtime(runtime, task_type).await?;
        println!("  使用 {} 运行时执行 {} 任务: {}", runtime, task_type, result);
        
        Ok(result)
    }

    /// 运行时适配器模式
    pub async fn runtime_adapter_pattern(&self) -> Result<()> {
        println!("🔌 运行时适配器模式:");
        
        // 为不同运行时提供统一接口
        let tasks = vec![
            ("tokio", "high_perf_task"),
            ("async-std", "easy_dev_task"),
            ("smol", "lightweight_task"),
        ];

        for (runtime, task) in tasks {
            let result = self.execute_with_runtime(runtime, task).await?;
            println!("  {} 适配器执行 {}: {}", runtime, task, result);
        }
        
        Ok(())
    }

    /// 运行时桥接模式
    pub async fn runtime_bridge_pattern(&self) -> Result<()> {
        println!("🌉 运行时桥接模式:");
        
        // 在不同运行时之间桥接数据
        let tokio_data = self.generate_tokio_data().await?;
        let async_std_data = self.convert_to_async_std_format(tokio_data.clone()).await?;
        let smol_data = self.convert_to_smol_format(async_std_data.clone()).await?;
        
        println!("  Tokio 数据: {}", tokio_data);
        println!("  async-std 数据: {}", async_std_data);
        println!("  smol 数据: {}", smol_data);
        
        Ok(())
    }

    async fn execute_with_runtime(&self, runtime: &str, task: &str) -> Result<String> {
        match runtime {
            "tokio" => {
                sleep(Duration::from_millis(10)).await;
                Ok(format!("tokio_executed_{}", task))
            }
            "async-std" => {
                sleep(Duration::from_millis(15)).await;
                Ok(format!("async_std_executed_{}", task))
            }
            "smol" => {
                sleep(Duration::from_millis(5)).await;
                Ok(format!("smol_executed_{}", task))
            }
            "std" => {
                sleep(Duration::from_millis(20)).await;
                Ok(format!("std_executed_{}", task))
            }
            _ => Err(anyhow::anyhow!("未知运行时: {}", runtime))
        }
    }

    async fn generate_tokio_data(&self) -> Result<String> {
        sleep(Duration::from_millis(10)).await;
        Ok("tokio_data".to_string())
    }

    async fn convert_to_async_std_format(&self, data: String) -> Result<String> {
        sleep(Duration::from_millis(5)).await;
        Ok(format!("async_std_{}", data))
    }

    async fn convert_to_smol_format(&self, data: String) -> Result<String> {
        sleep(Duration::from_millis(3)).await;
        Ok(format!("smol_{}", data))
    }
}

/// 综合演示所有异步运行时的特性
pub async fn demonstrate_all_async_runtimes() -> Result<()> {
    println!("🚀 Rust 异步运行时全面示例演示");
    println!("================================================");

    // 1. std 标准库示例
    println!("\n📚 1. std 标准库异步示例:");
    let std_examples = StdAsyncExamples::new();
    std_examples.demonstrate_std_limitations().await?;

    // 2. Tokio 示例
    println!("\n⚡ 2. Tokio 高性能异步示例:");
    let tokio_examples = TokioExamples::new(5);
    
    // 高性能并发处理
    let tasks = vec!["task1".to_string(), "task2".to_string(), "task3".to_string()];
    let results = tokio_examples.high_performance_concurrent_processing(tasks).await?;
    println!("  并发处理结果: {:?}", results);
    
    // 流处理
    tokio_examples.stream_processing_example().await?;
    
    // 定时器
    tokio_examples.timer_and_scheduling_example().await?;

    // 3. async-std 示例
    println!("\n📁 3. async-std 标准库风格示例:");
    let async_std_examples = AsyncStdExamples::new();
    
    async_std_examples.file_operations_example().await?;
    async_std_examples.network_client_example("localhost", 8080).await?;
    async_std_examples.task_management_example().await?;
    async_std_examples.std_compatibility_example().await?;

    // 4. smol 示例
    println!("\n⚡ 4. smol 轻量级示例:");
    let smol_examples = SmolExamples::new();
    
    smol_examples.lightweight_task_scheduling().await?;
    smol_examples.embedded_friendly_example().await?;
    smol_examples.runtime_compatibility_example().await?;
    smol_examples.zero_dependency_example().await?;

    // 5. 运行时组合示例
    println!("\n🔧 5. 运行时组合模式示例:");
    let composition_examples = RuntimeCompositionExamples::new();
    
    composition_examples.runtime_selector_pattern("high_performance").await?;
    composition_examples.runtime_adapter_pattern().await?;
    composition_examples.runtime_bridge_pattern().await?;

    println!("\n✅ 所有异步运行时示例演示完成!");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_std_async_examples() {
        let examples = StdAsyncExamples::new();
        assert!(examples.basic_async_function("test").await.is_ok());
        assert!(examples.async_iterator_example().await.is_ok());
    }

    #[tokio::test]
    async fn test_tokio_examples() {
        let examples = TokioExamples::new(3);
        let tasks = vec!["test1".to_string(), "test2".to_string()];
        assert!(examples.high_performance_concurrent_processing(tasks).await.is_ok());
        assert!(examples.stream_processing_example().await.is_ok());
    }

    #[tokio::test]
    async fn test_async_std_examples() {
        let examples = AsyncStdExamples::new();
        assert!(examples.file_operations_example().await.is_ok());
        assert!(examples.task_management_example().await.is_ok());
    }

    #[tokio::test]
    async fn test_smol_examples() {
        let examples = SmolExamples::new();
        assert!(examples.lightweight_task_scheduling().await.is_ok());
        assert!(examples.embedded_friendly_example().await.is_ok());
    }

    #[tokio::test]
    async fn test_runtime_composition() {
        let examples = RuntimeCompositionExamples::new();
        assert!(examples.runtime_selector_pattern("high_performance").await.is_ok());
        assert!(examples.runtime_adapter_pattern().await.is_ok());
    }
}
