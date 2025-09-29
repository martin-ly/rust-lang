//! 异步编程最佳实践示例
//! 
//! 本示例展示了异步编程的最佳实践和常见陷阱：
//! - 正确的异步函数设计
//! - 资源管理和生命周期
//! - 错误处理策略
//! - 性能优化技巧
//! - 常见陷阱和解决方案
//! 
//! 运行方式：
//! ```bash
//! cargo run --example async_best_practices
//! ```

use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{Mutex, Semaphore};
use tokio::time::{sleep, timeout};
use tokio::task::JoinSet;
use futures::{StreamExt, future, stream};
use anyhow::{Result, Context};

#[tokio::main]
async fn main() -> Result<()> {
    println!("🎯 异步编程最佳实践演示");
    println!("================================");

    // 1. 异步函数设计最佳实践
    println!("\n✅ 1. 异步函数设计最佳实践");
    demo_async_function_design().await?;

    // 2. 资源管理最佳实践
    println!("\n🔧 2. 资源管理最佳实践");
    demo_resource_management().await?;

    // 3. 错误处理最佳实践
    println!("\n❌ 3. 错误处理最佳实践");
    demo_error_handling_best_practices().await?;

    // 4. 性能优化最佳实践
    println!("\n⚡ 4. 性能优化最佳实践");
    demo_performance_best_practices().await?;

    // 5. 常见陷阱和解决方案
    println!("\n🚫 5. 常见陷阱和解决方案");
    demo_common_pitfalls().await?;

    println!("\n🎉 最佳实践演示完成！");
    Ok(())
}

/// 1. 异步函数设计最佳实践
async fn demo_async_function_design() -> Result<()> {
    println!("  演示良好的异步函数设计...");

    // ✅ 好的设计：清晰的错误处理
    match fetch_user_data(123).await {
        Ok(user) => println!("    成功获取用户数据: {:?}", user),
        Err(e) => println!("    获取用户数据失败: {}", e),
    }

    // ✅ 好的设计：使用适当的返回类型
    let result = process_data_safely("test_data".to_string()).await;
    println!("    安全数据处理结果: {:?}", result);

    // ✅ 好的设计：合理的超时设置
    match timeout(Duration::from_secs(5), long_running_operation()).await {
        Ok(result) => println!("    长时间操作完成: {}", result),
        Err(_) => println!("    长时间操作超时"),
    }

    // ✅ 好的设计：使用 JoinSet 管理任务生命周期
    let mut join_set = JoinSet::new();
    
    for i in 0..5 {
        join_set.spawn(async move {
            let result = async_task(&format!("任务{}", i), 100).await;
            (i, result)
        });
    }

    while let Some(result) = join_set.join_next().await {
        match result {
            Ok((id, value)) => println!("    任务 {} 完成: {}", id, value),
            Err(e) => println!("    任务失败: {}", e),
        }
    }

    Ok(())
}

/// 2. 资源管理最佳实践
async fn demo_resource_management() -> Result<()> {
    println!("  演示资源管理最佳实践...");

    // ✅ 使用 RAII 模式管理资源
    {
        let resource = ManagedResource::new("测试资源").await?;
        resource.do_work().await?;
        println!("    资源在作用域内使用");
    } // 资源自动清理
    println!("    资源已自动清理");

    // ✅ 使用 Arc 共享数据，避免不必要的克隆
    let shared_data = Arc::new(Mutex::new(Vec::new()));
    let mut handles = vec![];

    for i in 0..5 {
        let data = Arc::clone(&shared_data); // 只克隆 Arc，不克隆数据
        let handle = tokio::spawn(async move {
            let mut vec = data.lock().await;
            vec.push(i);
            println!("    添加数据: {}", i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await?;
    }

    println!("    共享数据最终状态: {:?}", *shared_data.lock().await);

    // ✅ 使用 Semaphore 控制资源使用
    let semaphore = Arc::new(Semaphore::new(3)); // 最多 3 个并发
    let mut handles = vec![];

    for i in 0..10 {
        let semaphore = Arc::clone(&semaphore);
        let handle = tokio::spawn(async move {
            let _permit = semaphore.acquire().await.unwrap();
            println!("    任务 {} 获得资源", i);
            sleep(Duration::from_millis(100)).await;
            println!("    任务 {} 释放资源", i);
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await?;
    }

    Ok(())
}

/// 3. 错误处理最佳实践
async fn demo_error_handling_best_practices() -> Result<()> {
    println!("  演示错误处理最佳实践...");

    // ✅ 使用 anyhow 进行错误处理
    match robust_operation().await {
        Ok(result) => println!("    操作成功: {}", result),
        Err(e) => println!("    操作失败: {}", e),
    }

    // ✅ 使用 ? 操作符传播错误
    let result = chain_operations().await?;
    println!("    链式操作成功: {}", result);

    // ✅ 使用 context 提供错误上下文
    match operation_with_context().await {
        Ok(result) => println!("    带上下文操作成功: {}", result),
        Err(e) => println!("    带上下文操作失败: {}", e),
    }

    // ✅ 使用适当的错误类型
    match typed_error_handling().await {
        Ok(result) => println!("    类型化错误处理成功: {:?}", result),
        Err(e) => println!("    类型化错误处理失败: {}", e),
    }

    Ok(())
}

/// 4. 性能优化最佳实践
async fn demo_performance_best_practices() -> Result<()> {
    println!("  演示性能优化最佳实践...");

    // ✅ 批量处理
    let items = (1..=100).collect::<Vec<_>>();
    let batch_size = 10;
    let start = std::time::Instant::now();

    let mut results = Vec::new();
    for chunk in items.chunks(batch_size) {
        let chunk_futures = chunk.iter().map(|&item| process_item_efficiently(item));
        let chunk_results = future::join_all(chunk_futures).await;
        results.extend(chunk_results);
    }

    let batch_time = start.elapsed();
    println!("    批量处理 {} 个项目耗时: {:?}", items.len(), batch_time);

    // ✅ 使用 Stream 进行流式处理
    let start = std::time::Instant::now();
    let numbers = stream::iter(1..=50);
    let processed = numbers
        .map(|x| async move { x * 2 })
        .buffer_unordered(5) // 控制并发度
        .collect::<Vec<_>>()
        .await;
    
    let stream_time = start.elapsed();
    println!("    Stream 处理 {} 个项目耗时: {:?}", processed.len(), stream_time);

    // ✅ 使用 pin! 宏避免堆分配
    let future = expensive_operation();
    futures::pin_mut!(future); // 在栈上固定 Future
    let result = future.await;
    println!("    使用 pin! 宏的结果: {}", result);

    Ok(())
}

/// 5. 常见陷阱和解决方案
async fn demo_common_pitfalls() -> Result<()> {
    println!("  演示常见陷阱和解决方案...");

    // ❌ 陷阱：阻塞异步运行时
    println!("    陷阱1: 阻塞异步运行时");
    println!("    ❌ 错误做法: std::thread::sleep(Duration::from_millis(100))");
    println!("    ✅ 正确做法: tokio::time::sleep(Duration::from_millis(100)).await");

    // ✅ 解决方案：使用异步替代
    sleep(Duration::from_millis(100)).await;
    println!("    使用异步睡眠");

    // ❌ 陷阱：忽略错误
    println!("    陷阱2: 忽略错误");
    println!("    ❌ 错误做法: let _ = risky_operation().await;");
    println!("    ✅ 正确做法: risky_operation().await.context(\"操作失败\")?;");

    // ✅ 解决方案：正确处理错误
    match risky_operation().await {
        Ok(result) => println!("    风险操作成功: {}", result),
        Err(e) => println!("    风险操作失败: {}", e),
    }

    // ❌ 陷阱：死锁
    println!("    陷阱3: 死锁");
    println!("    ❌ 错误做法: 不一致的锁顺序");
    println!("    ✅ 正确做法: 一致的锁顺序");

    // ✅ 解决方案：一致的锁顺序
    let mutex1 = Arc::new(Mutex::new(0));
    let mutex2 = Arc::new(Mutex::new(0));

    let handle1 = tokio::spawn({
        let mutex1 = Arc::clone(&mutex1);
        let mutex2 = Arc::clone(&mutex2);
        async move {
            let _lock1 = mutex1.lock().await;
            let _lock2 = mutex2.lock().await;
            println!("    任务1: 按顺序获取锁");
        }
    });

    let handle2 = tokio::spawn({
        let mutex1 = Arc::clone(&mutex1);
        let mutex2 = Arc::clone(&mutex2);
        async move {
            let _lock1 = mutex1.lock().await; // 相同的锁顺序
            let _lock2 = mutex2.lock().await;
            println!("    任务2: 按顺序获取锁");
        }
    });

    let _ = tokio::join!(handle1, handle2);

    // ❌ 陷阱：内存泄漏
    println!("    陷阱4: 内存泄漏");
    println!("    ❌ 错误做法: 循环引用");
    println!("    ✅ 正确做法: 使用 Weak 引用");

    // ✅ 解决方案：使用 Weak 引用
    let data = Arc::new(Mutex::new(0));
    let weak_data = Arc::downgrade(&data);
    
    let handle = tokio::spawn(async move {
        for i in 0..3 {
            if let Some(strong_data) = weak_data.upgrade() {
                let mut value = strong_data.lock().await;
                *value += i;
                println!("    使用 Weak 引用更新值: {}", *value);
            }
            sleep(Duration::from_millis(100)).await;
        }
    });

    handle.await?;
    println!("    使用 Weak 引用避免内存泄漏");

    Ok(())
}

// 辅助函数和结构体

/// 模拟获取用户数据
async fn fetch_user_data(user_id: u32) -> Result<User> {
    // 模拟网络请求
    sleep(Duration::from_millis(100)).await;
    
    if user_id == 0 {
        return Err(anyhow::anyhow!("用户不存在"));
    }
    
    Ok(User {
        id: user_id,
        name: format!("用户{}", user_id),
    })
}

/// 安全处理数据
async fn process_data_safely(data: String) -> Result<ProcessedData> {
    // 模拟数据处理
    sleep(Duration::from_millis(50)).await;
    
    Ok(ProcessedData {
        original: data.clone(),
        processed: data.to_uppercase(),
        timestamp: std::time::SystemTime::now(),
    })
}

/// 长时间运行的操作
async fn long_running_operation() -> String {
    sleep(Duration::from_secs(2)).await;
    "长时间操作完成".to_string()
}

/// 异步任务
async fn async_task(name: &str, delay_ms: u64) -> String {
    sleep(Duration::from_millis(delay_ms)).await;
    format!("{}完成", name)
}

/// 风险操作（可能失败）
async fn risky_operation() -> Result<String> {
    sleep(Duration::from_millis(50)).await;
    
    if rand::random::<f32>() < 0.3 {
        Err(anyhow::anyhow!("随机失败"))
    } else {
        Ok("操作成功".to_string())
    }
}

/// 健壮的操作
async fn robust_operation() -> Result<String> {
    // 使用重试机制
    for attempt in 1..=3 {
        match risky_operation().await {
            Ok(result) => return Ok(result),
            Err(e) if attempt == 3 => return Err(e),
            Err(_) => {
                println!("    重试第 {} 次", attempt);
                sleep(Duration::from_millis(100)).await;
            }
        }
    }
    unreachable!()
}

/// 链式操作
async fn chain_operations() -> Result<String> {
    let step1 = operation_step1().await?;
    let step2 = operation_step2(step1).await?;
    let step3 = operation_step3(step2).await?;
    Ok(step3)
}

/// 带上下文的操作
async fn operation_with_context() -> Result<String> {
    risky_operation().await
        .context("执行风险操作失败")?;
    Ok("操作成功".to_string())
}

/// 类型化错误处理
async fn typed_error_handling() -> Result<OperationResult, OperationError> {
    match risky_operation().await {
        Ok(_result) => Ok(OperationResult::Success(())),
        Err(_) => Err(OperationError::NetworkError("网络连接失败".to_string())),
    }
}

/// 高效处理单个项目
async fn process_item_efficiently(item: i32) -> i32 {
    sleep(Duration::from_millis(10)).await;
    item * 2
}

/// 昂贵的操作
async fn expensive_operation() -> String {
    sleep(Duration::from_millis(100)).await;
    "昂贵操作完成".to_string()
}

/// 操作步骤1
async fn operation_step1() -> Result<String> {
    sleep(Duration::from_millis(50)).await;
    Ok("步骤1完成".to_string())
}

/// 操作步骤2
async fn operation_step2(input: String) -> Result<String> {
    sleep(Duration::from_millis(50)).await;
    Ok(format!("步骤2完成: {}", input))
}

/// 操作步骤3
async fn operation_step3(input: String) -> Result<String> {
    sleep(Duration::from_millis(50)).await;
    Ok(format!("步骤3完成: {}", input))
}

/// 管理资源结构体
struct ManagedResource {
    name: String,
}

impl ManagedResource {
    async fn new(name: &str) -> Result<Self> {
        sleep(Duration::from_millis(10)).await; // 模拟初始化
        println!("    创建资源: {}", name);
        Ok(Self {
            name: name.to_string(),
        })
    }

    async fn do_work(&self) -> Result<()> {
        sleep(Duration::from_millis(50)).await;
        println!("    资源 {} 执行工作", self.name);
        Ok(())
    }
}

impl Drop for ManagedResource {
    fn drop(&mut self) {
        println!("    清理资源: {}", self.name);
    }
}

// 数据结构和错误类型
#[allow(dead_code)]
#[derive(Debug)]
struct User {
    id: u32,
    name: String,
}

#[allow(dead_code)]
#[derive(Debug)]
struct ProcessedData {
    original: String,
    processed: String,
    timestamp: std::time::SystemTime,
}

#[allow(dead_code)]
#[derive(Debug)]
enum OperationResult {
    Success(()),
    Failure(String),
}

#[allow(dead_code)]
#[derive(Debug)]
enum OperationError {
    NetworkError(String),
    ParseError(String),
    BusinessError(String),
}

#[allow(dead_code)]
impl std::fmt::Display for OperationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            OperationError::NetworkError(msg) => write!(f, "网络错误: {}", msg),
            OperationError::ParseError(msg) => write!(f, "解析错误: {}", msg),
            OperationError::BusinessError(msg) => write!(f, "业务错误: {}", msg),
        }
    }
}

#[allow(dead_code)]
impl std::error::Error for OperationError {}
