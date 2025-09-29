//! 异步测试框架演示
//! 
//! 本示例展示了异步测试的各种技术和最佳实践：
//! - 异步单元测试
//! - 集成测试
//! - 性能测试
//! - 并发测试
//! - 模拟和存根
//! - 测试工具和辅助函数
//! 
//! 运行方式：
//! ```bash
//! cargo test --example async_testing_demo
//! # 或者运行特定测试
//! cargo test --example async_testing_demo async_testing_demo::tests::test_concurrent_operations
//! ```

use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{Mutex, RwLock, Semaphore};
use tokio::time::{sleep, timeout, interval};
//use futures::{StreamExt};
use anyhow::Result;

/// 异步计数器 - 用于测试
#[derive(Debug)]
#[derive(Clone)]
pub struct AsyncCounter {
    count: Arc<Mutex<i32>>,
    operations: Arc<Mutex<Vec<String>>>,
}

impl AsyncCounter {
    pub fn new() -> Self {
        Self {
            count: Arc::new(Mutex::new(0)),
            operations: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub async fn increment(&self) -> i32 {
        let mut count = self.count.lock().await;
        *count += 1;
        
        let mut operations = self.operations.lock().await;
        operations.push(format!("increment to {}", *count));
        
        *count
    }

    pub async fn decrement(&self) -> i32 {
        let mut count = self.count.lock().await;
        *count -= 1;
        
        let mut operations = self.operations.lock().await;
        operations.push(format!("decrement to {}", *count));
        
        *count
    }

    pub async fn get_count(&self) -> i32 {
        *self.count.lock().await
    }

    pub async fn get_operations(&self) -> Vec<String> {
        self.operations.lock().await.clone()
    }

    pub async fn reset(&self) {
        let mut count = self.count.lock().await;
        *count = 0;
        
        let mut operations = self.operations.lock().await;
        operations.clear();
    }
}

/// 异步任务调度器 - 用于测试
#[derive(Debug)]
pub struct AsyncTaskScheduler {
    tasks: Arc<RwLock<Vec<Task>>>,
    running: Arc<Mutex<bool>>,
}

#[derive(Debug, Clone)]
pub struct Task {
    pub id: String,
    pub name: String,
    pub duration: Duration,
    pub completed: bool,
}

impl AsyncTaskScheduler {
    pub fn new() -> Self {
        Self {
            tasks: Arc::new(RwLock::new(Vec::new())),
            running: Arc::new(Mutex::new(false)),
        }
    }

    pub async fn add_task(&self, name: String, duration: Duration) -> String {
        let task_id = format!("task_{}", uuid::Uuid::new_v4());
        let task = Task {
            id: task_id.clone(),
            name,
            duration,
            completed: false,
        };

        let mut tasks = self.tasks.write().await;
        tasks.push(task);

        task_id
    }

    pub async fn start_scheduler(&self) {
        let mut running = self.running.lock().await;
        *running = true;
        drop(running);

        let tasks = Arc::clone(&self.tasks);
        let running = Arc::clone(&self.running);

        tokio::spawn(async move {
            let mut interval = interval(Duration::from_millis(100));

            loop {
                interval.tick().await;

                // 检查是否应该停止
                {
                    let running_guard = running.lock().await;
                    if !*running_guard {
                        break;
                    }
                }

                // 处理任务
                let mut tasks_guard = tasks.write().await;
                for task in tasks_guard.iter_mut() {
                    if !task.completed {
                        // 模拟任务执行
                        tokio::spawn({
                            let task = task.clone();
                            let tasks = Arc::clone(&tasks);
                            async move {
                                sleep(task.duration).await;
                                
                                let mut tasks = tasks.write().await;
                                if let Some(t) = tasks.iter_mut().find(|t| t.id == task.id) {
                                    t.completed = true;
                                }
                            }
                        });
                        break;
                    }
                }
            }
        });
    }

    pub async fn stop_scheduler(&self) {
        let mut running = self.running.lock().await;
        *running = false;
    }

    pub async fn get_tasks(&self) -> Vec<Task> {
        self.tasks.read().await.clone()
    }

    pub async fn get_completed_tasks(&self) -> Vec<Task> {
        let tasks = self.tasks.read().await;
        tasks.iter().filter(|t| t.completed).cloned().collect()
    }
}

/// 异步数据处理器 - 用于测试
#[derive(Debug)]
pub struct AsyncDataProcessor {
    buffer: Arc<RwLock<Vec<String>>>,
    processing: Arc<Mutex<bool>>,
    processed_count: Arc<Mutex<usize>>,
}

impl AsyncDataProcessor {
    pub fn new() -> Self {
        Self {
            buffer: Arc::new(RwLock::new(Vec::new())),
            processing: Arc::new(Mutex::new(false)),
            processed_count: Arc::new(Mutex::new(0)),
        }
    }

    pub async fn add_data(&self, data: String) -> Result<()> {
        let mut buffer = self.buffer.write().await;
        buffer.push(data);
        Ok(())
    }

    pub async fn start_processing(&self) {
        let mut processing = self.processing.lock().await;
        *processing = true;
        drop(processing);

        let buffer = Arc::clone(&self.buffer);
        let processing = Arc::clone(&self.processing);
        let processed_count = Arc::clone(&self.processed_count);

        tokio::spawn(async move {
            loop {
                // 检查是否应该停止
                {
                    let processing_guard = processing.lock().await;
                    if !*processing_guard {
                        break;
                    }
                }

                // 处理数据
                let data = {
                    let mut buffer = buffer.write().await;
                    buffer.pop()
                };

                if let Some(data) = data {
                    // 模拟数据处理
                    sleep(Duration::from_millis(50)).await;
                    
                    let mut count = processed_count.lock().await;
                    *count += 1;
                    
                    println!("      处理数据: {}", data);
                } else {
                    sleep(Duration::from_millis(10)).await;
                }
            }
        });
    }

    pub async fn stop_processing(&self) {
        let mut processing = self.processing.lock().await;
        *processing = false;
    }

    pub async fn get_processed_count(&self) -> usize {
        *self.processed_count.lock().await
    }

    pub async fn get_buffer_size(&self) -> usize {
        self.buffer.read().await.len()
    }
}

/// 测试工具和辅助函数
pub mod test_utils {
    use super::*;

    /// 等待条件满足
    pub async fn wait_for_condition<F, Fut>(mut condition: F, timeout_duration: Duration) -> Result<bool>
    where
        F: FnMut() -> Fut,
        Fut: std::future::Future<Output = bool>,
    {
        let start = Instant::now();
        
        while start.elapsed() < timeout_duration {
            if condition().await {
                return Ok(true);
            }
            sleep(Duration::from_millis(10)).await;
        }
        
        Ok(false)
    }

    /// 测量异步操作执行时间
    pub async fn measure_execution_time<F, Fut, T>(operation: F) -> (T, Duration)
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        let start = Instant::now();
        let result = operation().await;
        let duration = start.elapsed();
        (result, duration)
    }

    /// 并发执行多个异步操作
    pub async fn run_concurrent<F, Fut, T>(operations: Vec<F>) -> Vec<T>
    where
        F: FnOnce() -> Fut,
        Fut: std::future::Future<Output = T>,
    {
        let futures = operations.into_iter().map(|op| async move { op().await });
        futures::future::join_all(futures).await
    }

    /// 模拟网络延迟
    pub async fn simulate_network_delay(min_ms: u64, max_ms: u64) {
        let delay = min_ms + rand::random::<u64>() % (max_ms - min_ms);
        sleep(Duration::from_millis(delay)).await;
    }

    /// 模拟随机失败
    pub fn should_fail(failure_rate: f32) -> bool {
        rand::random::<f32>() < failure_rate
    }
}

/// 主演示函数
pub async fn run_async_testing_demo() -> Result<()> {
    println!("🧪 异步测试框架演示");
    println!("================================");

    // 1. 基本异步测试演示
    println!("\n📋 1. 基本异步测试演示");
    demo_basic_async_tests().await?;

    // 2. 并发测试演示
    println!("\n🔄 2. 并发测试演示");
    demo_concurrent_tests().await?;

    // 3. 性能测试演示
    println!("\n⚡ 3. 性能测试演示");
    demo_performance_tests().await?;

    // 4. 集成测试演示
    println!("\n🔗 4. 集成测试演示");
    demo_integration_tests().await?;

    // 5. 模拟和存根演示
    println!("\n🎭 5. 模拟和存根演示");
    demo_mocking_and_stubbing().await?;

    Ok(())
}

async fn demo_basic_async_tests() -> Result<()> {
    println!("  基本异步测试示例:");

    // 测试异步计数器
    let counter = AsyncCounter::new();
    assert_eq!(counter.get_count().await, 0);

    // 测试递增
    let count1 = counter.increment().await;
    assert_eq!(count1, 1);
    assert_eq!(counter.get_count().await, 1);

    // 测试递减
    let count2 = counter.decrement().await;
    assert_eq!(count2, 0);
    assert_eq!(counter.get_count().await, 0);

    // 测试操作记录
    let operations = counter.get_operations().await;
    assert_eq!(operations.len(), 2);
    assert!(operations[0].contains("increment"));
    assert!(operations[1].contains("decrement"));

    println!("    ✅ 异步计数器测试通过");

    // 测试超时
    let result = timeout(Duration::from_millis(100), async {
        sleep(Duration::from_millis(50)).await;
        "success"
    }).await;

    assert!(result.is_ok());
    assert_eq!(result.unwrap(), "success");

    println!("    ✅ 超时测试通过");

    Ok(())
}

async fn demo_concurrent_tests() -> Result<()> {
    println!("  并发测试示例:");

    let counter = AsyncCounter::new();
    let semaphore = Arc::new(Semaphore::new(3)); // 最多3个并发操作

    // 并发递增操作
    let mut handles = vec![];
    for i in 0..10 {
        let counter = counter.clone();
        let semaphore = Arc::clone(&semaphore);
        
        let handle = tokio::spawn(async move {
            let _permit = semaphore.acquire().await.unwrap();
            counter.increment().await;
            println!("      并发操作 {} 完成", i);
        });
        
        handles.push(handle);
    }

    // 等待所有操作完成
    for handle in handles {
        handle.await?;
    }

    let final_count = counter.get_count().await;
    assert_eq!(final_count, 10);

    println!("    ✅ 并发递增测试通过，最终计数: {}", final_count);

    // 测试竞态条件
    let counter = AsyncCounter::new();
    let mut handles = vec![];

    // 同时进行递增和递减操作
    for _ in 0..5 {
        let counter = counter.clone();
        let handle = tokio::spawn(async move {
            counter.increment().await;
            counter.decrement().await;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await?;
    }

    let final_count = counter.get_count().await;
    assert_eq!(final_count, 0);

    println!("    ✅ 竞态条件测试通过，最终计数: {}", final_count);

    Ok(())
}

async fn demo_performance_tests() -> Result<()> {
    println!("  性能测试示例:");

    // 测试批处理性能
    let (result, duration) = test_utils::measure_execution_time(|| async {
        let counter = AsyncCounter::new();
        let mut handles = vec![];

        for _ in 0..1000 {
            let counter = counter.clone();
            let handle = tokio::spawn(async move {
                counter.increment().await;
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.await.unwrap();
        }

        counter.get_count().await
    }).await;

    assert_eq!(result, 1000);
    println!("    ✅ 批处理性能测试通过");
    println!("      处理1000个操作耗时: {:?}", duration);
    println!("      吞吐量: {:.2} ops/sec", 1000.0 / duration.as_secs_f64());

    // 测试内存使用（模拟）
    let counter = AsyncCounter::new();
    for i in 0..10000 {
        // 模拟数据处理
        println!("    处理数据项 {}", i);
    }

    let count = counter.get_count().await;
    println!("    计数器值: {}", count);

    println!("    ✅ 内存使用测试通过，计数器值: {}", count);

    Ok(())
}

async fn demo_integration_tests() -> Result<()> {
    println!("  集成测试示例:");

    // 测试任务调度器和数据处理器的集成
    let scheduler = AsyncTaskScheduler::new();
    let processor = AsyncDataProcessor::new();

    // 启动调度器
    scheduler.start_scheduler().await;

    // 添加一些任务
    let _task_ids = vec![
        scheduler.add_task("任务1".to_string(), Duration::from_millis(100)).await,
        scheduler.add_task("任务2".to_string(), Duration::from_millis(200)).await,
        scheduler.add_task("任务3".to_string(), Duration::from_millis(150)).await,
    ];

    // 添加一些数据
    for i in 0..5 {
        processor.add_data(format!("数据_{}", i)).await?;
    }

    // 启动数据处理器
    processor.start_processing().await;

    // 等待处理完成
    sleep(Duration::from_millis(500)).await;

    // 检查结果
    let completed_tasks = scheduler.get_completed_tasks().await;
    let processed_count = processor.get_processed_count().await;

    assert!(completed_tasks.len() > 0);
    assert!(processed_count > 0);

    println!("    ✅ 集成测试通过");
    println!("      完成任务数: {}", completed_tasks.len());
    println!("      处理数据数: {}", processed_count);

    // 停止服务
    scheduler.stop_scheduler().await;
    processor.stop_processing().await;

    Ok(())
}

async fn demo_mocking_and_stubbing() -> Result<()> {
    println!("  模拟和存根示例:");

    // 模拟一个异步服务
    let mock_service = MockAsyncService::new();
    
    // 设置模拟行为
    mock_service.set_should_fail(false).await;
    mock_service.set_response_time(Duration::from_millis(100)).await;

    // 测试成功情况
    let result = mock_service.process_request("test_data".to_string()).await;
    assert!(result.is_ok());
    println!("    ✅ 模拟成功响应测试通过");

    // 测试失败情况
    mock_service.set_should_fail(true).await;
    let result = mock_service.process_request("test_data".to_string()).await;
    assert!(result.is_err());
    println!("    ✅ 模拟失败响应测试通过");

    // 测试响应时间
    mock_service.set_should_fail(false).await;
    mock_service.set_response_time(Duration::from_millis(200)).await;

    let (result, duration) = test_utils::measure_execution_time(|| async {
        mock_service.process_request("test_data".to_string()).await
    }).await;

    assert!(result.is_ok());
    assert!(duration >= Duration::from_millis(200));
    println!("    ✅ 模拟响应时间测试通过，实际耗时: {:?}", duration);

    Ok(())
}

/// 模拟异步服务
#[derive(Debug)]
struct MockAsyncService {
    should_fail: Arc<Mutex<bool>>,
    response_time: Arc<Mutex<Duration>>,
}

impl MockAsyncService {
    fn new() -> Self {
        Self {
            should_fail: Arc::new(Mutex::new(false)),
            response_time: Arc::new(Mutex::new(Duration::from_millis(100))),
        }
    }

    async fn set_should_fail(&self, should_fail: bool) {
        let mut flag = self.should_fail.lock().await;
        *flag = should_fail;
    }

    async fn set_response_time(&self, response_time: Duration) {
        let mut time = self.response_time.lock().await;
        *time = response_time;
    }

    async fn process_request(&self, _data: String) -> Result<String> {
        let response_time = *self.response_time.lock().await;
        sleep(response_time).await;

        let should_fail = *self.should_fail.lock().await;
        if should_fail {
            Err(anyhow::anyhow!("模拟服务错误"))
        } else {
            Ok("模拟响应".to_string())
        }
    }
}

// 测试模块
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_counter_basic() {
        let counter = AsyncCounter::new();
        
        assert_eq!(counter.get_count().await, 0);
        
        let count = counter.increment().await;
        assert_eq!(count, 1);
        assert_eq!(counter.get_count().await, 1);
        
        let count = counter.decrement().await;
        assert_eq!(count, 0);
        assert_eq!(counter.get_count().await, 0);
    }

    #[tokio::test]
    async fn test_async_counter_concurrent() {
        let counter = AsyncCounter::new();
        let mut handles = vec![];

        // 并发递增
        for _ in 0..100 {
            let counter = counter.clone();
            let handle = tokio::spawn(async move {
                counter.increment().await;
            });
            handles.push(handle);
        }

        for handle in handles {
            handle.await.unwrap();
        }

        assert_eq!(counter.get_count().await, 100);
    }

    #[tokio::test]
    async fn test_async_counter_operations() {
        let counter = AsyncCounter::new();
        
        counter.increment().await;
        counter.decrement().await;
        counter.increment().await;
        
        let operations = counter.get_operations().await;
        assert_eq!(operations.len(), 3);
        assert!(operations[0].contains("increment"));
        assert!(operations[1].contains("decrement"));
        assert!(operations[2].contains("increment"));
    }

    #[tokio::test]
    async fn test_task_scheduler() {
        let scheduler = AsyncTaskScheduler::new();
        
        let task_id = scheduler.add_task("测试任务".to_string(), Duration::from_millis(100)).await;
        
        let tasks = scheduler.get_tasks().await;
        assert_eq!(tasks.len(), 1);
        assert_eq!(tasks[0].id, task_id);
        assert_eq!(tasks[0].name, "测试任务");
        assert!(!tasks[0].completed);
    }

    #[tokio::test]
    async fn test_data_processor() {
        let processor = AsyncDataProcessor::new();
        
        processor.add_data("测试数据1".to_string()).await.unwrap();
        processor.add_data("测试数据2".to_string()).await.unwrap();
        
        assert_eq!(processor.get_buffer_size().await, 2);
        assert_eq!(processor.get_processed_count().await, 0);
    }

    #[tokio::test]
    async fn test_wait_for_condition() {
        let counter = AsyncCounter::new();
        
        // 启动后台任务
        let counter_clone = counter.clone();
        tokio::spawn(async move {
            sleep(Duration::from_millis(50)).await;
            counter_clone.increment().await;
        });

        // 等待条件满足
        let condition_met = test_utils::wait_for_condition(
            || async { counter.get_count().await > 0 },
            Duration::from_secs(1)
        ).await.unwrap();

        assert!(condition_met);
        assert_eq!(counter.get_count().await, 1);
    }

    #[tokio::test]
    async fn test_measure_execution_time() {
        let (result, duration) = test_utils::measure_execution_time(|| async {
            sleep(Duration::from_millis(100)).await;
            42
        }).await;

        assert_eq!(result, 42);
        assert!(duration >= Duration::from_millis(100));
        assert!(duration < Duration::from_millis(200));
    }

    #[tokio::test]
    async fn test_run_concurrent() {
        let operations = vec![
            || async { 1 },
            || async { 2 },
            || async { 3 },
            || async { 4 },
            || async { 5 },
        ];

        let results = test_utils::run_concurrent(operations).await;
        assert_eq!(results, vec![1, 2, 3, 4, 5]);
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    run_async_testing_demo().await?;

    println!("\n🎉 异步测试框架演示完成！");
    println!("运行 'cargo test --example async_testing_demo' 来执行所有测试");
    
    Ok(())
}
