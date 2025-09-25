use anyhow::Result;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::{RwLock, Mutex};
use tokio::time::sleep;
use tracing::{info, warn, error};
use serde::{Deserialize, Serialize};

/// 2025年简化异步设计模式演示
/// 展示实用的异步编程模式和最佳实践

/// 1. 异步状态机模式
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum AsyncState {
    Idle,
    Loading,
    Ready,
    Processing,
    Error,
    Completed,
}

pub struct AsyncStateMachine {
    state: Arc<RwLock<AsyncState>>,
    transitions: Arc<Mutex<Vec<(AsyncState, AsyncState, String)>>>,
}

impl AsyncStateMachine {
    pub fn new(initial_state: AsyncState) -> Self {
        Self {
            state: Arc::new(RwLock::new(initial_state)),
            transitions: Arc::new(Mutex::new(Vec::new())),
        }
    }

    pub async fn transition(&self, from: AsyncState, to: AsyncState, reason: String) -> Result<()> {
        let current_state = self.state.read().await.clone();
        
        if current_state != from {
            return Err(anyhow::anyhow!("Invalid transition from {:?} to {:?}", current_state, to));
        }

        // 记录转换
        {
            let mut transitions = self.transitions.lock().await;
            transitions.push((from.clone(), to.clone(), reason));
        }

        // 执行状态转换
        {
            let mut state = self.state.write().await;
            *state = to.clone();
        }

        info!("状态转换: {:?} -> {:?}", from, to);
        Ok(())
    }

    pub async fn get_state(&self) -> AsyncState {
        self.state.read().await.clone()
    }

    pub async fn get_transitions(&self) -> Vec<(AsyncState, AsyncState, String)> {
        self.transitions.lock().await.clone()
    }
}

/// 2. 异步事件系统
pub struct AsyncEventSystem {
    subscribers: Arc<RwLock<Vec<String>>>,
    event_history: Arc<RwLock<Vec<String>>>,
}

impl AsyncEventSystem {
    pub fn new() -> Self {
        Self {
            subscribers: Arc::new(RwLock::new(Vec::new())),
            event_history: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub async fn subscribe(&self, subscriber: String) {
        self.subscribers.write().await.push(subscriber);
    }

    pub async fn publish(&self, event: String) -> Result<()> {
        let subscribers = self.subscribers.read().await;
        let mut history = self.event_history.write().await;
        
        info!("发布事件: {}", event);
        
        // 记录事件历史
        history.push(event.clone());
        
        // 通知所有订阅者
        for subscriber in subscribers.iter() {
            info!("通知订阅者 {}: {}", subscriber, event);
        }

        Ok(())
    }

    pub async fn get_event_count(&self) -> usize {
        self.event_history.read().await.len()
    }
}

/// 3. 异步命令模式（简化版）
pub struct AsyncCommandInvoker {
    history: Arc<RwLock<Vec<String>>>,
    current_index: Arc<RwLock<isize>>,
}

impl AsyncCommandInvoker {
    pub fn new() -> Self {
        Self {
            history: Arc::new(RwLock::new(Vec::new())),
            current_index: Arc::new(RwLock::new(-1)),
        }
    }

    pub async fn execute_command(&self, command: String) -> Result<()> {
        info!("执行命令: {}", command);
        
        // 模拟命令执行
        sleep(Duration::from_millis(50)).await;

        let mut history = self.history.write().await;
        let mut index = self.current_index.write().await;
        
        *index += 1;
        history.truncate(*index as usize);
        history.push(command);

        Ok(())
    }

    pub async fn undo(&self) -> Result<()> {
        let mut index = self.current_index.write().await;
        if *index >= 0 {
            let history = self.history.read().await;
            if let Some(command) = history.get(*index as usize) {
                info!("撤销命令: {}", command);
                *index -= 1;
                return Ok(());
            }
        }
        Err(anyhow::anyhow!("Nothing to undo"))
    }

    pub async fn redo(&self) -> Result<()> {
        let mut index = self.current_index.write().await;
        let history = self.history.read().await;
        
        if (*index + 1) < history.len() as isize {
            *index += 1;
            if let Some(command) = history.get(*index as usize) {
                info!("重做命令: {}", command);
                return Ok(());
            }
        }
        Err(anyhow::anyhow!("Nothing to redo"))
    }

    pub async fn can_undo(&self) -> bool {
        *self.current_index.read().await >= 0
    }

    pub async fn can_redo(&self) -> bool {
        let index = *self.current_index.read().await;
        let history_len = self.history.read().await.len();
        (index + 1) < history_len as isize
    }
}

/// 4. 异步缓存系统
pub struct AsyncCache<K, V> {
    cache: Arc<RwLock<std::collections::HashMap<K, V>>>,
    hit_count: Arc<RwLock<u64>>,
    miss_count: Arc<RwLock<u64>>,
}

impl<K: Clone + std::hash::Hash + Eq + Send + Sync, V: Clone + Send + Sync> AsyncCache<K, V> {
    pub fn new() -> Self {
        Self {
            cache: Arc::new(RwLock::new(std::collections::HashMap::new())),
            hit_count: Arc::new(RwLock::new(0)),
            miss_count: Arc::new(RwLock::new(0)),
        }
    }

    pub async fn get(&self, key: &K) -> Option<V> {
        let cache = self.cache.read().await;
        match cache.get(key) {
            Some(value) => {
                *self.hit_count.write().await += 1;
                Some(value.clone())
            }
            None => {
                *self.miss_count.write().await += 1;
                None
            }
        }
    }

    pub async fn set(&self, key: K, value: V) {
        self.cache.write().await.insert(key, value);
    }

    pub async fn hit_rate(&self) -> f64 {
        let hits = *self.hit_count.read().await;
        let misses = *self.miss_count.read().await;
        
        if hits + misses == 0 {
            0.0
        } else {
            hits as f64 / (hits + misses) as f64
        }
    }
}

/// 5. 异步任务调度器
pub struct AsyncTaskScheduler {
    tasks: Arc<RwLock<Vec<String>>>,
    completed_tasks: Arc<RwLock<Vec<String>>>,
    max_concurrent: usize,
    current_running: Arc<RwLock<usize>>,
}

impl AsyncTaskScheduler {
    pub fn new(max_concurrent: usize) -> Self {
        Self {
            tasks: Arc::new(RwLock::new(Vec::new())),
            completed_tasks: Arc::new(RwLock::new(Vec::new())),
            max_concurrent,
            current_running: Arc::new(RwLock::new(0)),
        }
    }

    pub async fn add_task(&self, task: String) {
        self.tasks.write().await.push(task);
    }

    pub async fn execute_task(&self, task: String) -> Result<()> {
        // 检查是否超过最大并发数
        {
            let current = *self.current_running.read().await;
            if current >= self.max_concurrent {
                return Err(anyhow::anyhow!("Maximum concurrent tasks reached"));
            }
        }

        // 增加运行计数
        *self.current_running.write().await += 1;

        info!("开始执行任务: {}", task);
        
        // 模拟任务执行
        sleep(Duration::from_millis(100)).await;
        
        info!("任务完成: {}", task);

        // 减少运行计数并记录完成的任务
        *self.current_running.write().await -= 1;
        self.completed_tasks.write().await.push(task);

        Ok(())
    }

    pub async fn get_stats(&self) -> (usize, usize, usize) {
        let pending = self.tasks.read().await.len();
        let completed = self.completed_tasks.read().await.len();
        let running = *self.current_running.read().await;
        (pending, running, completed)
    }
}

/// 6. 异步重试机制
pub struct AsyncRetryManager {
    max_attempts: u32,
    base_delay: Duration,
}

impl AsyncRetryManager {
    pub fn new(max_attempts: u32, base_delay: Duration) -> Self {
        Self {
            max_attempts,
            base_delay,
        }
    }

    pub async fn execute_with_retry<F, T>(&self, mut operation: F) -> Result<T>
    where
        F: FnMut() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<T>> + Send>>,
    {
        let mut last_error = None;
        
        for attempt in 1..=self.max_attempts {
            match operation().await {
                Ok(result) => {
                    if attempt > 1 {
                        info!("操作在第 {} 次尝试后成功", attempt);
                    }
                    return Ok(result);
                }
                Err(e) => {
                    last_error = Some(e);
                    if attempt < self.max_attempts {
                        let delay = self.base_delay * attempt;
                        warn!("操作失败，第 {} 次尝试，{}ms 后重试", attempt, delay.as_millis());
                        sleep(delay).await;
                    }
                }
            }
        }

        Err(last_error.unwrap())
    }
}

/// 7. 异步限流器
pub struct AsyncRateLimiter {
    max_requests: u32,
    time_window: Duration,
    requests: Arc<RwLock<Vec<Instant>>>,
}

impl AsyncRateLimiter {
    pub fn new(max_requests: u32, time_window: Duration) -> Self {
        Self {
            max_requests,
            time_window,
            requests: Arc::new(RwLock::new(Vec::new())),
        }
    }

    pub async fn allow_request(&self) -> bool {
        let now = Instant::now();
        let mut requests = self.requests.write().await;
        
        // 清理过期的请求记录
        requests.retain(|&time| now.duration_since(time) < self.time_window);
        
        if requests.len() < self.max_requests as usize {
            requests.push(now);
            true
        } else {
            false
        }
    }

    pub async fn wait_for_slot(&self) -> Result<()> {
        while !self.allow_request().await {
            sleep(Duration::from_millis(10)).await;
        }
        Ok(())
    }
}

/// 8. 异步健康检查系统
pub struct AsyncHealthChecker {
    checks: Arc<RwLock<Vec<HealthCheck>>>,
    last_check: Arc<RwLock<Option<Instant>>>,
}

#[derive(Debug, Clone)]
pub struct HealthCheck {
    name: String,
    status: HealthStatus,
    last_checked: Option<Instant>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

impl AsyncHealthChecker {
    pub fn new() -> Self {
        Self {
            checks: Arc::new(RwLock::new(Vec::new())),
            last_check: Arc::new(RwLock::new(None)),
        }
    }

    pub async fn add_check(&self, name: String) {
        let check = HealthCheck {
            name,
            status: HealthStatus::Unknown,
            last_checked: None,
        };
        self.checks.write().await.push(check);
    }

    pub async fn run_health_checks(&self) -> Result<()> {
        let now = Instant::now();
        let mut checks = self.checks.write().await;
        
        for check in checks.iter_mut() {
            // 模拟健康检查
            sleep(Duration::from_millis(10)).await;
            
            // 简单的随机健康状态（用于演示）
            let is_healthy = rand::random::<bool>();
            check.status = if is_healthy {
                HealthStatus::Healthy
            } else {
                HealthStatus::Unhealthy
            };
            check.last_checked = Some(now);
            
            info!("健康检查 '{}': {:?}", check.name, check.status);
        }

        *self.last_check.write().await = Some(now);
        Ok(())
    }

    pub async fn get_overall_health(&self) -> HealthStatus {
        let checks = self.checks.read().await;
        
        if checks.is_empty() {
            return HealthStatus::Unknown;
        }

        let unhealthy_count = checks.iter()
            .filter(|check| check.status == HealthStatus::Unhealthy)
            .count();

        if unhealthy_count == 0 {
            HealthStatus::Healthy
        } else if unhealthy_count == checks.len() {
            HealthStatus::Unhealthy
        } else {
            HealthStatus::Unhealthy // 任何不健康的检查都导致整体不健康
        }
    }
}

/// 演示所有简化的异步设计模式
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt()
        .with_env_filter("info")
        .init();

    info!("🚀 开始 2025 年简化异步设计模式演示");

    // 1. 异步状态机演示
    demo_async_state_machine().await?;

    // 2. 异步事件系统演示
    demo_async_event_system().await?;

    // 3. 异步命令模式演示
    demo_async_command_pattern().await?;

    // 4. 异步缓存演示
    demo_async_cache().await?;

    // 5. 异步任务调度器演示
    demo_async_task_scheduler().await?;

    // 6. 异步重试机制演示
    demo_async_retry_mechanism().await?;

    // 7. 异步限流器演示
    demo_async_rate_limiter().await?;

    // 8. 异步健康检查演示
    demo_async_health_checker().await?;

    info!("✅ 2025 年简化异步设计模式演示完成!");
    Ok(())
}

async fn demo_async_state_machine() -> Result<()> {
    info!("📊 演示异步状态机模式");

    let state_machine = AsyncStateMachine::new(AsyncState::Idle);

    // 执行状态转换
    state_machine.transition(AsyncState::Idle, AsyncState::Loading, "开始加载".to_string()).await?;
    sleep(Duration::from_millis(100)).await;
    
    state_machine.transition(AsyncState::Loading, AsyncState::Ready, "加载完成".to_string()).await?;
    sleep(Duration::from_millis(50)).await;
    
    state_machine.transition(AsyncState::Ready, AsyncState::Processing, "开始处理".to_string()).await?;
    sleep(Duration::from_millis(100)).await;
    
    state_machine.transition(AsyncState::Processing, AsyncState::Completed, "处理完成".to_string()).await?;

    let final_state = state_machine.get_state().await;
    let transitions = state_machine.get_transitions().await;
    
    info!("最终状态: {:?}", final_state);
    info!("状态转换历史: {:?}", transitions);

    Ok(())
}

async fn demo_async_event_system() -> Result<()> {
    info!("👀 演示异步事件系统");

    let event_system = AsyncEventSystem::new();
    
    // 添加订阅者
    event_system.subscribe("订阅者1".to_string()).await;
    event_system.subscribe("订阅者2".to_string()).await;
    event_system.subscribe("订阅者3".to_string()).await;

    // 发布事件
    event_system.publish("事件1".to_string()).await?;
    sleep(Duration::from_millis(50)).await;
    
    event_system.publish("事件2".to_string()).await?;
    sleep(Duration::from_millis(50)).await;
    
    event_system.publish("事件3".to_string()).await?;

    info!("总共发布了 {} 个事件", event_system.get_event_count().await);

    Ok(())
}

async fn demo_async_command_pattern() -> Result<()> {
    info!("📝 演示异步命令模式");

    let invoker = AsyncCommandInvoker::new();

    // 执行命令
    invoker.execute_command("创建文件".to_string()).await?;
    invoker.execute_command("写入数据".to_string()).await?;
    invoker.execute_command("保存文件".to_string()).await?;

    // 撤销命令
    if invoker.can_undo().await {
        invoker.undo().await?;
    }

    // 重做命令
    if invoker.can_redo().await {
        invoker.redo().await?;
    }

    Ok(())
}

async fn demo_async_cache() -> Result<()> {
    info!("💾 演示异步缓存系统");

    let cache = AsyncCache::new();

    // 填充缓存
    for i in 0..100 {
        cache.set(i, format!("值_{}", i)).await;
    }

    // 读取测试
    for i in 0..200 {
        cache.get(&i).await;
    }

    let hit_rate = cache.hit_rate().await;
    info!("缓存命中率: {:.2}%", hit_rate * 100.0);
    info!("预期命中率: 50% (100/200)");

    Ok(())
}

async fn demo_async_task_scheduler() -> Result<()> {
    info!("⚙️ 演示异步任务调度器");

    let scheduler = AsyncTaskScheduler::new(3);

    // 添加任务
    for i in 1..=10 {
        scheduler.add_task(format!("任务_{}", i)).await;
    }

    // 并发执行任务
    let mut handles = Vec::new();
    for i in 1..=10 {
        let scheduler = scheduler.clone();
        let handle = tokio::spawn(async move {
            scheduler.execute_task(format!("任务_{}", i)).await
        });
        handles.push(handle);
    }

    // 等待所有任务完成
    for handle in handles {
        if let Err(e) = handle.await? {
            error!("任务执行失败: {}", e);
        }
    }

    let (pending, running, completed) = scheduler.get_stats().await;
    info!("任务统计 - 待执行: {}, 运行中: {}, 已完成: {}", pending, running, completed);

    Ok(())
}

async fn demo_async_retry_mechanism() -> Result<()> {
    info!("🔄 演示异步重试机制");

    let retry_manager = AsyncRetryManager::new(3, Duration::from_millis(100));

    let mut attempt_count = 0;
    let result = retry_manager.execute_with_retry(|| {
        attempt_count += 1;
        Box::pin(async move {
            // 模拟可能失败的操作
            if attempt_count < 3 {
                Err(anyhow::anyhow!("模拟失败"))
            } else {
                Ok("操作成功".to_string())
            }
        })
    }).await?;

    info!("重试结果: {}", result);

    Ok(())
}

async fn demo_async_rate_limiter() -> Result<()> {
    info!("🚦 演示异步限流器");

    let rate_limiter = AsyncRateLimiter::new(5, Duration::from_secs(1));

    // 尝试发送多个请求
    for i in 1..=10 {
        if rate_limiter.allow_request().await {
            info!("请求 {} 被允许", i);
        } else {
            info!("请求 {} 被限流", i);
            rate_limiter.wait_for_slot().await?;
            info!("请求 {} 等待后通过", i);
        }
    }

    Ok(())
}

async fn demo_async_health_checker() -> Result<()> {
    info!("🏥 演示异步健康检查系统");

    let health_checker = AsyncHealthChecker::new();

    // 添加健康检查
    health_checker.add_check("数据库连接".to_string()).await;
    health_checker.add_check("Redis连接".to_string()).await;
    health_checker.add_check("外部API".to_string()).await;

    // 运行健康检查
    health_checker.run_health_checks().await?;

    let overall_health = health_checker.get_overall_health().await;
    info!("整体健康状态: {:?}", overall_health);

    Ok(())
}

impl Clone for AsyncTaskScheduler {
    fn clone(&self) -> Self {
        Self {
            tasks: self.tasks.clone(),
            completed_tasks: self.completed_tasks.clone(),
            max_concurrent: self.max_concurrent,
            current_running: self.current_running.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_async_state_machine() {
        let sm = AsyncStateMachine::new(AsyncState::Idle);
        assert_eq!(sm.get_state().await, AsyncState::Idle);
        
        sm.transition(AsyncState::Idle, AsyncState::Loading, "test".to_string()).await.unwrap();
        assert_eq!(sm.get_state().await, AsyncState::Loading);
    }

    #[tokio::test]
    async fn test_async_cache() {
        let cache = AsyncCache::new();
        cache.set("key".to_string(), "value".to_string()).await;
        
        assert_eq!(cache.get(&"key".to_string()).await, Some("value".to_string()));
        assert_eq!(cache.get(&"nonexistent".to_string()).await, None);
    }

    #[tokio::test]
    async fn test_async_rate_limiter() {
        let limiter = AsyncRateLimiter::new(2, Duration::from_millis(100));
        
        assert!(limiter.allow_request().await);
        assert!(limiter.allow_request().await);
        assert!(!limiter.allow_request().await); // 应该被限流
    }
}
