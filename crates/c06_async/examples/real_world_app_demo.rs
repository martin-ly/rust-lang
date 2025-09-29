//! 真实世界应用场景演示
//! 
//! 本示例展示了在真实世界应用中使用异步编程的场景：
//! - Web API 服务器
//! - 消息队列处理
//! - 文件上传和处理
//! - 定时任务调度
//! - 配置热重载
//! - 健康检查和监控
//! 
//! 运行方式：
//! ```bash
//! cargo run --example real_world_app_demo
//! ```

use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime};
use tokio::sync::{RwLock, Mutex, Notify};
use tokio::time::{sleep, interval};
use anyhow::Result;
use serde::{Serialize, Deserialize};
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Config {
    server_port: u16,
    database_url: String,
    max_connections: usize,
    log_level: String,
    features: HashMap<String, bool>,
}

impl Default for Config {
    fn default() -> Self {
        let mut features = HashMap::new();
        features.insert("caching".to_string(), true);
        features.insert("metrics".to_string(), true);
        features.insert("rate_limiting".to_string(), false);
        
        Self {
            server_port: 8080,
            database_url: "postgresql://localhost:5432/myapp".to_string(),
            max_connections: 100,
            log_level: "info".to_string(),
            features,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct User {
    id: Uuid,
    name: String,
    email: String,
    created_at: SystemTime,
    last_login: Option<SystemTime>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct Task {
    id: Uuid,
    user_id: Uuid,
    title: String,
    description: String,
    status: TaskStatus,
    created_at: SystemTime,
    updated_at: SystemTime,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum TaskStatus {
    Pending,
    InProgress,
    Completed,
    Cancelled,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct UploadRequest {
    id: Uuid,
    filename: String,
    size: u64,
    content_type: String,
    user_id: Uuid,
    created_at: SystemTime,
}

#[derive(Debug, Clone)]
struct ApplicationState {
    config: Arc<RwLock<Config>>,
    users: Arc<RwLock<HashMap<Uuid, User>>>,
    tasks: Arc<RwLock<HashMap<Uuid, Task>>>,
    uploads: Arc<RwLock<HashMap<Uuid, UploadRequest>>>,
    metrics: Arc<Mutex<ApplicationMetrics>>,
    shutdown_notify: Arc<Notify>,
}

#[derive(Debug)]
struct ApplicationMetrics {
    requests_total: u64,
    requests_success: u64,
    requests_failed: u64,
    active_connections: u64,
    cache_hits: u64,
    cache_misses: u64,
    start_time: Instant,
}

impl Default for ApplicationMetrics {
    fn default() -> Self {
        Self {
            requests_total: 0,
            requests_success: 0,
            requests_failed: 0,
            active_connections: 0,
            cache_hits: 0,
            cache_misses: 0,
            start_time: Instant::now(),
        }
    }
}

impl ApplicationState {
    fn new() -> Self {
        Self {
            config: Arc::new(RwLock::new(Config::default())),
            users: Arc::new(RwLock::new(HashMap::new())),
            tasks: Arc::new(RwLock::new(HashMap::new())),
            uploads: Arc::new(RwLock::new(HashMap::new())),
            metrics: Arc::new(Mutex::new(ApplicationMetrics::default())),
            shutdown_notify: Arc::new(Notify::new()),
        }
    }
}

struct RealWorldApp {
    state: ApplicationState,
    message_queue: Arc<Mutex<Vec<Message>>>,
    config_watcher: Arc<Notify>,
}

#[derive(Debug, Clone)]
enum Message {
    UserCreated(User),
    TaskUpdated(Task),
    FileUploaded(UploadRequest),
    SystemAlert(String),
}

impl RealWorldApp {
    fn new() -> Self {
        Self {
            state: ApplicationState::new(),
            message_queue: Arc::new(Mutex::new(Vec::new())),
            config_watcher: Arc::new(Notify::new()),
        }
    }

    async fn run(&self) -> Result<()> {
        println!("🌍 真实世界应用场景演示");
        println!("================================");

        // 启动各种服务
        let mut handles = vec![];

        // 1. Web API 服务器
        println!("\n🌐 1. Web API 服务器");
        let api_handle = self.start_api_server().await?;
        handles.push(api_handle);

        // 2. 消息队列处理器
        println!("\n📨 2. 消息队列处理器");
        let queue_handle = self.start_message_queue_processor().await?;
        handles.push(queue_handle);

        // 3. 文件上传处理器
        println!("\n📁 3. 文件上传处理器");
        let upload_handle = self.start_file_upload_processor().await?;
        handles.push(upload_handle);

        // 4. 定时任务调度器
        println!("\n⏰ 4. 定时任务调度器");
        let scheduler_handle = self.start_task_scheduler().await?;
        handles.push(scheduler_handle);

        // 5. 配置热重载
        println!("\n⚙️ 5. 配置热重载");
        let config_handle = self.start_config_watcher().await?;
        handles.push(config_handle);

        // 6. 健康检查和监控
        println!("\n🏥 6. 健康检查和监控");
        let health_handle = self.start_health_monitor().await?;
        handles.push(health_handle);

        // 模拟一些用户活动
        self.simulate_user_activity().await?;

        // 运行一段时间后关闭
        sleep(Duration::from_secs(10)).await;
        println!("\n🛑 发送关闭信号...");
        self.state.shutdown_notify.notify_waiters();

        // 等待所有服务关闭
        for handle in handles {
            handle.await?;
        }

        // 显示最终统计
        self.print_final_statistics().await;

        Ok(())
    }

    async fn start_api_server(&self) -> Result<tokio::task::JoinHandle<()>> {
        let state = self.state.clone();
        let message_queue = Arc::clone(&self.message_queue);
        let shutdown = Arc::clone(&self.state.shutdown_notify);

        let handle = tokio::spawn(async move {
            println!("    🚀 API 服务器启动在端口 8080");
            
            let mut request_count = 0;
            let mut interval = interval(Duration::from_secs(1));
            
            loop {
                tokio::select! {
                    _ = interval.tick() => {
                        request_count += 1;
                        println!("      📡 处理 API 请求 #{}", request_count);
                        
                        // 模拟API请求处理
                        Self::handle_api_request(&state, &message_queue, request_count).await;
                        
                        // 更新指标
                        {
                            let mut metrics = state.metrics.lock().await;
                            metrics.requests_total += 1;
                            if request_count % 10 != 0 {
                                metrics.requests_success += 1;
                            } else {
                                metrics.requests_failed += 1;
                            }
                        }
                    }
                    _ = shutdown.notified() => {
                        println!("      🛑 API 服务器关闭");
                        break;
                    }
                }
            }
        });

        Ok(handle)
    }

    async fn handle_api_request(
        state: &ApplicationState,
        message_queue: &Arc<Mutex<Vec<Message>>>,
        request_id: u64,
    ) {
        match request_id % 4 {
            0 => {
                // 创建用户
                let user = User {
                    id: Uuid::new_v4(),
                    name: format!("用户 {}", request_id),
                    email: format!("user{}@example.com", request_id),
                    created_at: SystemTime::now(),
                    last_login: None,
                };
                
                {
                    let mut users = state.users.write().await;
                    users.insert(user.id, user.clone());
                }
                
                let mut queue = message_queue.lock().await;
                queue.push(Message::UserCreated(user));
            }
            1 => {
                // 创建任务
                let task = Task {
                    id: Uuid::new_v4(),
                    user_id: Uuid::new_v4(),
                    title: format!("任务 {}", request_id),
                    description: format!("任务描述 {}", request_id),
                    status: TaskStatus::Pending,
                    created_at: SystemTime::now(),
                    updated_at: SystemTime::now(),
                };
                
                {
                    let mut tasks = state.tasks.write().await;
                    tasks.insert(task.id, task.clone());
                }
                
                let mut queue = message_queue.lock().await;
                queue.push(Message::TaskUpdated(task));
            }
            2 => {
                // 文件上传请求
                let upload = UploadRequest {
                    id: Uuid::new_v4(),
                    filename: format!("file_{}.txt", request_id),
                    size: 1024 * (request_id % 100) as u64,
                    content_type: "text/plain".to_string(),
                    user_id: Uuid::new_v4(),
                    created_at: SystemTime::now(),
                };
                
                {
                    let mut uploads = state.uploads.write().await;
                    uploads.insert(upload.id, upload.clone());
                }
                
                let mut queue = message_queue.lock().await;
                queue.push(Message::FileUploaded(upload));
            }
            _ => {
                // 系统告警
                let alert = format!("系统告警: 请求 #{} 处理异常", request_id);
                let mut queue = message_queue.lock().await;
                queue.push(Message::SystemAlert(alert));
            }
        }
    }

    async fn start_message_queue_processor(&self) -> Result<tokio::task::JoinHandle<()>> {
        let message_queue = Arc::clone(&self.message_queue);
        let shutdown = Arc::clone(&self.state.shutdown_notify);

        let handle = tokio::spawn(async move {
            println!("    📨 消息队列处理器启动");
            
            let mut processed_count = 0;
            
            loop {
                tokio::select! {
                    _ = sleep(Duration::from_millis(500)) => {
                        let mut queue = message_queue.lock().await;
                        if let Some(message) = queue.pop() {
                            processed_count += 1;
                            Self::process_message(message, processed_count).await;
                        }
                    }
                    _ = shutdown.notified() => {
                        println!("      🛑 消息队列处理器关闭，共处理 {} 条消息", processed_count);
                        break;
                    }
                }
            }
        });

        Ok(handle)
    }

    async fn process_message(message: Message, count: u64) {
        match message {
            Message::UserCreated(user) => {
                println!("      👤 处理用户创建消息 #{}: {}", count, user.name);
                // 模拟异步处理：发送欢迎邮件、创建用户目录等
                sleep(Duration::from_millis(100)).await;
            }
            Message::TaskUpdated(task) => {
                println!("      📝 处理任务更新消息 #{}: {}", count, task.title);
                // 模拟异步处理：通知相关人员、更新索引等
                sleep(Duration::from_millis(150)).await;
            }
            Message::FileUploaded(upload) => {
                println!("      📁 处理文件上传消息 #{}: {} ({} 字节)", 
                    count, upload.filename, upload.size);
                // 模拟异步处理：病毒扫描、缩略图生成等
                sleep(Duration::from_millis(200)).await;
            }
            Message::SystemAlert(alert) => {
                println!("      🚨 处理系统告警消息 #{}: {}", count, alert);
                // 模拟异步处理：发送通知、记录日志等
                sleep(Duration::from_millis(50)).await;
            }
        }
    }

    async fn start_file_upload_processor(&self) -> Result<tokio::task::JoinHandle<()>> {
        let uploads = Arc::clone(&self.state.uploads);
        let shutdown = Arc::clone(&self.state.shutdown_notify);

        let handle = tokio::spawn(async move {
            println!("    📁 文件上传处理器启动");
            
            let mut processed_uploads = 0;
            let mut interval = interval(Duration::from_secs(2));
            
            loop {
                tokio::select! {
                    _ = interval.tick() => {
                        let mut uploads_map = uploads.write().await;
                        if let Some((id, upload)) = uploads_map.iter().next().map(|(k, v)| (*k, v.clone())) {
                            uploads_map.remove(&id);
                            processed_uploads += 1;
                            println!("      📤 处理文件上传 #{}: {}", processed_uploads, upload.filename);
                            
                            // 模拟文件处理
                            Self::process_file_upload(upload).await;
                        }
                    }
                    _ = shutdown.notified() => {
                        println!("      🛑 文件上传处理器关闭，共处理 {} 个文件", processed_uploads);
                        break;
                    }
                }
            }
        });

        Ok(handle)
    }

    async fn process_file_upload(upload: UploadRequest) {
        // 模拟文件处理步骤
        println!("        🔍 病毒扫描: {}", upload.filename);
        sleep(Duration::from_millis(100)).await;
        
        println!("        🖼️ 生成缩略图: {}", upload.filename);
        sleep(Duration::from_millis(200)).await;
        
        println!("        💾 存储到云存储: {}", upload.filename);
        sleep(Duration::from_millis(150)).await;
        
        println!("        ✅ 文件处理完成: {}", upload.filename);
    }

    async fn start_task_scheduler(&self) -> Result<tokio::task::JoinHandle<()>> {
        let tasks = Arc::clone(&self.state.tasks);
        let shutdown = Arc::clone(&self.state.shutdown_notify);

        let handle = tokio::spawn(async move {
            println!("    ⏰ 定时任务调度器启动");
            
            let mut scheduled_tasks = 0;
            let mut interval = interval(Duration::from_secs(3));
            
            loop {
                tokio::select! {
                    _ = interval.tick() => {
                        scheduled_tasks += 1;
                        println!("      ⏰ 执行定时任务 #{}", scheduled_tasks);
                        
                        // 模拟定时任务
                        Self::execute_scheduled_task(&tasks, scheduled_tasks).await;
                    }
                    _ = shutdown.notified() => {
                        println!("      🛑 定时任务调度器关闭，共执行 {} 个任务", scheduled_tasks);
                        break;
                    }
                }
            }
        });

        Ok(handle)
    }

    async fn execute_scheduled_task(_tasks: &Arc<RwLock<HashMap<Uuid, Task>>>, task_id: u64) {
        match task_id % 3 {
            0 => {
                println!("        🧹 清理过期任务");
                sleep(Duration::from_millis(100)).await;
            }
            1 => {
                println!("        📊 生成统计报告");
                sleep(Duration::from_millis(200)).await;
            }
            _ => {
                println!("        🔄 同步外部数据");
                sleep(Duration::from_millis(150)).await;
            }
        }
    }

    async fn start_config_watcher(&self) -> Result<tokio::task::JoinHandle<()>> {
        let config = Arc::clone(&self.state.config);
        let config_watcher = Arc::clone(&self.config_watcher);
        let shutdown = Arc::clone(&self.state.shutdown_notify);

        let handle = tokio::spawn(async move {
            println!("    ⚙️ 配置热重载启动");
            
            let mut reload_count = 0;
            let mut interval = interval(Duration::from_secs(5));
            
            loop {
                tokio::select! {
                    _ = interval.tick() => {
                        // 模拟配置文件变化
                        if rand::random::<f32>() < 0.3 {
                            reload_count += 1;
                            println!("      🔄 检测到配置变化，重新加载 #{}", reload_count);
                            
                            Self::reload_config(&config).await;
                            config_watcher.notify_waiters();
                        }
                    }
                    _ = shutdown.notified() => {
                        println!("      🛑 配置热重载关闭，共重载 {} 次", reload_count);
                        break;
                    }
                }
            }
        });

        Ok(handle)
    }

    async fn reload_config(config: &Arc<RwLock<Config>>) {
        let mut config_guard = config.write().await;
        
        // 模拟配置更新
        config_guard.log_level = if config_guard.log_level == "info" {
            "debug".to_string()
        } else {
            "info".to_string()
        };
        
        let current_rate_limiting = config_guard.features.get("rate_limiting").unwrap_or(&false);
        let new_rate_limiting = !current_rate_limiting;
        config_guard.features.insert("rate_limiting".to_string(), new_rate_limiting);
        println!("        ✅ 配置已更新: log_level={}, rate_limiting={}", 
            config_guard.log_level, 
            new_rate_limiting);
    }

    async fn start_health_monitor(&self) -> Result<tokio::task::JoinHandle<()>> {
        let metrics = Arc::clone(&self.state.metrics);
        let shutdown = Arc::clone(&self.state.shutdown_notify);

        let handle = tokio::spawn(async move {
            println!("    🏥 健康检查监控启动");
            
            let mut health_checks = 0;
            let mut interval = interval(Duration::from_secs(4));
            
            loop {
                tokio::select! {
                    _ = interval.tick() => {
                        health_checks += 1;
                        println!("      🏥 执行健康检查 #{}", health_checks);
                        
                        Self::perform_health_check(&metrics).await;
                    }
                    _ = shutdown.notified() => {
                        println!("      🛑 健康检查监控关闭，共执行 {} 次检查", health_checks);
                        break;
                    }
                }
            }
        });

        Ok(handle)
    }

    async fn perform_health_check(metrics: &Arc<Mutex<ApplicationMetrics>>) {
        let metrics_guard = metrics.lock().await;
        
        let uptime = metrics_guard.start_time.elapsed();
        let success_rate = if metrics_guard.requests_total > 0 {
            metrics_guard.requests_success as f64 / metrics_guard.requests_total as f64
        } else {
            1.0
        };
        
        let cache_hit_rate = if metrics_guard.cache_hits + metrics_guard.cache_misses > 0 {
            metrics_guard.cache_hits as f64 / (metrics_guard.cache_hits + metrics_guard.cache_misses) as f64
        } else {
            0.0
        };
        
        println!("        ✅ 系统健康状态:");
        println!("          运行时间: {:?}", uptime);
        println!("          请求成功率: {:.1}%", success_rate * 100.0);
        println!("          缓存命中率: {:.1}%", cache_hit_rate * 100.0);
        println!("          活跃连接: {}", metrics_guard.active_connections);
        
        // 模拟健康检查
        sleep(Duration::from_millis(50)).await;
    }

    async fn simulate_user_activity(&self) -> Result<()> {
        println!("\n👥 模拟用户活动");
        
        // 模拟用户注册
        for i in 0..5 {
            let user = User {
                id: Uuid::new_v4(),
                name: format!("模拟用户 {}", i),
                email: format!("simuser{}@example.com", i),
                created_at: SystemTime::now(),
                last_login: None,
            };
            
            {
                let mut users = self.state.users.write().await;
                users.insert(user.id, user.clone());
            }
            
            let mut queue = self.message_queue.lock().await;
            queue.push(Message::UserCreated(user));
            
            println!("  👤 模拟用户注册: 用户 {}", i);
            sleep(Duration::from_millis(200)).await;
        }
        
        // 模拟任务创建
        for i in 0..3 {
            let task = Task {
                id: Uuid::new_v4(),
                user_id: Uuid::new_v4(),
                title: format!("模拟任务 {}", i),
                description: format!("这是一个模拟任务 {}", i),
                status: TaskStatus::Pending,
                created_at: SystemTime::now(),
                updated_at: SystemTime::now(),
            };
            
            {
                let mut tasks = self.state.tasks.write().await;
                tasks.insert(task.id, task.clone());
            }
            
            let mut queue = self.message_queue.lock().await;
            queue.push(Message::TaskUpdated(task));
            
            println!("  📝 模拟任务创建: 任务 {}", i);
            sleep(Duration::from_millis(300)).await;
        }
        
        Ok(())
    }

    async fn print_final_statistics(&self) {
        println!("\n📊 最终统计信息");
        println!("==================");
        
        let users_count = self.state.users.read().await.len();
        let tasks_count = self.state.tasks.read().await.len();
        let uploads_count = self.state.uploads.read().await.len();
        let messages_count = self.message_queue.lock().await.len();
        
        let metrics = self.state.metrics.lock().await;
        let uptime = metrics.start_time.elapsed();
        
        println!("  👥 用户数量: {}", users_count);
        println!("  📝 任务数量: {}", tasks_count);
        println!("  📁 上传数量: {}", uploads_count);
        println!("  📨 待处理消息: {}", messages_count);
        println!("  ⏱️ 运行时间: {:?}", uptime);
        println!("  📡 总请求数: {}", metrics.requests_total);
        println!("  ✅ 成功请求: {}", metrics.requests_success);
        println!("  ❌ 失败请求: {}", metrics.requests_failed);
        
        if metrics.requests_total > 0 {
            let success_rate = metrics.requests_success as f64 / metrics.requests_total as f64;
            println!("  📈 成功率: {:.1}%", success_rate * 100.0);
        }
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    let app = RealWorldApp::new();
    app.run().await?;

    println!("\n🎉 真实世界应用场景演示完成！");
    Ok(())
}
