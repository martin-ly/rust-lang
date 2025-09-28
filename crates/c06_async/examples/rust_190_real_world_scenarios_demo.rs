//! Rust 1.90 真实世界应用场景演示
//! 
//! 本程序展示了 Rust 1.90 异步特性在真实世界应用场景中的使用，
//! 包括高并发 Web 服务、实时数据处理、分布式系统等实际应用

use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use std::collections::HashMap;
use anyhow::Result;
use tokio::sync::{RwLock, Mutex, mpsc};
use tokio::time::sleep;
use tracing::{info, warn, error, debug};
use serde::{Deserialize, Serialize};

/// 用户会话信息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserSession {
    pub user_id: String,
    pub session_id: String,
    pub created_at: u64,
    pub last_activity: u64,
    pub ip_address: String,
    pub user_agent: String,
}

/// 实时消息
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RealtimeMessage {
    pub message_id: String,
    pub user_id: String,
    pub content: String,
    pub timestamp: u64,
    pub message_type: MessageType,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum MessageType {
    Text,
    Image,
    Video,
    System,
}

/// 高并发 Web 服务
pub struct HighConcurrencyWebService {
    sessions: Arc<RwLock<HashMap<String, UserSession>>>,
    active_connections: Arc<AtomicUsize>,
    message_channels: Arc<RwLock<HashMap<String, mpsc::UnboundedSender<RealtimeMessage>>>>,
    metrics: Arc<ServiceMetrics>,
}

impl HighConcurrencyWebService {
    pub fn new() -> Self {
        Self {
            sessions: Arc::new(RwLock::new(HashMap::new())),
            active_connections: Arc::new(AtomicUsize::new(0)),
            message_channels: Arc::new(RwLock::new(HashMap::new())),
            metrics: Arc::new(ServiceMetrics::new()),
        }
    }

    /// 用户登录
    pub async fn user_login(&self, user_id: String, ip_address: String, user_agent: String) -> Result<String> {
        let session_id = format!("session_{}_{}", user_id, SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs());
        let now = SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs();
        
        let session = UserSession {
            user_id: user_id.clone(),
            session_id: session_id.clone(),
            created_at: now,
            last_activity: now,
            ip_address,
            user_agent,
        };

        // 存储会话
        {
            let mut sessions = self.sessions.write().await;
            sessions.insert(session_id.clone(), session);
        }

        // 创建消息通道
        let (tx, mut rx) = mpsc::unbounded_channel();
        {
            let mut channels = self.message_channels.write().await;
            channels.insert(user_id.clone(), tx);
        }

        // 启动消息处理任务
        let user_id_clone = user_id.clone();
        let metrics = Arc::clone(&self.metrics);
        
        tokio::spawn(async move {
            while let Some(message) = rx.recv().await {
                // 处理实时消息
                metrics.increment_messages_processed().await;
                debug!("处理用户 {} 的消息: {}", user_id_clone, message.content);
            }
        });

        self.active_connections.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.metrics.increment_login_count().await;
        
        info!("用户 {} 登录成功，会话ID: {}", user_id, session_id);
        Ok(session_id)
    }

    /// 发送实时消息
    pub async fn send_realtime_message(&self, from_user: String, to_user: String, content: String, message_type: MessageType) -> Result<()> {
        let now = SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs();
        let message_id = format!("msg_{}_{}", from_user, now);
        
        let message = RealtimeMessage {
            message_id,
            user_id: from_user.clone(),
            content: content.clone(),
            timestamp: now,
            message_type,
        };

        // 查找目标用户的通道
        let channels = self.message_channels.read().await;
        if let Some(tx) = channels.get(&to_user) {
            if let Err(_) = tx.send(message) {
                warn!("发送消息到用户 {} 失败，通道已关闭", to_user);
                return Err(anyhow::anyhow!("用户离线"));
            }
            
            self.metrics.increment_messages_sent().await;
            info!("消息已发送: {} -> {}: {}", from_user, to_user, content);
        } else {
            warn!("用户 {} 不在线", to_user);
            return Err(anyhow::anyhow!("用户不在线"));
        }

        Ok(())
    }

    /// 用户登出
    pub async fn user_logout(&self, session_id: String) -> Result<()> {
        let _user_id = {
            let mut sessions = self.sessions.write().await;
            if let Some(session) = sessions.remove(&session_id) {
                let user_id = session.user_id.clone();
                self.active_connections.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
                
                // 关闭消息通道
                let mut channels = self.message_channels.write().await;
                channels.remove(&user_id);
                
                info!("用户 {} 登出，会话ID: {}", user_id, session_id);
                Ok(user_id)
            } else {
                Err(anyhow::anyhow!("会话不存在"))
            }
        }?;

        self.metrics.increment_logout_count().await;
        Ok(())
    }

    /// 获取服务统计
    pub async fn get_service_stats(&self) -> ServiceStats {
        let sessions = self.sessions.read().await;
        let channels = self.message_channels.read().await;
        
        ServiceStats {
            active_sessions: sessions.len(),
            active_connections: self.active_connections.load(std::sync::atomic::Ordering::Relaxed),
            active_channels: channels.len(),
            metrics: self.metrics.get_metrics().await,
        }
    }

    /// 清理过期会话
    pub async fn cleanup_expired_sessions(&self) -> Result<()> {
        let now = SystemTime::now().duration_since(UNIX_EPOCH)?.as_secs();
        let expiry_time = 3600; // 1小时过期

        let mut sessions = self.sessions.write().await;
        let mut channels = self.message_channels.write().await;
        
        let mut expired_sessions = Vec::new();
        
        for (session_id, session) in sessions.iter() {
            if now - session.last_activity > expiry_time {
                expired_sessions.push((session_id.clone(), session.user_id.clone()));
            }
        }

        for (session_id, user_id) in expired_sessions {
            sessions.remove(&session_id);
            channels.remove(&user_id);
            self.active_connections.fetch_sub(1, std::sync::atomic::Ordering::Relaxed);
            info!("清理过期会话: {}", session_id);
        }

        Ok(())
    }
}

/// 服务指标
pub struct ServiceMetrics {
    login_count: Arc<AtomicUsize>,
    logout_count: Arc<AtomicUsize>,
    messages_sent: Arc<AtomicUsize>,
    messages_processed: Arc<AtomicUsize>,
    errors: Arc<AtomicUsize>,
}

impl ServiceMetrics {
    pub fn new() -> Self {
        Self {
            login_count: Arc::new(AtomicUsize::new(0)),
            logout_count: Arc::new(AtomicUsize::new(0)),
            messages_sent: Arc::new(AtomicUsize::new(0)),
            messages_processed: Arc::new(AtomicUsize::new(0)),
            errors: Arc::new(AtomicUsize::new(0)),
        }
    }

    pub async fn increment_login_count(&self) {
        self.login_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    pub async fn increment_logout_count(&self) {
        self.logout_count.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    pub async fn increment_messages_sent(&self) {
        self.messages_sent.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    pub async fn increment_messages_processed(&self) {
        self.messages_processed.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    pub async fn increment_errors(&self) {
        self.errors.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    pub async fn get_metrics(&self) -> MetricsData {
        MetricsData {
            login_count: self.login_count.load(std::sync::atomic::Ordering::Relaxed),
            logout_count: self.logout_count.load(std::sync::atomic::Ordering::Relaxed),
            messages_sent: self.messages_sent.load(std::sync::atomic::Ordering::Relaxed),
            messages_processed: self.messages_processed.load(std::sync::atomic::Ordering::Relaxed),
            errors: self.errors.load(std::sync::atomic::Ordering::Relaxed),
        }
    }
}

/// 指标数据
#[derive(Debug, Clone)]
pub struct MetricsData {
    pub login_count: usize,
    pub logout_count: usize,
    pub messages_sent: usize,
    pub messages_processed: usize,
    pub errors: usize,
}

/// 服务统计
#[derive(Debug)]
pub struct ServiceStats {
    pub active_sessions: usize,
    pub active_connections: usize,
    pub active_channels: usize,
    pub metrics: MetricsData,
}

/// 实时数据处理管道
pub struct RealtimeDataPipeline {
    input_channel: mpsc::UnboundedReceiver<RealtimeMessage>,
    processors: Vec<Arc<dyn DataProcessor + Send + Sync>>,
    output_channels: HashMap<String, mpsc::UnboundedSender<ProcessedMessage>>,
    processing_stats: Arc<ProcessingStats>,
}

/// 数据处理器 trait - 使用 async-trait 支持动态分发
#[async_trait::async_trait]
pub trait DataProcessor: Send + Sync {
    async fn process(&self, message: &RealtimeMessage) -> Result<ProcessedMessage>;
    fn get_name(&self) -> &str;
}

/// 处理后的消息
#[derive(Debug, Clone)]
pub struct ProcessedMessage {
    pub original_message: RealtimeMessage,
    pub processed_content: String,
    pub processor_name: String,
    pub processing_time_ms: u64,
}

/// 处理统计
pub struct ProcessingStats {
    messages_processed: Arc<AtomicUsize>,
    processing_time: Arc<AtomicU64>,
    errors: Arc<AtomicUsize>,
}

impl ProcessingStats {
    pub fn new() -> Self {
        Self {
            messages_processed: Arc::new(AtomicUsize::new(0)),
            processing_time: Arc::new(AtomicU64::new(0)),
            errors: Arc::new(AtomicUsize::new(0)),
        }
    }

    pub fn record_processing(&self, time_ms: u64) {
        self.messages_processed.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        self.processing_time.fetch_add(time_ms, std::sync::atomic::Ordering::Relaxed);
    }

    pub fn record_error(&self) {
        self.errors.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    }

    pub fn get_stats(&self) -> ProcessingStatsData {
        let processed = self.messages_processed.load(std::sync::atomic::Ordering::Relaxed);
        let total_time = self.processing_time.load(std::sync::atomic::Ordering::Relaxed);
        let errors = self.errors.load(std::sync::atomic::Ordering::Relaxed);
        
        ProcessingStatsData {
            messages_processed: processed,
            total_processing_time_ms: total_time,
            average_processing_time_ms: if processed > 0 { total_time / processed as u64 } else { 0 },
            errors: errors,
        }
    }
}

#[derive(Debug)]
pub struct ProcessingStatsData {
    pub messages_processed: usize,
    pub total_processing_time_ms: u64,
    pub average_processing_time_ms: u64,
    pub errors: usize,
}

impl RealtimeDataPipeline {
    pub fn new(input_channel: mpsc::UnboundedReceiver<RealtimeMessage>) -> Self {
        Self {
            input_channel,
            processors: Vec::new(),
            output_channels: HashMap::new(),
            processing_stats: Arc::new(ProcessingStats::new()),
        }
    }

    pub fn add_processor(&mut self, processor: Arc<dyn DataProcessor + Send + Sync>) {
        self.processors.push(processor);
    }

    pub fn add_output_channel(&mut self, name: String, sender: mpsc::UnboundedSender<ProcessedMessage>) {
        self.output_channels.insert(name, sender);
    }

    pub async fn start_processing(&mut self) -> Result<()> {
        info!("启动实时数据处理管道");
        
        while let Some(message) = self.input_channel.recv().await {
            let start_time = Instant::now();
            
            // 并行处理消息
            let mut handles = Vec::new();
            for processor in &self.processors {
                let processor = Arc::clone(processor);
                let message = message.clone();
                let stats = Arc::clone(&self.processing_stats);
                
                let handle = tokio::spawn(async move {
                    let process_start = Instant::now();
                    match processor.process(&message).await {
                        Ok(processed_message) => {
                            let process_time = process_start.elapsed().as_millis() as u64;
                            stats.record_processing(process_time);
                            Ok(processed_message)
                        }
                        Err(e) => {
                            stats.record_error();
                            error!("处理器 {} 处理消息失败: {}", processor.get_name(), e);
                            Err(e)
                        }
                    }
                });
                handles.push(handle);
            }

            // 收集处理结果
            let mut processed_messages = Vec::new();
            for handle in handles {
                if let Ok(Ok(processed_message)) = handle.await {
                    processed_messages.push(processed_message);
                }
            }

            // 发送到输出通道
            for processed_message in processed_messages {
                for (channel_name, sender) in &self.output_channels {
                    if let Err(_) = sender.send(processed_message.clone()) {
                        warn!("发送到通道 {} 失败", channel_name);
                    }
                }
            }

            let total_time = start_time.elapsed().as_millis();
            debug!("处理消息耗时: {}ms", total_time);
        }

        Ok(())
    }

    pub fn get_processing_stats(&self) -> ProcessingStatsData {
        self.processing_stats.get_stats()
    }
}

/// 文本内容处理器
pub struct TextContentProcessor {
    name: String,
}

impl TextContentProcessor {
    pub fn new() -> Self {
        Self {
            name: "TextContentProcessor".to_string(),
        }
    }
}

#[async_trait::async_trait]
impl DataProcessor for TextContentProcessor {
    async fn process(&self, message: &RealtimeMessage) -> Result<ProcessedMessage> {
        // 模拟文本处理
        sleep(Duration::from_millis(10)).await;
        
        let processed_content = format!("[PROCESSED] {}", message.content.to_uppercase());
        
        Ok(ProcessedMessage {
            original_message: message.clone(),
            processed_content,
            processor_name: self.name.clone(),
            processing_time_ms: 10,
        })
    }

    fn get_name(&self) -> &str {
        &self.name
    }
}

/// 分布式系统协调器
#[allow(dead_code)]
pub struct DistributedSystemCoordinator {
    nodes: Arc<RwLock<HashMap<String, NodeInfo>>>,
    leader_election: Arc<Mutex<Option<String>>>,
    heartbeat_interval: Duration,
    election_timeout: Duration,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
pub struct NodeInfo {
    pub node_id: String,
    pub address: String,
    pub last_heartbeat: Instant,
    pub is_leader: bool,
    pub health_status: HealthStatus,
}

#[derive(Debug, Clone, PartialEq)]
#[allow(dead_code)]
pub enum HealthStatus {
    Healthy,
    Unhealthy,
    Unknown,
}

impl DistributedSystemCoordinator {
    pub fn new(heartbeat_interval: Duration, election_timeout: Duration) -> Self {
        Self {
            nodes: Arc::new(RwLock::new(HashMap::new())),
            leader_election: Arc::new(Mutex::new(None)),
            heartbeat_interval,
            election_timeout,
        }
    }

    /// 注册节点
    pub async fn register_node(&self, node_id: String, address: String) -> Result<()> {
        let node_info = NodeInfo {
            node_id: node_id.clone(),
            address,
            last_heartbeat: Instant::now(),
            is_leader: false,
            health_status: HealthStatus::Healthy,
        };

        let mut nodes = self.nodes.write().await;
        nodes.insert(node_id.clone(), node_info);
        
        info!("节点 {} 注册成功", node_id);
        
        // 如果是第一个节点，自动成为领导者
        if nodes.len() == 1 {
            self.elect_leader(node_id).await?;
        }
        
        Ok(())
    }

    /// 心跳更新
    pub async fn update_heartbeat(&self, node_id: &str) -> Result<()> {
        let mut nodes = self.nodes.write().await;
        if let Some(node) = nodes.get_mut(node_id) {
            node.last_heartbeat = Instant::now();
            node.health_status = HealthStatus::Healthy;
        }
        Ok(())
    }

    /// 选举领导者
    pub async fn elect_leader(&self, node_id: String) -> Result<()> {
        let mut leader = self.leader_election.lock().await;
        *leader = Some(node_id.clone());
        
        let mut nodes = self.nodes.write().await;
        for node in nodes.values_mut() {
            node.is_leader = node.node_id == node_id;
        }
        
        info!("节点 {} 被选为领导者", node_id);
        Ok(())
    }

    /// 检查领导者健康状态
    pub async fn check_leader_health(&self) -> Result<()> {
        let leader_id = {
            let leader = self.leader_election.lock().await;
            leader.clone()
        };

        if let Some(leader_id) = leader_id {
            let nodes = self.nodes.read().await;
            if let Some(leader_node) = nodes.get(&leader_id) {
                if leader_node.last_heartbeat.elapsed() > self.election_timeout {
                    warn!("领导者 {} 超时，开始重新选举", leader_id);
                    self.start_leader_election().await?;
                }
            }
        }
        
        Ok(())
    }

    /// 开始领导者选举
    pub async fn start_leader_election(&self) -> Result<()> {
        let nodes = self.nodes.read().await;
        let healthy_nodes: Vec<_> = nodes.values()
            .filter(|node| node.health_status == HealthStatus::Healthy)
            .collect();

        if let Some(new_leader) = healthy_nodes.iter().min_by_key(|node| &node.node_id) {
            self.elect_leader(new_leader.node_id.clone()).await?;
        }
        
        Ok(())
    }

    /// 获取集群状态
    pub async fn get_cluster_status(&self) -> ClusterStatus {
        let nodes = self.nodes.read().await;
        let leader = {
            let leader = self.leader_election.lock().await;
            leader.clone()
        };

        ClusterStatus {
            total_nodes: nodes.len(),
            healthy_nodes: nodes.values().filter(|n| n.health_status == HealthStatus::Healthy).count(),
            leader_node: leader,
            nodes: nodes.values().cloned().collect(),
        }
    }
}

#[derive(Debug)]
#[allow(dead_code)]
pub struct ClusterStatus {
    pub total_nodes: usize,
    pub healthy_nodes: usize,
    pub leader_node: Option<String>,
    pub nodes: Vec<NodeInfo>,
}

/// 主演示函数
#[tokio::main]
async fn main() -> Result<()> {
    // 初始化日志
    tracing_subscriber::fmt::init();

    info!("🚀 开始 Rust 1.90 真实世界应用场景演示");
    info!("==========================================");

    // 1. 高并发 Web 服务演示
    info!("\n🌐 高并发 Web 服务演示:");
    let web_service = Arc::new(HighConcurrencyWebService::new());

    // 模拟用户登录
    let session1 = web_service.user_login("user1".to_string(), "192.168.1.100".to_string(), "Mozilla/5.0".to_string()).await?;
    let session2 = web_service.user_login("user2".to_string(), "192.168.1.101".to_string(), "Chrome/91.0".to_string()).await?;

    // 模拟实时消息发送
    for i in 0..5 {
        web_service.send_realtime_message(
            "user1".to_string(),
            "user2".to_string(),
            format!("Hello from user1! Message {}", i),
            MessageType::Text
        ).await?;
        
        sleep(Duration::from_millis(100)).await;
    }

    // 显示服务统计
    let stats = web_service.get_service_stats().await;
    println!("服务统计: {:?}", stats);

    // 2. 实时数据处理管道演示
    info!("\n📊 实时数据处理管道演示:");
    let (input_tx, input_rx) = mpsc::unbounded_channel();
    let (output_tx, mut output_rx) = mpsc::unbounded_channel();
    
    let mut pipeline = RealtimeDataPipeline::new(input_rx);
    pipeline.add_processor(Arc::new(TextContentProcessor::new()));
    pipeline.add_output_channel("output".to_string(), output_tx);

    // 启动处理管道
    let pipeline_handle = tokio::spawn(async move {
        pipeline.start_processing().await
    });

    // 发送测试消息
    for i in 0..10 {
        let message = RealtimeMessage {
            message_id: format!("msg_{}", i),
            user_id: "test_user".to_string(),
            content: format!("Test message {}", i),
            timestamp: SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_secs(),
            message_type: MessageType::Text,
        };
        
        input_tx.send(message)?;
        sleep(Duration::from_millis(50)).await;
    }

    // 收集处理结果
    let mut processed_count = 0;
    while let Some(processed_message) = output_rx.recv().await {
        println!("处理结果: {}", processed_message.processed_content);
        processed_count += 1;
        if processed_count >= 10 {
            break;
        }
    }

    // 3. 分布式系统协调演示
    info!("\n🔄 分布式系统协调演示:");
    let coordinator = Arc::new(DistributedSystemCoordinator::new(
        Duration::from_secs(5),
        Duration::from_secs(10)
    ));

    // 注册节点
    coordinator.register_node("node1".to_string(), "192.168.1.10:8080".to_string()).await?;
    coordinator.register_node("node2".to_string(), "192.168.1.11:8080".to_string()).await?;
    coordinator.register_node("node3".to_string(), "192.168.1.12:8080".to_string()).await?;

    // 模拟心跳
    for _i in 0..3 {
        coordinator.update_heartbeat("node1").await?;
        coordinator.update_heartbeat("node2").await?;
        sleep(Duration::from_millis(100)).await;
    }

    // 显示集群状态
    let cluster_status = coordinator.get_cluster_status().await;
    println!("集群状态: {:?}", cluster_status);

    // 4. 清理和登出
    web_service.user_logout(session1).await?;
    web_service.user_logout(session2).await?;

    // 等待管道完成
    let _ = pipeline_handle.await;

    info!("✅ Rust 1.90 真实世界应用场景演示完成!");
    Ok(())
}

// 添加缺失的导入
use std::sync::atomic::{AtomicUsize, AtomicU64};

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_web_service_login_logout() {
        let service = HighConcurrencyWebService::new();
        
        let session = service.user_login("test_user".to_string(), "127.0.0.1".to_string(), "test".to_string()).await.unwrap();
        assert!(!session.is_empty());
        
        service.user_logout(session).await.unwrap();
    }

    #[tokio::test]
    async fn test_realtime_message() {
        let service = HighConcurrencyWebService::new();
        
        let session1 = service.user_login("user1".to_string(), "127.0.0.1".to_string(), "test".to_string()).await.unwrap();
        let session2 = service.user_login("user2".to_string(), "127.0.0.2".to_string(), "test".to_string()).await.unwrap();
        
        let result = service.send_realtime_message(
            "user1".to_string(),
            "user2".to_string(),
            "Hello".to_string(),
            MessageType::Text
        ).await;
        
        assert!(result.is_ok());
        
        service.user_logout(session1).await.unwrap();
        service.user_logout(session2).await.unwrap();
    }

    #[tokio::test]
    async fn test_distributed_coordinator() {
        let coordinator = DistributedSystemCoordinator::new(
            Duration::from_secs(1),
            Duration::from_secs(2)
        );
        
        coordinator.register_node("node1".to_string(), "127.0.0.1:8080".to_string()).await.unwrap();
        
        let status = coordinator.get_cluster_status().await;
        assert_eq!(status.total_nodes, 1);
        assert_eq!(status.healthy_nodes, 1);
    }
}
