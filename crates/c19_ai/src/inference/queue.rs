//! 推理队列模块
//! 
//! 提供高性能的推理请求队列管理

use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use uuid::Uuid;
use std::collections::{BinaryHeap, HashMap};
use std::sync::Arc;
use tokio::sync::{RwLock, mpsc};
use std::cmp::Ordering;
// 移除未使用的导入

/// 推理队列条目
#[derive(Debug, Clone)]
#[allow(unused)]
struct QueueItem {
    request: super::InferenceRequest,
    priority: u8, // 0 = Critical, 1 = High, 2 = Normal, 3 = Low
    enqueued_at: DateTime<Utc>,
}

impl PartialEq for QueueItem {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}

impl Eq for QueueItem {}

impl PartialOrd for QueueItem {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for QueueItem {
    fn cmp(&self, other: &Self) -> Ordering {
        // 优先级数字越小，优先级越高
        other.priority.cmp(&self.priority)
    }
}

/// 推理队列状态
#[derive(Debug, Clone, Serialize, Deserialize)]
#[allow(unused)]
pub struct QueueStatus {
    pub queue_size: usize,
    pub queue_capacity: usize,
    pub processing_count: usize,
    pub completed_count: u64,
    pub failed_count: u64,
    pub average_wait_time_ms: f64,
}

/// 推理队列
#[derive(Debug)]
#[allow(unused)]
pub struct InferenceQueue {
    pub id: Uuid,
    pub name: String,
    pub created_at: DateTime<Utc>,
    queue: Arc<RwLock<BinaryHeap<QueueItem>>>,
    results: Arc<RwLock<HashMap<String, super::InferenceResponse>>>,
    status: Arc<RwLock<QueueStatus>>,
    capacity: usize,
    sender: mpsc::UnboundedSender<QueueItem>,
    receiver: Arc<RwLock<Option<mpsc::UnboundedReceiver<QueueItem>>>>,
}

impl InferenceQueue {
    /// 创建新的推理队列
    #[allow(unused)]
    pub fn new(name: String) -> Self {
        let (sender, receiver) = mpsc::unbounded_channel();
        
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
            queue: Arc::new(RwLock::new(BinaryHeap::new())),
            results: Arc::new(RwLock::new(HashMap::new())),
            status: Arc::new(RwLock::new(QueueStatus {
                queue_size: 0,
                queue_capacity: 1000,
                processing_count: 0,
                completed_count: 0,
                failed_count: 0,
                average_wait_time_ms: 0.0,
            })),
            capacity: 1000,
            sender,
            receiver: Arc::new(RwLock::new(Some(receiver))),
        }
    }

    /// 创建带容量的推理队列
    #[allow(unused)]
    pub fn with_capacity(name: String, capacity: usize) -> Self {
        let (sender, receiver) = mpsc::unbounded_channel();
        
        Self {
            id: Uuid::new_v4(),
            name,
            created_at: Utc::now(),
            queue: Arc::new(RwLock::new(BinaryHeap::new())),
            results: Arc::new(RwLock::new(HashMap::new())),
            status: Arc::new(RwLock::new(QueueStatus {
                queue_size: 0,
                queue_capacity: capacity,
                processing_count: 0,
                completed_count: 0,
                failed_count: 0,
                average_wait_time_ms: 0.0,
            })),
            capacity,
            sender,
            receiver: Arc::new(RwLock::new(Some(receiver))),
        }
    }

    /// 将请求加入队列
    #[allow(unused)]
    pub async fn enqueue(&self, request: super::InferenceRequest) -> anyhow::Result<()> {
        // 检查队列容量
        {
            let status = self.status.read().await;
            if status.queue_size >= self.capacity {
                return Err(anyhow::anyhow!("Queue is full"));
            }
        }

        // 转换优先级
        let priority = match request.priority {
            super::InferencePriority::Critical => 0,
            super::InferencePriority::High => 1,
            super::InferencePriority::Normal => 2,
            super::InferencePriority::Low => 3,
        };

        let queue_item = QueueItem {
            request,
            priority,
            enqueued_at: Utc::now(),
        };

        // 添加到队列
        {
            let mut queue = self.queue.write().await;
            queue.push(queue_item);
        }

        // 更新状态
        {
            let mut status = self.status.write().await;
            status.queue_size += 1;
        }

        Ok(())
    }

    /// 获取推理结果
    #[allow(unused)]
    pub async fn get_result(&self, request_id: &str) -> anyhow::Result<Option<super::InferenceResponse>> {
        let results = self.results.read().await;
        Ok(results.get(request_id).cloned())
    }

    /// 设置推理结果
    pub async fn set_result(&self, request_id: String, response: super::InferenceResponse) {
        let mut results = self.results.write().await;
        results.insert(request_id, response);
        
        // 更新状态
        let mut status = self.status.write().await;
        status.completed_count += 1;
        status.processing_count = status.processing_count.saturating_sub(1);
    }

    /// 设置推理失败
    pub async fn set_failed(&self, _request_id: String) {
        // 更新状态
        let mut status = self.status.write().await;
        status.failed_count += 1;
        status.processing_count = status.processing_count.saturating_sub(1);
    }

    /// 获取下一个请求
    pub async fn dequeue(&self) -> Option<super::InferenceRequest> {
        let mut queue = self.queue.write().await;
        if let Some(item) = queue.pop() {
            // 更新状态
            let mut status = self.status.write().await;
            status.queue_size = status.queue_size.saturating_sub(1);
            status.processing_count += 1;
            
            Some(item.request)
        } else {
            None
        }
    }

    /// 获取队列状态
    pub async fn get_status(&self) -> QueueStatus {
        let status = self.status.read().await;
        status.clone()
    }

    /// 清空队列
    pub async fn clear(&self) {
        let mut queue = self.queue.write().await;
        queue.clear();
        
        let mut results = self.results.write().await;
        results.clear();
        
        let mut status = self.status.write().await;
        status.queue_size = 0;
        status.processing_count = 0;
    }

    /// 获取队列大小
    pub async fn size(&self) -> usize {
        let status = self.status.read().await;
        status.queue_size
    }

    /// 检查队列是否为空
    pub async fn is_empty(&self) -> bool {
        self.size().await == 0
    }

    /// 检查队列是否已满
    pub async fn is_full(&self) -> bool {
        let status = self.status.read().await;
        status.queue_size >= self.capacity
    }

    /// 启动队列处理器
    pub async fn start_processor<F>(&self, mut processor: F) 
    where
        F: FnMut(super::InferenceRequest) -> anyhow::Result<super::InferenceResponse> + Send + 'static,
    {
        let receiver = {
            let mut receiver_guard = self.receiver.write().await;
            receiver_guard.take()
        };

        if let Some(mut rx) = receiver {
            tokio::spawn(async move {
                while let Some(item) = rx.recv().await {
                    match processor(item.request.clone()) {
                        Ok(_response) => {
                            // 设置结果
                            // TODO: 需要访问self来设置结果
                        }
                        Err(e) => {
                            tracing::error!("Failed to process request {}: {}", item.request.id, e);
                            // TODO: 设置失败状态
                        }
                    }
                }
            });
        }
    }
}
