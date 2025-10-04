/// 日志关联系统
///
/// 提供跨服务的日志关联和追踪功能

use crate::prelude::*;
use std::collections::HashMap;
use std::sync::Arc;
use tokio::sync::RwLock;
use serde::{Serialize, Deserialize};

/// 日志级别
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum LogLevel {
    Trace,
    Debug,
    Info,
    Warn,
    Error,
    Fatal,
}

/// 关联上下文
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CorrelationContext {
    /// 追踪ID
    pub trace_id: String,
    /// 请求ID
    pub request_id: String,
    /// 用户ID
    pub user_id: Option<String>,
    /// 会话ID
    pub session_id: Option<String>,
    /// 服务名称
    pub service_name: String,
    /// 额外元数据
    pub metadata: HashMap<String, String>,
}

impl CorrelationContext {
    /// 创建新的关联上下文
    pub fn new(service_name: impl Into<String>) -> Self {
        Self {
            trace_id: uuid::Uuid::new_v4().to_string(),
            request_id: uuid::Uuid::new_v4().to_string(),
            user_id: None,
            session_id: None,
            service_name: service_name.into(),
            metadata: HashMap::new(),
        }
    }
    
    /// 设置用户ID
    pub fn with_user_id(mut self, user_id: impl Into<String>) -> Self {
        self.user_id = Some(user_id.into());
        self
    }
    
    /// 设置会话ID
    pub fn with_session_id(mut self, session_id: impl Into<String>) -> Self {
        self.session_id = Some(session_id.into());
        self
    }
    
    /// 添加元数据
    pub fn add_metadata(&mut self, key: impl Into<String>, value: impl Into<String>) {
        self.metadata.insert(key.into(), value.into());
    }
}

/// 关联的日志条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CorrelatedLogEntry {
    /// 日志ID
    pub id: String,
    /// 关联上下文
    pub context: CorrelationContext,
    /// 日志级别
    pub level: LogLevel,
    /// 日志消息
    pub message: String,
    /// 时间戳
    pub timestamp: i64,
    /// 文件位置
    pub location: Option<String>,
    /// 额外字段
    pub fields: HashMap<String, String>,
}

/// 日志查询
#[derive(Debug, Clone)]
pub struct LogQuery {
    /// 追踪ID过滤
    pub trace_id: Option<String>,
    /// 请求ID过滤
    pub request_id: Option<String>,
    /// 服务名称过滤
    pub service_name: Option<String>,
    /// 日志级别过滤
    pub min_level: Option<LogLevel>,
    /// 时间范围（开始）
    pub start_time: Option<i64>,
    /// 时间范围（结束）
    pub end_time: Option<i64>,
    /// 最大结果数
    pub limit: usize,
}

impl Default for LogQuery {
    fn default() -> Self {
        Self {
            trace_id: None,
            request_id: None,
            service_name: None,
            min_level: None,
            start_time: None,
            end_time: None,
            limit: 1000,
        }
    }
}

/// 日志关联器
pub struct LogCorrelator {
    /// 存储的日志条目
    logs: Arc<RwLock<Vec<CorrelatedLogEntry>>>,
    /// 最大日志条目数
    max_logs: usize,
}

impl LogCorrelator {
    /// 创建新的日志关联器
    pub fn new() -> Self {
        Self {
            logs: Arc::new(RwLock::new(Vec::new())),
            max_logs: 100000,
        }
    }
    
    /// 设置最大日志数
    pub fn with_max_logs(mut self, max: usize) -> Self {
        self.max_logs = max;
        self
    }
    
    /// 记录日志
    pub async fn log(
        &self,
        context: CorrelationContext,
        level: LogLevel,
        message: impl Into<String>,
    ) -> Result<()> {
        self.log_with_fields(context, level, message, HashMap::new()).await
    }
    
    /// 记录带字段的日志
    pub async fn log_with_fields(
        &self,
        context: CorrelationContext,
        level: LogLevel,
        message: impl Into<String>,
        fields: HashMap<String, String>,
    ) -> Result<()> {
        let entry = CorrelatedLogEntry {
            id: uuid::Uuid::new_v4().to_string(),
            context,
            level,
            message: message.into(),
            timestamp: chrono::Utc::now().timestamp(),
            location: None,
            fields,
        };
        
        let mut logs = self.logs.write().await;
        logs.push(entry);
        
        // 限制日志数量
        if logs.len() > self.max_logs {
            let to_remove = logs.len() - self.max_logs;
            logs.drain(0..to_remove);
        }
        
        Ok(())
    }
    
    /// 查询日志
    pub async fn query(&self, query: LogQuery) -> Vec<CorrelatedLogEntry> {
        let logs = self.logs.read().await;
        
        let filtered: Vec<_> = logs.iter()
            .filter(|entry| {
                // 追踪ID过滤
                if let Some(ref trace_id) = query.trace_id {
                    if &entry.context.trace_id != trace_id {
                        return false;
                    }
                }
                
                // 请求ID过滤
                if let Some(ref request_id) = query.request_id {
                    if &entry.context.request_id != request_id {
                        return false;
                    }
                }
                
                // 服务名称过滤
                if let Some(ref service_name) = query.service_name {
                    if &entry.context.service_name != service_name {
                        return false;
                    }
                }
                
                // 日志级别过滤
                if let Some(min_level) = query.min_level {
                    if entry.level < min_level {
                        return false;
                    }
                }
                
                // 时间范围过滤
                if let Some(start_time) = query.start_time {
                    if entry.timestamp < start_time {
                        return false;
                    }
                }
                
                if let Some(end_time) = query.end_time {
                    if entry.timestamp > end_time {
                        return false;
                    }
                }
                
                true
            })
            .cloned()
            .collect();
        
        filtered.into_iter().take(query.limit).collect()
    }
    
    /// 通过追踪ID获取所有关联日志
    pub async fn get_by_trace_id(&self, trace_id: &str) -> Vec<CorrelatedLogEntry> {
        let query = LogQuery {
            trace_id: Some(trace_id.to_string()),
            ..Default::default()
        };
        self.query(query).await
    }
    
    /// 清空所有日志
    pub async fn clear(&self) {
        self.logs.write().await.clear();
    }
}

impl Default for LogCorrelator {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_log_correlation() {
        let correlator = LogCorrelator::new();
        let context = CorrelationContext::new("test-service")
            .with_user_id("user123");
        
        correlator.log(context.clone(), LogLevel::Info, "Test log 1").await.unwrap();
        correlator.log(context.clone(), LogLevel::Error, "Test log 2").await.unwrap();
        
        let logs = correlator.get_by_trace_id(&context.trace_id).await;
        assert_eq!(logs.len(), 2);
    }
    
    #[tokio::test]
    async fn test_log_query() {
        let correlator = LogCorrelator::new();
        let context = CorrelationContext::new("test-service");
        
        correlator.log(context.clone(), LogLevel::Debug, "Debug log").await.unwrap();
        correlator.log(context.clone(), LogLevel::Error, "Error log").await.unwrap();
        
        let query = LogQuery {
            min_level: Some(LogLevel::Error),
            ..Default::default()
        };
        
        let logs = correlator.query(query).await;
        assert_eq!(logs.len(), 1);
        assert_eq!(logs[0].level, LogLevel::Error);
    }
}

