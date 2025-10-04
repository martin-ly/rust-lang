//! # 调用链追踪（Call Chain Tracing）
//!
//! 记录和分析方法调用链，支持同步和异步调用。

use dashmap::DashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use serde::{Deserialize, Serialize};

/// 调用ID
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct CallId(pub String);

impl CallId {
    pub fn new() -> Self {
        Self(uuid::Uuid::new_v4().to_string())
    }
}

impl Default for CallId {
    fn default() -> Self {
        Self::new()
    }
}

/// 调用条目
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CallEntry {
    /// 调用ID
    pub call_id: CallId,
    /// 父调用ID
    pub parent_id: Option<CallId>,
    /// 方法名
    pub method_name: String,
    /// 服务名
    pub service_name: String,
    /// 开始时间
    pub start_time: u64,
    /// 持续时间（微秒）
    pub duration_us: u64,
    /// 状态：success/error
    pub status: String,
    /// 错误信息
    pub error: Option<String>,
    /// 深度
    pub depth: usize,
}

/// 调用链
#[derive(Debug, Clone)]
pub struct CallChain {
    /// 根调用ID
    pub root_id: CallId,
    /// 所有调用条目
    pub entries: Vec<CallEntry>,
    /// 总持续时间
    pub total_duration: Duration,
}

impl CallChain {
    /// 获取最长路径
    pub fn longest_path(&self) -> Vec<&CallEntry> {
        // 简化版：返回所有条目
        self.entries.iter().collect()
    }
    
    /// 获取最慢的调用
    pub fn slowest_calls(&self, limit: usize) -> Vec<&CallEntry> {
        let mut sorted: Vec<_> = self.entries.iter().collect();
        sorted.sort_by_key(|e| e.duration_us);
        sorted.reverse();
        sorted.into_iter().take(limit).collect()
    }
    
    /// 获取错误调用
    pub fn failed_calls(&self) -> Vec<&CallEntry> {
        self.entries.iter().filter(|e| e.status == "error").collect()
    }
}

/// 调用链统计
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CallChainStats {
    /// 总调用数
    pub total_calls: u64,
    /// 成功调用数
    pub successful_calls: u64,
    /// 失败调用数
    pub failed_calls: u64,
    /// 平均持续时间（微秒）
    pub avg_duration_us: u64,
    /// P50持续时间
    pub p50_duration_us: u64,
    /// P95持续时间
    pub p95_duration_us: u64,
    /// P99持续时间
    pub p99_duration_us: u64,
}

/// 调用链追踪器
pub struct CallChainTracker {
    /// 活跃的调用链
    active_chains: Arc<DashMap<CallId, Vec<CallEntry>>>,
    /// 完成的调用链
    completed_chains: Arc<DashMap<CallId, CallChain>>,
}

impl CallChainTracker {
    /// 创建新的追踪器
    pub fn new() -> Self {
        Self {
            active_chains: Arc::new(DashMap::new()),
            completed_chains: Arc::new(DashMap::new()),
        }
    }
    
    /// 开始调用
    pub fn start_call(
        &self,
        method_name: String,
        service_name: String,
        parent_id: Option<CallId>,
    ) -> CallId {
        let call_id = CallId::new();
        let depth = if let Some(ref pid) = parent_id {
            if let Some(entries) = self.active_chains.get(pid) {
                entries.iter().map(|e| e.depth).max().unwrap_or(0) + 1
            } else {
                0
            }
        } else {
            0
        };
        
        let entry = CallEntry {
            call_id: call_id.clone(),
            parent_id: parent_id.clone(),
            method_name,
            service_name,
            start_time: Instant::now().elapsed().as_micros() as u64,
            duration_us: 0,
            status: "pending".to_string(),
            error: None,
            depth,
        };
        
        let root_id = parent_id.unwrap_or_else(|| call_id.clone());
        self.active_chains.entry(root_id).or_insert_with(Vec::new).push(entry);
        
        call_id
    }
    
    /// 结束调用
    pub fn end_call(&self, call_id: &CallId, status: &str, error: Option<String>) {
        // 查找并更新调用条目
        for mut entry in self.active_chains.iter_mut() {
            if let Some(call_entry) = entry.value_mut().iter_mut().find(|e| &e.call_id == call_id) {
                call_entry.duration_us = Instant::now().elapsed().as_micros() as u64 - call_entry.start_time;
                call_entry.status = status.to_string();
                call_entry.error = error;
                break;
            }
        }
    }
    
    /// 完成调用链
    pub fn complete_chain(&self, root_id: &CallId) {
        if let Some((_, entries)) = self.active_chains.remove(root_id) {
            let total_duration = entries.iter()
                .map(|e| Duration::from_micros(e.duration_us))
                .sum();
            
            let chain = CallChain {
                root_id: root_id.clone(),
                entries,
                total_duration,
            };
            
            self.completed_chains.insert(root_id.clone(), chain);
        }
    }
    
    /// 获取调用链
    pub fn get_chain(&self, root_id: &CallId) -> Option<CallChain> {
        self.completed_chains.get(root_id).map(|entry| entry.value().clone())
    }
    
    /// 获取统计信息
    pub fn get_stats(&self) -> CallChainStats {
        let all_entries: Vec<_> = self.completed_chains
            .iter()
            .flat_map(|entry| entry.value().entries.clone())
            .collect();
        
        let total_calls = all_entries.len() as u64;
        let successful_calls = all_entries.iter().filter(|e| e.status == "success").count() as u64;
        let failed_calls = all_entries.iter().filter(|e| e.status == "error").count() as u64;
        
        let mut durations: Vec<_> = all_entries.iter().map(|e| e.duration_us).collect();
        durations.sort_unstable();
        
        let avg_duration_us = if !durations.is_empty() {
            durations.iter().sum::<u64>() / durations.len() as u64
        } else {
            0
        };
        
        let p50_duration_us = durations.get(durations.len() / 2).copied().unwrap_or(0);
        let p95_duration_us = durations.get(durations.len() * 95 / 100).copied().unwrap_or(0);
        let p99_duration_us = durations.get(durations.len() * 99 / 100).copied().unwrap_or(0);
        
        CallChainStats {
            total_calls,
            successful_calls,
            failed_calls,
            avg_duration_us,
            p50_duration_us,
            p95_duration_us,
            p99_duration_us,
        }
    }
    
    /// 清理旧的调用链
    pub fn cleanup_old_chains(&self, older_than: Duration) {
        let now = Instant::now();
        self.completed_chains.retain(|_, chain| {
            chain.total_duration < now.elapsed() - older_than
        });
    }
}

impl Default for CallChainTracker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_call_chain_tracker() {
        let tracker = CallChainTracker::new();
        
        let call_id = tracker.start_call(
            "test_method".to_string(),
            "test_service".to_string(),
            None,
        );
        
        tracker.end_call(&call_id, "success", None);
        tracker.complete_chain(&call_id);
        
        let chain = tracker.get_chain(&call_id);
        assert!(chain.is_some());
        
        let stats = tracker.get_stats();
        assert_eq!(stats.total_calls, 1);
    }
    
    #[test]
    fn test_nested_calls() {
        let tracker = CallChainTracker::new();
        
        let parent_id = tracker.start_call(
            "parent".to_string(),
            "service".to_string(),
            None,
        );
        
        let child_id = tracker.start_call(
            "child".to_string(),
            "service".to_string(),
            Some(parent_id.clone()),
        );
        
        tracker.end_call(&child_id, "success", None);
        tracker.end_call(&parent_id, "success", None);
        tracker.complete_chain(&parent_id);
        
        let chain = tracker.get_chain(&parent_id).unwrap();
        assert_eq!(chain.entries.len(), 2);
    }
}

