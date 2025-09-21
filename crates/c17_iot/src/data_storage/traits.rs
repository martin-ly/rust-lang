//! 存储接口 trait 定义
//! 
//! 本模块定义了所有存储相关的 trait 接口

use crate::data_storage::{DataPoint, Query, StorageError, StorageStats};
use async_trait::async_trait;
use std::collections::HashMap;

/// 存储接口
#[async_trait]
pub trait StorageInterface {
    /// 连接存储
    async fn connect(&mut self) -> Result<(), StorageError>;
    
    /// 断开连接
    async fn disconnect(&mut self) -> Result<(), StorageError>;
    
    /// 插入数据
    async fn insert(&mut self, data: DataPoint) -> Result<(), StorageError>;
    
    /// 批量插入数据
    async fn insert_batch(&mut self, data: Vec<DataPoint>) -> Result<(), StorageError>;
    
    /// 查询数据
    async fn query(&mut self, query: Query) -> Result<Vec<DataPoint>, StorageError>;
    
    /// 更新数据
    async fn update(&mut self, query: Query, updates: HashMap<String, serde_json::Value>) -> Result<u64, StorageError>;
    
    /// 删除数据
    async fn delete(&mut self, query: Query) -> Result<u64, StorageError>;
    
    /// 获取统计信息
    async fn get_stats(&mut self) -> Result<StorageStats, StorageError>;
    
    /// 备份数据
    async fn backup(&mut self, backup_path: &str) -> Result<(), StorageError>;
    
    /// 恢复数据
    async fn restore(&mut self, backup_path: &str) -> Result<(), StorageError>;
}
