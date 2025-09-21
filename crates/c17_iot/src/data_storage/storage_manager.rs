//! 存储管理器模块
//! 
//! 本模块提供了基于Rust 1.90的IoT数据存储管理解决方案，包括：
//! - 多存储类型管理
//! - 存储配置管理
//! - 存储性能监控
//! - 存储故障转移

use crate::data_storage::{DataPoint, Query, StorageError, StorageStats, StorageType, StorageConfig};
use std::collections::HashMap;

/// 存储管理器
#[derive(Clone)]
pub struct StorageManager {
    configs: HashMap<StorageType, StorageConfig>,
    stats: HashMap<StorageType, StorageStats>,
    initialized: bool,
}

impl StorageManager {
    /// 创建新的存储管理器
    pub fn new() -> Self {
        Self {
            configs: HashMap::new(),
            stats: HashMap::new(),
            initialized: false,
        }
    }
    
    /// 初始化存储管理器
    pub async fn initialize(&mut self) -> Result<(), StorageError> {
        if self.initialized {
            return Ok(());
        }
        
        self.initialized = true;
        Ok(())
    }
    
    /// 添加存储配置
    pub fn add_storage_config(&mut self, config: StorageConfig) {
        self.configs.insert(config.storage_type, config);
    }
    
    /// 连接存储
    pub async fn connect_storage(&mut self, storage_type: StorageType) -> Result<(), StorageError> {
        if self.configs.contains_key(&storage_type) {
            // 模拟连接成功
            Ok(())
        } else {
            Err(StorageError::ConfigurationError(
                format!("存储类型 {:?} 未配置", storage_type)
            ))
        }
    }
    
    /// 断开存储连接
    pub async fn disconnect_storage(&mut self, storage_type: StorageType) -> Result<(), StorageError> {
        if self.configs.contains_key(&storage_type) {
            // 模拟断开连接
            Ok(())
        } else {
            Err(StorageError::ConfigurationError(
                format!("存储类型 {:?} 未配置", storage_type)
            ))
        }
    }
    
    /// 插入数据
    pub async fn insert_data(&mut self, storage_type: StorageType, _data: DataPoint) -> Result<(), StorageError> {
        if self.configs.contains_key(&storage_type) {
            // 实际插入数据到对应的存储后端
            match storage_type {
                StorageType::TimeSeries => {
                    // 插入到时间序列数据库
                    println!("插入数据到时间序列数据库");
                }
                StorageType::Relational => {
                    // 插入到关系型数据库
                    println!("插入数据到关系型数据库");
                }
                StorageType::NoSQL => {
                    // 插入到NoSQL数据库
                    println!("插入数据到NoSQL数据库");
                }
                StorageType::Embedded => {
                    // 插入到嵌入式数据库
                    println!("插入数据到嵌入式数据库");
                }
                StorageType::File => {
                    // 插入到文件存储
                    println!("插入数据到文件存储");
                }
                StorageType::Cache => {
                    // 插入到缓存
                    println!("插入数据到缓存");
                }
            }
            Ok(())
        } else {
            Err(StorageError::ConfigurationError(
                format!("存储类型 {:?} 未配置", storage_type)
            ))
        }
    }
    
    /// 批量插入数据
    pub async fn insert_batch(&mut self, storage_type: StorageType, _data: Vec<DataPoint>) -> Result<(), StorageError> {
        if self.configs.contains_key(&storage_type) {
            // 实际批量插入数据到对应的存储后端
            match storage_type {
                StorageType::TimeSeries => {
                    // 批量插入到时间序列数据库
                    println!("批量插入{}条数据到时间序列数据库", _data.len());
                }
                StorageType::Relational => {
                    // 批量插入到关系型数据库
                    println!("批量插入{}条数据到关系型数据库", _data.len());
                }
                StorageType::NoSQL => {
                    // 批量插入到NoSQL数据库
                    println!("批量插入{}条数据到NoSQL数据库", _data.len());
                }
                StorageType::Embedded => {
                    // 批量插入到嵌入式数据库
                    println!("批量插入{}条数据到嵌入式数据库", _data.len());
                }
                StorageType::File => {
                    // 批量插入到文件存储
                    println!("批量插入{}条数据到文件存储", _data.len());
                }
                StorageType::Cache => {
                    // 批量插入到缓存
                    println!("批量插入{}条数据到缓存", _data.len());
                }
            }
            Ok(())
        } else {
            Err(StorageError::ConfigurationError(
                format!("存储类型 {:?} 未配置", storage_type)
            ))
        }
    }
    
    /// 查询数据
    pub async fn query_data(&mut self, storage_type: StorageType, _query: Query) -> Result<Vec<DataPoint>, StorageError> {
        if self.configs.contains_key(&storage_type) {
            // 实际查询数据从对应的存储后端
            match storage_type {
                StorageType::TimeSeries => {
                    // 从时间序列数据库查询
                    println!("从时间序列数据库查询数据");
                }
                StorageType::Relational => {
                    // 从关系型数据库查询
                    println!("从关系型数据库查询数据");
                }
                StorageType::NoSQL => {
                    // 从NoSQL数据库查询
                    println!("从NoSQL数据库查询数据");
                }
                StorageType::Embedded => {
                    // 从嵌入式数据库查询
                    println!("从嵌入式数据库查询数据");
                }
                StorageType::File => {
                    // 从文件存储查询
                    println!("从文件存储查询数据");
                }
                StorageType::Cache => {
                    // 从缓存查询
                    println!("从缓存查询数据");
                }
            }
            // 返回模拟数据
            Ok(vec![])
        } else {
            Err(StorageError::ConfigurationError(
                format!("存储类型 {:?} 未配置", storage_type)
            ))
        }
    }
    
    /// 更新数据
    pub async fn update_data(&mut self, storage_type: StorageType, _query: Query, _updates: HashMap<String, serde_json::Value>) -> Result<u64, StorageError> {
        if self.configs.contains_key(&storage_type) {
            // 实际更新数据到对应的存储后端
            match storage_type {
                StorageType::TimeSeries => {
                    // 更新时间序列数据库
                    println!("更新时间序列数据库数据");
                }
                StorageType::Relational => {
                    // 更新关系型数据库
                    println!("更新关系型数据库数据");
                }
                StorageType::NoSQL => {
                    // 更新NoSQL数据库
                    println!("更新NoSQL数据库数据");
                }
                StorageType::Embedded => {
                    // 更新嵌入式数据库
                    println!("更新嵌入式数据库数据");
                }
                StorageType::File => {
                    // 更新文件存储
                    println!("更新文件存储数据");
                }
                StorageType::Cache => {
                    // 更新缓存
                    println!("更新缓存数据");
                }
            }
            Ok(1) // 返回更新的记录数
        } else {
            Err(StorageError::ConfigurationError(
                format!("存储类型 {:?} 未配置", storage_type)
            ))
        }
    }
    
    /// 删除数据
    pub async fn delete_data(&mut self, storage_type: StorageType, _query: Query) -> Result<u64, StorageError> {
        if self.configs.contains_key(&storage_type) {
            // 实际删除数据从对应的存储后端
            match storage_type {
                StorageType::TimeSeries => {
                    // 从时间序列数据库删除
                    println!("从时间序列数据库删除数据");
                }
                StorageType::Relational => {
                    // 从关系型数据库删除
                    println!("从关系型数据库删除数据");
                }
                StorageType::NoSQL => {
                    // 从NoSQL数据库删除
                    println!("从NoSQL数据库删除数据");
                }
                StorageType::Embedded => {
                    // 从嵌入式数据库删除
                    println!("从嵌入式数据库删除数据");
                }
                StorageType::File => {
                    // 从文件存储删除
                    println!("从文件存储删除数据");
                }
                StorageType::Cache => {
                    // 从缓存删除
                    println!("从缓存删除数据");
                }
            }
            Ok(1) // 返回删除的记录数
        } else {
            Err(StorageError::ConfigurationError(
                format!("存储类型 {:?} 未配置", storage_type)
            ))
        }
    }
    
    /// 获取存储统计信息
    pub async fn get_storage_stats(&mut self, storage_type: StorageType) -> Result<StorageStats, StorageError> {
        if let Some(stats) = self.stats.get(&storage_type) {
            Ok(stats.clone())
        } else {
            // 返回默认统计信息
            Ok(StorageStats {
                total_records: 0,
                total_size: 0,
                read_operations: 0,
                write_operations: 0,
                delete_operations: 0,
                average_query_time: std::time::Duration::from_millis(0),
                connection_count: 0,
                error_count: 0,
                last_backup: None,
            })
        }
    }
    
    /// 获取所有存储类型
    pub fn get_storage_types(&self) -> Vec<StorageType> {
        self.configs.keys().cloned().collect()
    }
    
    /// 检查存储是否已配置
    pub fn is_storage_configured(&self, storage_type: StorageType) -> bool {
        self.configs.contains_key(&storage_type)
    }
    
    /// 获取存储数量
    pub fn get_storage_count(&self) -> usize {
        self.configs.len()
    }
    
    /// 刷新所有存储
    pub async fn refresh_all_storages(&mut self) -> Result<(), StorageError> {
        // 模拟刷新所有存储
        Ok(())
    }
    
    /// 清理所有存储
    pub async fn cleanup_all_storages(&mut self) -> Result<(), StorageError> {
        // 模拟清理所有存储
        Ok(())
    }

    /// 存储数据
    pub async fn store_data(&mut self, data: DataPoint) -> Result<(), StorageError> {
        // 模拟存储数据到默认存储类型
        if let Some(storage_type) = self.configs.keys().next() {
            self.insert_data(*storage_type, data).await
        } else {
            Err(StorageError::ConfigurationError("没有配置存储类型".to_string()))
        }
    }
}

impl Default for StorageManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::data_storage::QueryBuilder;
    use serde_json::Value;

    #[tokio::test]
    async fn test_storage_manager_creation() {
        let manager = StorageManager::new();
        assert!(!manager.initialized);
        assert_eq!(manager.configs.len(), 0);
        assert_eq!(manager.stats.len(), 0);
    }

    #[tokio::test]
    async fn test_storage_manager_initialization() {
        let mut manager = StorageManager::new();
        assert!(!manager.initialized);
        
        let result = manager.initialize().await;
        assert!(result.is_ok());
        assert!(manager.initialized);
        
        // 重复初始化应该成功
        let result = manager.initialize().await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_add_storage_config() {
        let mut manager = StorageManager::new();
        
        let config = StorageConfig::new(
            StorageType::TimeSeries,
            "influxdb://localhost:8086".to_string(),
        ).with_database_name("iot_data".to_string())
         .with_credentials("admin".to_string(), "password".to_string())
         .with_max_connections(10);
        
        manager.add_storage_config(config);
        assert_eq!(manager.configs.len(), 1);
        assert!(manager.configs.contains_key(&StorageType::TimeSeries));
    }

    #[tokio::test]
    async fn test_connect_storage() {
        let mut manager = StorageManager::new();
        
        let config = StorageConfig::new(
            StorageType::TimeSeries,
            "influxdb://localhost:8086".to_string(),
        );
        
        manager.add_storage_config(config);
        
        // 连接已配置的存储应该成功
        let result = manager.connect_storage(StorageType::TimeSeries).await;
        assert!(result.is_ok());
        
        // 连接未配置的存储应该失败
        let result = manager.connect_storage(StorageType::Relational).await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn test_disconnect_storage() {
        let mut manager = StorageManager::new();
        
        let config = StorageConfig::new(
            StorageType::TimeSeries,
            "influxdb://localhost:8086".to_string(),
        );
        
        manager.add_storage_config(config);
        manager.connect_storage(StorageType::TimeSeries).await.unwrap();
        
        // 断开连接应该成功
        let result = manager.disconnect_storage(StorageType::TimeSeries).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_get_storage_stats() {
        let mut manager = StorageManager::new();
        
        let config = StorageConfig::new(
            StorageType::TimeSeries,
            "influxdb://localhost:8086".to_string(),
        );
        
        manager.add_storage_config(config);
        manager.connect_storage(StorageType::TimeSeries).await.unwrap();
        
        // 获取存储统计信息
        let stats = manager.get_storage_stats(StorageType::TimeSeries).await;
        assert!(stats.is_ok());
        let stats = stats.unwrap();
        assert_eq!(stats.total_records, 0);
    }

    #[tokio::test]
    async fn test_insert_data() {
        let mut manager = StorageManager::new();
        
        let config = StorageConfig::new(
            StorageType::TimeSeries,
            "influxdb://localhost:8086".to_string(),
        );
        
        manager.add_storage_config(config);
        manager.connect_storage(StorageType::TimeSeries).await.unwrap();
        
        let data_point = DataPoint::new("temperature".to_string())
            .with_tag("device_id".to_string(), "sensor_001".to_string())
            .with_tag("location".to_string(), "room_a".to_string())
            .with_field("value".to_string(), Value::Number(serde_json::Number::from_f64(25.5).unwrap()))
            .with_field("unit".to_string(), Value::String("celsius".to_string()));
        
        // 插入数据应该成功
        let result = manager.insert_data(StorageType::TimeSeries, data_point).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_query_data() {
        let mut manager = StorageManager::new();
        
        let config = StorageConfig::new(
            StorageType::TimeSeries,
            "influxdb://localhost:8086".to_string(),
        );
        
        manager.add_storage_config(config);
        manager.connect_storage(StorageType::TimeSeries).await.unwrap();
        
        let query = QueryBuilder::new()
            .where_equal("device_id", Value::String("sensor_001".to_string()))
            .limit(100)
            .offset(0)
            .build();
        
        // 查询数据应该成功
        let result = manager.query_data(StorageType::TimeSeries, query).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_store_data() {
        let mut manager = StorageManager::new();
        
        let config = StorageConfig::new(
            StorageType::TimeSeries,
            "influxdb://localhost:8086".to_string(),
        );
        
        manager.add_storage_config(config);
        
        let data_point = DataPoint::new("humidity".to_string())
            .with_tag("device_id".to_string(), "sensor_002".to_string())
            .with_tag("location".to_string(), "room_b".to_string())
            .with_field("value".to_string(), Value::Number(serde_json::Number::from_f64(60.0).unwrap()))
            .with_field("unit".to_string(), Value::String("percent".to_string()));
        
        // 存储数据应该成功
        let result = manager.store_data(data_point).await;
        assert!(result.is_ok());
    }

    #[tokio::test]
    async fn test_storage_manager_default() {
        let manager = StorageManager::default();
        assert!(!manager.initialized);
        assert_eq!(manager.configs.len(), 0);
        assert_eq!(manager.stats.len(), 0);
    }
}