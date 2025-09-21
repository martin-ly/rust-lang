//! 数据存储模块
//! 
//! 本模块提供了基于Rust 1.90的IoT数据存储解决方案，包括：
//! - 时间序列数据库 (InfluxDB, TimescaleDB)
//! - 关系型数据库 (PostgreSQL, MySQL)
//! - NoSQL数据库 (MongoDB, Redis)
//! - 嵌入式数据库 (SQLite, Sled)
//! - 文件存储 (本地文件系统, 云存储)
//! - 缓存系统 (Redis, Memcached)
//! - 数据备份和恢复
//! - 数据压缩和归档

pub mod traits;
pub mod timeseries;
pub mod relational;
pub mod nosql;
pub mod embedded;
pub mod file_storage;
pub mod cache;
pub mod backup;
pub mod compression;
pub mod storage_manager;
pub mod cache_optimizer;

pub use traits::StorageInterface;
pub use timeseries::{TimeSeriesDB, InfluxDBClient, TimescaleDBClient, TimeSeriesError};
pub use relational::{RelationalDB, PostgreSQLClient, MySQLClient, RelationalError};
pub use nosql::{NoSQLDB, MongoDBClient, RedisClient, NoSQLError};
pub use embedded::{EmbeddedDB, SQLiteClient, SledClient, EmbeddedError};
pub use file_storage::{FileStorage, LocalFileStorage, CloudFileStorage, FileStorageError};
pub use cache::{CacheSystem, RedisCache, MemoryCache, CacheError};
pub use backup::{BackupManager, BackupStrategy, BackupError};
pub use compression::{CompressionManager, CompressionAlgorithm, CompressionError};
pub use storage_manager::StorageManager;
pub use cache_optimizer::{
    CacheOptimizer, CacheLevel, CacheStrategy, CacheItem, CacheStats, CacheConfig,
    PrewarmingStrategy, CacheOptimizationResult, CacheOptimization, CacheOptimizationType,
    CacheOptimizerError
};

/// 数据存储错误类型
#[derive(Debug, thiserror::Error)]
pub enum StorageError {
    #[error("连接失败: {0}")]
    ConnectionFailed(String),
    
    #[error("查询失败: {0}")]
    QueryFailed(String),
    
    #[error("插入失败: {0}")]
    InsertFailed(String),
    
    #[error("更新失败: {0}")]
    UpdateFailed(String),
    
    #[error("删除失败: {0}")]
    DeleteFailed(String),
    
    #[error("事务失败: {0}")]
    TransactionFailed(String),
    
    #[error("序列化失败: {0}")]
    SerializationFailed(String),
    
    #[error("反序列化失败: {0}")]
    DeserializationFailed(String),
    
    #[error("配置错误: {0}")]
    ConfigurationError(String),
    
    #[error("权限错误: {0}")]
    PermissionError(String),
    
    #[error("空间不足: {0}")]
    InsufficientSpace(String),
    
    #[error("备份失败: {0}")]
    BackupFailed(String),
    
    #[error("恢复失败: {0}")]
    RestoreFailed(String),
    
    #[error("压缩失败: {0}")]
    CompressionFailed(String),
    
    #[error("解压缩失败: {0}")]
    DecompressionFailed(String),
}

/// 存储类型
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StorageType {
    /// 时间序列数据库
    TimeSeries,
    /// 关系型数据库
    Relational,
    /// NoSQL数据库
    NoSQL,
    /// 嵌入式数据库
    Embedded,
    /// 文件存储
    File,
    /// 缓存系统
    Cache,
}

/// 数据点
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct DataPoint {
    pub timestamp: chrono::DateTime<chrono::Utc>,
    pub measurement: String,
    pub tags: std::collections::HashMap<String, String>,
    pub fields: std::collections::HashMap<String, serde_json::Value>,
}

impl DataPoint {
    /// 创建新的数据点
    pub fn new(measurement: String) -> Self {
        Self {
            timestamp: chrono::Utc::now(),
            measurement,
            tags: std::collections::HashMap::new(),
            fields: std::collections::HashMap::new(),
        }
    }

    /// 添加标签
    pub fn with_tag(mut self, key: String, value: String) -> Self {
        self.tags.insert(key, value);
        self
    }

    /// 添加字段
    pub fn with_field(mut self, key: String, value: serde_json::Value) -> Self {
        self.fields.insert(key, value);
        self
    }

    /// 设置时间戳
    pub fn with_timestamp(mut self, timestamp: chrono::DateTime<chrono::Utc>) -> Self {
        self.timestamp = timestamp;
        self
    }
}

/// 查询条件
#[derive(Debug, Clone)]
pub struct QueryCondition {
    pub field: String,
    pub operator: QueryOperator,
    pub value: serde_json::Value,
}

/// 查询操作符
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QueryOperator {
    /// 等于
    Equal,
    /// 不等于
    NotEqual,
    /// 大于
    GreaterThan,
    /// 大于等于
    GreaterThanOrEqual,
    /// 小于
    LessThan,
    /// 小于等于
    LessThanOrEqual,
    /// 包含
    Contains,
    /// 正则表达式
    Regex,
    /// 在范围内
    In,
    /// 不在范围内
    NotIn,
}

/// 查询构建器
pub struct QueryBuilder {
    conditions: Vec<QueryCondition>,
    order_by: Option<(String, bool)>, // (field, ascending)
    limit: Option<usize>,
    offset: Option<usize>,
}

impl QueryBuilder {
    /// 创建新的查询构建器
    pub fn new() -> Self {
        Self {
            conditions: Vec::new(),
            order_by: None,
            limit: None,
            offset: None,
        }
    }

    /// 添加条件
    pub fn where_condition(mut self, condition: QueryCondition) -> Self {
        self.conditions.push(condition);
        self
    }

    /// 添加等于条件
    pub fn where_equal(mut self, field: &str, value: serde_json::Value) -> Self {
        self.conditions.push(QueryCondition {
            field: field.to_string(),
            operator: QueryOperator::Equal,
            value,
        });
        self
    }

    /// 添加大于条件
    pub fn where_greater_than(mut self, field: &str, value: serde_json::Value) -> Self {
        self.conditions.push(QueryCondition {
            field: field.to_string(),
            operator: QueryOperator::GreaterThan,
            value,
        });
        self
    }

    /// 添加小于条件
    pub fn where_less_than(mut self, field: &str, value: serde_json::Value) -> Self {
        self.conditions.push(QueryCondition {
            field: field.to_string(),
            operator: QueryOperator::LessThan,
            value,
        });
        self
    }

    /// 设置排序
    pub fn order_by(mut self, field: &str, ascending: bool) -> Self {
        self.order_by = Some((field.to_string(), ascending));
        self
    }

    /// 设置限制
    pub fn limit(mut self, limit: u64) -> Self {
        self.limit = Some(limit.try_into().unwrap_or(usize::MAX));
        self
    }

    /// 设置偏移
    pub fn offset(mut self, offset: u64) -> Self {
        self.offset = Some(offset.try_into().unwrap_or(usize::MAX));
        self
    }

    /// 构建查询
    pub fn build(self) -> Query {
        Query {
            conditions: self.conditions,
            order_by: self.order_by,
            limit: self.limit,
            offset: self.offset,
        }
    }
}

/// 查询
#[derive(Debug, Clone)]
pub struct Query {
    pub conditions: Vec<QueryCondition>,
    pub order_by: Option<(String, bool)>,
    pub limit: Option<usize>,
    pub offset: Option<usize>,
}

/// 存储配置
#[derive(Debug, Clone)]
pub struct StorageConfig {
    pub storage_type: StorageType,
    pub connection_string: String,
    pub database_name: String,
    pub username: Option<String>,
    pub password: Option<String>,
    pub max_connections: Option<u32>,
    pub connection_timeout: Option<std::time::Duration>,
    pub query_timeout: Option<std::time::Duration>,
    pub enable_ssl: bool,
    pub enable_compression: bool,
    pub backup_enabled: bool,
    pub backup_interval: Option<std::time::Duration>,
    pub retention_policy: Option<String>,
}

impl StorageConfig {
    /// 创建新的存储配置
    pub fn new(storage_type: StorageType, connection_string: String) -> Self {
        Self {
            storage_type,
            connection_string,
            database_name: "iot_db".to_string(),
            username: None,
            password: None,
            max_connections: Some(10),
            connection_timeout: Some(std::time::Duration::from_secs(30)),
            query_timeout: Some(std::time::Duration::from_secs(60)),
            enable_ssl: false,
            enable_compression: true,
            backup_enabled: false,
            backup_interval: None,
            retention_policy: None,
        }
    }

    /// 设置数据库名称
    pub fn with_database_name(mut self, database_name: String) -> Self {
        self.database_name = database_name;
        self
    }

    /// 设置认证信息
    pub fn with_credentials(mut self, username: String, password: String) -> Self {
        self.username = Some(username);
        self.password = Some(password);
        self
    }

    /// 设置最大连接数
    pub fn with_max_connections(mut self, max_connections: u32) -> Self {
        self.max_connections = Some(max_connections);
        self
    }

    /// 启用SSL
    pub fn with_ssl(mut self, enable: bool) -> Self {
        self.enable_ssl = enable;
        self
    }

    /// 启用压缩
    pub fn with_compression(mut self, enable: bool) -> Self {
        self.enable_compression = enable;
        self
    }

    /// 启用备份
    pub fn with_backup(mut self, interval: std::time::Duration) -> Self {
        self.backup_enabled = true;
        self.backup_interval = Some(interval);
        self
    }
}

/// 存储统计信息
#[derive(Debug, Clone)]
pub struct StorageStats {
    pub total_records: u64,
    pub total_size: u64,
    pub read_operations: u64,
    pub write_operations: u64,
    pub delete_operations: u64,
    pub average_query_time: std::time::Duration,
    pub connection_count: u32,
    pub error_count: u64,
    pub last_backup: Option<chrono::DateTime<chrono::Utc>>,
}


/// 存储结果类型
pub type StorageResult<T> = Result<T, StorageError>;
