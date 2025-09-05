//! 数据库最佳实践示例
//! 
//! 展示Rust中不同数据库的操作模式和最佳实践

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::Duration;
use tokio::time::sleep;
use uuid::Uuid;

/// 用户模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: Uuid,
    pub name: String,
    pub email: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
    pub updated_at: chrono::DateTime<chrono::Utc>,
}

/// 订单模型
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Order {
    pub id: Uuid,
    pub user_id: Uuid,
    pub product_name: String,
    pub amount: f64,
    pub status: OrderStatus,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum OrderStatus {
    Pending,
    Processing,
    Shipped,
    Delivered,
    Cancelled,
}

/// 数据库连接池配置
#[derive(Debug, Clone)]
pub struct DatabaseConfig {
    pub max_connections: u32,
    pub min_connections: u32,
    pub connection_timeout: Duration,
    pub idle_timeout: Duration,
    pub max_lifetime: Duration,
}

impl Default for DatabaseConfig {
    fn default() -> Self {
        Self {
            max_connections: 10,
            min_connections: 1,
            connection_timeout: Duration::from_secs(30),
            idle_timeout: Duration::from_secs(600),
            max_lifetime: Duration::from_secs(1800),
        }
    }
}

/// 数据库操作结果
#[derive(Debug)]
pub enum DatabaseResult<T> {
    Success(T),
    NotFound,
    Conflict(String),
    Timeout,
    ConnectionError(String),
    QueryError(String),
}

impl<T> DatabaseResult<T> {
    pub fn is_success(&self) -> bool {
        matches!(self, DatabaseResult::Success(_))
    }
    
    pub fn unwrap_or_default(self) -> T 
    where 
        T: Default 
    {
        match self {
            DatabaseResult::Success(value) => value,
            _ => T::default(),
        }
    }
}

/// 数据库操作trait
pub trait DatabaseOperations {
    type Connection;
    type Error;
    
    /// 建立连接
    async fn connect(&self) -> Result<Self::Connection, Self::Error>;
    
    /// 执行事务
    async fn execute_transaction<F, R>(&self, f: F) -> Result<R, Self::Error>
    where
        F: FnOnce(&mut Self::Connection) -> Result<R, Self::Error> + Send + Sync;
    
    /// 健康检查
    async fn health_check(&self) -> Result<bool, Self::Error>;
}

/// PostgreSQL 数据库操作实现
pub struct PostgresDatabase {
    config: DatabaseConfig,
    connection_string: String,
}

impl PostgresDatabase {
    pub fn new(connection_string: String, config: DatabaseConfig) -> Self {
        Self {
            config,
            connection_string,
        }
    }
    
    /// 创建用户表
    pub async fn create_user_table(&self) -> DatabaseResult<()> {
        // 模拟创建表
        sleep(Duration::from_millis(100)).await;
        println!("✅ PostgreSQL: 用户表创建成功");
        DatabaseResult::Success(())
    }
    
    /// 插入用户
    pub async fn insert_user(&self, user: &User) -> DatabaseResult<User> {
        // 模拟插入操作
        sleep(Duration::from_millis(50)).await;
        println!("✅ PostgreSQL: 用户 {} 插入成功", user.name);
        DatabaseResult::Success(user.clone())
    }
    
    /// 查询用户
    pub async fn get_user(&self, id: Uuid) -> DatabaseResult<User> {
        // 模拟查询操作
        sleep(Duration::from_millis(30)).await;
        
        if id == Uuid::nil() {
            return DatabaseResult::NotFound;
        }
        
        let user = User {
            id,
            name: "示例用户".to_string(),
            email: "user@example.com".to_string(),
            created_at: chrono::Utc::now(),
            updated_at: chrono::Utc::now(),
        };
        
        println!("✅ PostgreSQL: 用户 {} 查询成功", user.name);
        DatabaseResult::Success(user)
    }
    
    /// 批量插入
    pub async fn batch_insert_users(&self, users: &[User]) -> DatabaseResult<Vec<User>> {
        // 模拟批量插入
        sleep(Duration::from_millis(users.len() as u64 * 10)).await;
        println!("✅ PostgreSQL: 批量插入 {} 个用户成功", users.len());
        DatabaseResult::Success(users.to_vec())
    }
    
    /// 复杂查询
    pub async fn search_users(&self, query: &str, limit: usize) -> DatabaseResult<Vec<User>> {
        // 模拟复杂查询
        sleep(Duration::from_millis(200)).await;
        
        let users: Vec<User> = (0..limit.min(5))
            .map(|i| User {
                id: Uuid::new_v4(),
                name: format!("用户{}", i + 1),
                email: format!("user{}@example.com", i + 1),
                created_at: chrono::Utc::now(),
                updated_at: chrono::Utc::now(),
            })
            .collect();
        
        println!("✅ PostgreSQL: 搜索 '{}' 返回 {} 个结果", query, users.len());
        DatabaseResult::Success(users)
    }
}

/// Redis 缓存操作
pub struct RedisCache {
    config: DatabaseConfig,
    connection_string: String,
}

impl RedisCache {
    pub fn new(connection_string: String, config: DatabaseConfig) -> Self {
        Self {
            config,
            connection_string,
        }
    }
    
    /// 设置缓存
    pub async fn set(&self, key: &str, value: &str, ttl: Duration) -> DatabaseResult<()> {
        // 模拟Redis SET操作
        sleep(Duration::from_millis(5)).await;
        println!("✅ Redis: 设置缓存 {} = {}", key, value);
        DatabaseResult::Success(())
    }
    
    /// 获取缓存
    pub async fn get(&self, key: &str) -> DatabaseResult<Option<String>> {
        // 模拟Redis GET操作
        sleep(Duration::from_millis(3)).await;
        
        if key == "not_found" {
            return DatabaseResult::Success(None);
        }
        
        let value = format!("cached_value_for_{}", key);
        println!("✅ Redis: 获取缓存 {} = {}", key, value);
        DatabaseResult::Success(Some(value))
    }
    
    /// 删除缓存
    pub async fn delete(&self, key: &str) -> DatabaseResult<bool> {
        // 模拟Redis DEL操作
        sleep(Duration::from_millis(2)).await;
        println!("✅ Redis: 删除缓存 {}", key);
        DatabaseResult::Success(true)
    }
    
    /// 批量设置
    pub async fn mset(&self, pairs: &HashMap<String, String>) -> DatabaseResult<()> {
        // 模拟Redis MSET操作
        sleep(Duration::from_millis(pairs.len() as u64 * 2)).await;
        println!("✅ Redis: 批量设置 {} 个键值对", pairs.len());
        DatabaseResult::Success(())
    }
    
    /// 设置过期时间
    pub async fn expire(&self, key: &str, ttl: Duration) -> DatabaseResult<bool> {
        // 模拟Redis EXPIRE操作
        sleep(Duration::from_millis(1)).await;
        println!("✅ Redis: 设置 {} 过期时间 {} 秒", key, ttl.as_secs());
        DatabaseResult::Success(true)
    }
}

/// MongoDB 文档数据库操作
pub struct MongoDatabase {
    config: DatabaseConfig,
    connection_string: String,
}

impl MongoDatabase {
    pub fn new(connection_string: String, config: DatabaseConfig) -> Self {
        Self {
            config,
            connection_string,
        }
    }
    
    /// 插入文档
    pub async fn insert_document(&self, collection: &str, _document: &serde_json::Value) -> DatabaseResult<String> {
        // 模拟MongoDB插入操作
        sleep(Duration::from_millis(80)).await;
        let id = Uuid::new_v4().to_string();
        println!("✅ MongoDB: 在集合 {} 中插入文档 {}", collection, id);
        DatabaseResult::Success(id)
    }
    
    /// 查询文档
    pub async fn find_document(&self, collection: &str, _filter: &serde_json::Value) -> DatabaseResult<Option<serde_json::Value>> {
        // 模拟MongoDB查询操作
        sleep(Duration::from_millis(60)).await;
        
        let document = serde_json::json!({
            "_id": Uuid::new_v4().to_string(),
            "name": "示例文档",
            "data": "这是示例数据",
            "created_at": chrono::Utc::now()
        });
        
        println!("✅ MongoDB: 在集合 {} 中查询到文档", collection);
        DatabaseResult::Success(Some(document))
    }
    
    /// 更新文档
    pub async fn update_document(&self, collection: &str, _filter: &serde_json::Value, _update: &serde_json::Value) -> DatabaseResult<u64> {
        // 模拟MongoDB更新操作
        sleep(Duration::from_millis(70)).await;
        println!("✅ MongoDB: 在集合 {} 中更新文档", collection);
        DatabaseResult::Success(1)
    }
    
    /// 聚合查询
    pub async fn aggregate(&self, collection: &str, pipeline: &[serde_json::Value]) -> DatabaseResult<Vec<serde_json::Value>> {
        // 模拟MongoDB聚合操作
        sleep(Duration::from_millis(150)).await;
        
        let results = vec![
            serde_json::json!({
                "_id": "category1",
                "count": 10,
                "total_amount": 1000.0
            }),
            serde_json::json!({
                "_id": "category2", 
                "count": 5,
                "total_amount": 500.0
            })
        ];
        
        println!("✅ MongoDB: 聚合查询返回 {} 个结果", results.len());
        DatabaseResult::Success(results)
    }
}

/// 数据库连接池管理
pub struct ConnectionPool<T> {
    connections: Vec<T>,
    config: DatabaseConfig,
    current_size: usize,
}

impl<T> ConnectionPool<T> {
    pub fn new(config: DatabaseConfig) -> Self {
        Self {
            connections: Vec::new(),
            config,
            current_size: 0,
        }
    }
    
    /// 获取连接
    pub async fn get_connection(&mut self) -> Option<T> {
        if self.connections.is_empty() {
            if self.current_size < self.config.max_connections as usize {
                // 创建新连接
                self.current_size += 1;
                println!("🔗 创建新连接，当前连接数: {}", self.current_size);
                return None; // 实际实现中会创建新连接
            } else {
                println!("❌ 连接池已满，无法获取连接");
                return None;
            }
        }
        
        let connection = self.connections.pop().unwrap();
        println!("🔗 从连接池获取连接，剩余连接数: {}", self.connections.len());
        Some(connection)
    }
    
    /// 归还连接
    pub fn return_connection(&mut self, connection: T) {
        if self.connections.len() < self.config.max_connections as usize {
            self.connections.push(connection);
            println!("🔗 连接已归还，当前连接数: {}", self.connections.len());
        } else {
            println!("🔗 连接池已满，丢弃连接");
        }
    }
    
    /// 健康检查
    pub async fn health_check(&self) -> bool {
        println!("🏥 执行连接池健康检查");
        self.current_size > 0
    }
}

/// 数据库事务管理
pub struct TransactionManager {
    transactions: HashMap<String, TransactionState>,
}

#[derive(Debug, Clone)]
pub enum TransactionState {
    Started,
    Committed,
    RolledBack,
    Failed(String),
}

impl TransactionManager {
    pub fn new() -> Self {
        Self {
            transactions: HashMap::new(),
        }
    }
    
    /// 开始事务
    pub async fn begin_transaction(&mut self, id: &str) -> DatabaseResult<()> {
        println!("🔄 开始事务: {}", id);
        self.transactions.insert(id.to_string(), TransactionState::Started);
        DatabaseResult::Success(())
    }
    
    /// 提交事务
    pub async fn commit_transaction(&mut self, id: &str) -> DatabaseResult<()> {
        if let Some(state) = self.transactions.get_mut(id) {
            *state = TransactionState::Committed;
            println!("✅ 提交事务: {}", id);
            DatabaseResult::Success(())
        } else {
            DatabaseResult::NotFound
        }
    }
    
    /// 回滚事务
    pub async fn rollback_transaction(&mut self, id: &str) -> DatabaseResult<()> {
        if let Some(state) = self.transactions.get_mut(id) {
            *state = TransactionState::RolledBack;
            println!("🔄 回滚事务: {}", id);
            DatabaseResult::Success(())
        } else {
            DatabaseResult::NotFound
        }
    }
    
    /// 获取事务状态
    pub fn get_transaction_state(&self, id: &str) -> Option<&TransactionState> {
        self.transactions.get(id)
    }
}

/// 数据库迁移管理
pub struct MigrationManager {
    migrations: Vec<Migration>,
    applied_migrations: Vec<String>,
}

#[derive(Debug, Clone)]
pub struct Migration {
    pub version: String,
    pub name: String,
    pub up_sql: String,
    pub down_sql: String,
}

impl MigrationManager {
    pub fn new() -> Self {
        Self {
            migrations: Vec::new(),
            applied_migrations: Vec::new(),
        }
    }
    
    /// 添加迁移
    pub fn add_migration(&mut self, migration: Migration) {
        self.migrations.push(migration);
    }
    
    /// 执行迁移
    pub async fn migrate(&mut self) -> DatabaseResult<()> {
        println!("🔄 开始执行数据库迁移");
        
        for migration in &self.migrations {
            if !self.applied_migrations.contains(&migration.version) {
                println!("📝 执行迁移: {} - {}", migration.version, migration.name);
                sleep(Duration::from_millis(100)).await;
                self.applied_migrations.push(migration.version.clone());
                println!("✅ 迁移 {} 执行成功", migration.version);
            }
        }
        
        println!("✅ 所有迁移执行完成");
        DatabaseResult::Success(())
    }
    
    /// 回滚迁移
    pub async fn rollback(&mut self, version: &str) -> DatabaseResult<()> {
        println!("🔄 回滚迁移到版本: {}", version);
        
        for migration in self.migrations.iter().rev() {
            if migration.version.as_str() > version && self.applied_migrations.contains(&migration.version) {
                println!("📝 回滚迁移: {} - {}", migration.version, migration.name);
                sleep(Duration::from_millis(100)).await;
                self.applied_migrations.retain(|v| v != &migration.version);
                println!("✅ 迁移 {} 回滚成功", migration.version);
            }
        }
        
        DatabaseResult::Success(())
    }
}

#[tokio::main]
async fn main() {
    println!("🚀 数据库最佳实践示例");
    println!("========================");
    
    // 1. PostgreSQL 操作示例
    println!("\n📊 PostgreSQL 数据库操作:");
    let postgres = PostgresDatabase::new(
        "postgresql://localhost/mydb".to_string(),
        DatabaseConfig::default(),
    );
    
    // 创建表
    postgres.create_user_table().await;
    
    // 插入用户
    let user = User {
        id: Uuid::new_v4(),
        name: "张三".to_string(),
        email: "zhangsan@example.com".to_string(),
        created_at: chrono::Utc::now(),
        updated_at: chrono::Utc::now(),
    };
    postgres.insert_user(&user).await;
    
    // 查询用户
    postgres.get_user(user.id).await;
    
    // 批量插入
    let users = vec![
        User {
            id: Uuid::new_v4(),
            name: "李四".to_string(),
            email: "lisi@example.com".to_string(),
            created_at: chrono::Utc::now(),
            updated_at: chrono::Utc::now(),
        },
        User {
            id: Uuid::new_v4(),
            name: "王五".to_string(),
            email: "wangwu@example.com".to_string(),
            created_at: chrono::Utc::now(),
            updated_at: chrono::Utc::now(),
        },
    ];
    postgres.batch_insert_users(&users).await;
    
    // 复杂查询
    postgres.search_users("张", 10).await;
    
    // 2. Redis 缓存操作示例
    println!("\n💾 Redis 缓存操作:");
    let redis = RedisCache::new(
        "redis://localhost:6379".to_string(),
        DatabaseConfig::default(),
    );
    
    // 设置缓存
    redis.set("user:1", "张三", Duration::from_secs(3600)).await;
    redis.set("user:2", "李四", Duration::from_secs(3600)).await;
    
    // 获取缓存
    redis.get("user:1").await;
    redis.get("not_found").await;
    
    // 批量设置
    let mut cache_data = HashMap::new();
    cache_data.insert("key1".to_string(), "value1".to_string());
    cache_data.insert("key2".to_string(), "value2".to_string());
    redis.mset(&cache_data).await;
    
    // 设置过期时间
    redis.expire("user:1", Duration::from_secs(1800)).await;
    
    // 删除缓存
    redis.delete("user:2").await;
    
    // 3. MongoDB 文档数据库操作示例
    println!("\n📄 MongoDB 文档数据库操作:");
    let mongo = MongoDatabase::new(
        "mongodb://localhost:27017/mydb".to_string(),
        DatabaseConfig::default(),
    );
    
    // 插入文档
    let document = serde_json::json!({
        "name": "产品A",
        "price": 99.99,
        "category": "电子产品",
        "in_stock": true
    });
    mongo.insert_document("products", &document).await;
    
    // 查询文档
    let filter = serde_json::json!({"category": "电子产品"});
    mongo.find_document("products", &filter).await;
    
    // 更新文档
    let update = serde_json::json!({"$set": {"price": 89.99}});
    mongo.update_document("products", &filter, &update).await;
    
    // 聚合查询
    let pipeline = vec![
        serde_json::json!({"$match": {"category": "电子产品"}}),
        serde_json::json!({"$group": {"_id": "$category", "count": {"$sum": 1}, "avg_price": {"$avg": "$price"}}})
    ];
    mongo.aggregate("products", &pipeline).await;
    
    // 4. 连接池管理示例
    println!("\n🔗 连接池管理:");
    let mut pool: ConnectionPool<String> = ConnectionPool::new(DatabaseConfig::default());
    
    // 获取连接
    pool.get_connection().await;
    pool.get_connection().await;
    
    // 归还连接
    pool.return_connection("connection1".to_string());
    pool.return_connection("connection2".to_string());
    
    // 健康检查
    pool.health_check().await;
    
    // 5. 事务管理示例
    println!("\n🔄 事务管理:");
    let mut tx_manager = TransactionManager::new();
    
    // 开始事务
    tx_manager.begin_transaction("tx1").await;
    tx_manager.begin_transaction("tx2").await;
    
    // 提交事务
    tx_manager.commit_transaction("tx1").await;
    
    // 回滚事务
    tx_manager.rollback_transaction("tx2").await;
    
    // 6. 数据库迁移示例
    println!("\n📝 数据库迁移:");
    let mut migration_manager = MigrationManager::new();
    
    // 添加迁移
    migration_manager.add_migration(Migration {
        version: "001".to_string(),
        name: "创建用户表".to_string(),
        up_sql: "CREATE TABLE users (id UUID PRIMARY KEY, name VARCHAR(100), email VARCHAR(100))".to_string(),
        down_sql: "DROP TABLE users".to_string(),
    });
    
    migration_manager.add_migration(Migration {
        version: "002".to_string(),
        name: "创建订单表".to_string(),
        up_sql: "CREATE TABLE orders (id UUID PRIMARY KEY, user_id UUID, amount DECIMAL(10,2))".to_string(),
        down_sql: "DROP TABLE orders".to_string(),
    });
    
    // 执行迁移
    migration_manager.migrate().await;
    
    // 回滚迁移
    migration_manager.rollback("001").await;
    
    println!("\n✅ 数据库最佳实践示例完成！");
}
