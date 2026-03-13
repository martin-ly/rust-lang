//! 异步数据库操作示例
//! 
//! 展示如何使用异步编程进行数据库操作
use std::sync::Arc;
use std::time::Duration;
use anyhow::Result;
use tokio::time::sleep;
use serde::{Deserialize, Serialize};
use tokio::sync::RwLock;
use std::collections::HashMap;

/// 用户数据结构
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: u64,
    pub name: String,
    pub email: String,
    pub created_at: chrono::DateTime<chrono::Utc>,
}

/// 数据库连接池
pub struct DatabaseConnectionPool {
    connections: Arc<RwLock<Vec<DatabaseConnection>>>,
    max_connections: usize,
}

impl DatabaseConnectionPool {
    pub fn new(max_connections: usize) -> Self {
        Self {
            connections: Arc::new(RwLock::new(Vec::new())),
            max_connections,
        }
    }
    
    /// 获取数据库连接
    pub async fn get_connection(&self) -> Result<DatabaseConnection> {
        let mut connections = self.connections.write().await;
        
        if let Some(connection) = connections.pop() {
            Ok(connection)
        } else {
            // 创建新连接
            Ok(DatabaseConnection::new().await?)
        }
    }
    
    /// 归还数据库连接
    pub async fn return_connection(&self, mut connection: DatabaseConnection) {
        let mut connections = self.connections.write().await;
        
        if connections.len() < self.max_connections {
            connection.reset().await;
            connections.push(connection);
        }
    }
}

/// 数据库连接
pub struct DatabaseConnection {
    pub id: u64,
    pub is_active: bool,
    pub last_used: chrono::DateTime<chrono::Utc>,
}

impl DatabaseConnection {
    pub async fn new() -> Result<Self> {
        // 模拟数据库连接建立时间
        sleep(Duration::from_millis(100)).await;
        
        Ok(Self {
            id: rand::random::<u64>(),
            is_active: true,
            last_used: chrono::Utc::now(),
        })
    }
    
    pub async fn reset(&mut self) {
        self.is_active = true;
        self.last_used = chrono::Utc::now();
    }
    
    /// 执行查询
    pub async fn query(&mut self, _sql: &str) -> Result<Vec<User>> {
        // 模拟数据库查询时间
        sleep(Duration::from_millis(50)).await;
        
        self.last_used = chrono::Utc::now();
        
        // 模拟查询结果
        let users = vec![
            User {
                id: 1,
                name: "张三".to_string(),
                email: "zhangsan@example.com".to_string(),
                created_at: chrono::Utc::now(),
            },
            User {
                id: 2,
                name: "李四".to_string(),
                email: "lisi@example.com".to_string(),
                created_at: chrono::Utc::now(),
            },
        ];
        
        Ok(users)
    }
    
    /// 执行插入
    pub async fn insert(&mut self, _user: &User) -> Result<u64> {
        // 模拟数据库插入时间
        sleep(Duration::from_millis(30)).await;
        
        self.last_used = chrono::Utc::now();
        
        // 模拟插入成功，返回新ID
        Ok(rand::random::<u64>())
    }
    
    /// 执行更新
    pub async fn update(&mut self, _id: u64, _user: &User) -> Result<bool> {
        // 模拟数据库更新时间
        sleep(Duration::from_millis(40)).await;
        
        self.last_used = chrono::Utc::now();
        
        // 模拟更新成功
        Ok(true)
    }
    
    /// 执行删除
    pub async fn delete(&mut self, _id: u64) -> Result<bool> {
        // 模拟数据库删除时间
        sleep(Duration::from_millis(20)).await;
        
        self.last_used = chrono::Utc::now();
        
        // 模拟删除成功
        Ok(true)
    }
}

/// 异步用户服务
pub struct AsyncUserService {
    connection_pool: Arc<DatabaseConnectionPool>,
    cache: Arc<RwLock<HashMap<u64, User>>>,
}

impl AsyncUserService {
    pub fn new(connection_pool: Arc<DatabaseConnectionPool>) -> Self {
        Self {
            connection_pool,
            cache: Arc::new(RwLock::new(HashMap::new())),
        }
    }
    
    /// 获取所有用户
    pub async fn get_all_users(&self) -> Result<Vec<User>> {
        println!("🔍 查询所有用户");
        
        let mut connection = self.connection_pool.get_connection().await?;
        let users = connection.query("SELECT * FROM users").await?;
        
        // 更新缓存
        {
            let mut cache = self.cache.write().await;
            for user in &users {
                cache.insert(user.id, user.clone());
            }
        }
        
        self.connection_pool.return_connection(connection).await;
        
        println!("✅ 查询完成，找到 {} 个用户", users.len());
        Ok(users)
    }
    
    /// 根据ID获取用户
    pub async fn get_user_by_id(&self, id: u64) -> Result<Option<User>> {
        println!("🔍 查询用户 ID: {}", id);
        
        // 先检查缓存
        {
            let cache = self.cache.read().await;
            if let Some(user) = cache.get(&id) {
                println!("📦 从缓存获取用户");
                return Ok(Some(user.clone()));
            }
        }
        
        // 从数据库查询
        let mut connection = self.connection_pool.get_connection().await?;
        let users = connection.query(&format!("SELECT * FROM users WHERE id = {}", id)).await?;
        
        let user = users.into_iter().next();
        
        // 更新缓存
        if let Some(ref user) = user {
            let mut cache = self.cache.write().await;
            cache.insert(user.id, user.clone());
        }
        
        self.connection_pool.return_connection(connection).await;
        
        if user.is_some() {
            println!("✅ 从数据库获取用户");
        } else {
            println!("❌ 用户不存在");
        }
        
        Ok(user)
    }
    
    /// 创建新用户
    pub async fn create_user(&self, name: String, email: String) -> Result<User> {
        println!("➕ 创建新用户: {} ({})", name, email);
        
        let user = User {
            id: 0, // 将由数据库分配
            name: name.clone(),
            email: email.clone(),
            created_at: chrono::Utc::now(),
        };
        
        let mut connection = self.connection_pool.get_connection().await?;
        let new_id = connection.insert(&user).await?;
        
        self.connection_pool.return_connection(connection).await;
        
        let new_user = User {
            id: new_id,
            name,
            email,
            created_at: chrono::Utc::now(),
        };
        
        // 更新缓存
        {
            let mut cache = self.cache.write().await;
            cache.insert(new_user.id, new_user.clone());
        }
        
        println!("✅ 用户创建成功，ID: {}", new_user.id);
        Ok(new_user)
    }
    
    /// 更新用户
    pub async fn update_user(&self, id: u64, name: String, email: String) -> Result<bool> {
        println!("✏️ 更新用户 ID: {}", id);
        
        let user = User {
            id,
            name: name.clone(),
            email: email.clone(),
            created_at: chrono::Utc::now(),
        };
        
        let mut connection = self.connection_pool.get_connection().await?;
        let success = connection.update(id, &user).await?;
        
        self.connection_pool.return_connection(connection).await;
        
        if success {
            // 更新缓存
            {
                let mut cache = self.cache.write().await;
                cache.insert(id, user);
            }
            println!("✅ 用户更新成功");
        } else {
            println!("❌ 用户更新失败");
        }
        
        Ok(success)
    }
    
    /// 删除用户
    pub async fn delete_user(&self, id: u64) -> Result<bool> {
        println!("🗑️ 删除用户 ID: {}", id);
        
        let mut connection = self.connection_pool.get_connection().await?;
        let success = connection.delete(id).await?;
        
        self.connection_pool.return_connection(connection).await;
        
        if success {
            // 从缓存中移除
            {
                let mut cache = self.cache.write().await;
                cache.remove(&id);
            }
            println!("✅ 用户删除成功");
        } else {
            println!("❌ 用户删除失败");
        }
        
        Ok(success)
    }
    
    /// 批量创建用户
    pub async fn batch_create_users(&self, users_data: Vec<(String, String)>) -> Result<Vec<User>> {
        println!("📦 批量创建 {} 个用户", users_data.len());
        
        let mut created_users = Vec::new();
        
        // 并发创建用户
        let mut tasks = Vec::new();
        for (name, email) in users_data {
            let service = self.clone();
            let task = tokio::spawn(async move {
                service.create_user(name, email).await
            });
            tasks.push(task);
        }
        
        // 等待所有任务完成
        for task in tasks {
            match task.await {
                Ok(Ok(user)) => created_users.push(user),
                Ok(Err(e)) => eprintln!("❌ 创建用户失败: {}", e),
                Err(e) => eprintln!("❌ 任务执行失败: {}", e),
            }
        }
        
        println!("✅ 批量创建完成，成功创建 {} 个用户", created_users.len());
        Ok(created_users)
    }
    
    /// 获取缓存统计
    pub async fn get_cache_stats(&self) -> (usize, Vec<u64>) {
        let cache = self.cache.read().await;
        let count = cache.len();
        let ids: Vec<u64> = cache.keys().cloned().collect();
        (count, ids)
    }
}

impl Clone for AsyncUserService {
    fn clone(&self) -> Self {
        Self {
            connection_pool: Arc::clone(&self.connection_pool),
            cache: Arc::clone(&self.cache),
        }
    }
}

/// 数据库事务示例
pub struct DatabaseTransaction {
    connection: DatabaseConnection,
    operations: Vec<TransactionOperation>,
}

#[derive(Debug, Clone)]
pub enum TransactionOperation {
    Insert(User),
    Update(u64, User),
    Delete(u64),
}

impl DatabaseTransaction {
    pub async fn new(connection_pool: &Arc<DatabaseConnectionPool>) -> Result<Self> {
        let connection = connection_pool.get_connection().await?;
        Ok(Self {
            connection,
            operations: Vec::new(),
        })
    }
    
    pub fn add_insert(&mut self, user: User) {
        self.operations.push(TransactionOperation::Insert(user));
    }
    
    pub fn add_update(&mut self, id: u64, user: User) {
        self.operations.push(TransactionOperation::Update(id, user));
    }
    
    pub fn add_delete(&mut self, id: u64) {
        self.operations.push(TransactionOperation::Delete(id));
    }
    
    pub async fn commit(mut self) -> Result<bool> {
        println!("🔄 开始事务提交，操作数: {}", self.operations.len());
        
        for operation in self.operations {
            match operation {
                TransactionOperation::Insert(user) => {
                    self.connection.insert(&user).await?;
                    println!("  ✅ 插入用户: {}", user.name);
                }
                TransactionOperation::Update(id, user) => {
                    self.connection.update(id, &user).await?;
                    println!("  ✅ 更新用户 ID: {}", id);
                }
                TransactionOperation::Delete(id) => {
                    self.connection.delete(id).await?;
                    println!("  ✅ 删除用户 ID: {}", id);
                }
            }
        }
        
        println!("✅ 事务提交成功");
        Ok(true)
    }
    
    pub async fn rollback(self) -> Result<()> {
        println!("🔄 事务回滚");
        // 在实际实现中，这里会撤销所有操作
        Ok(())
    }
}

/// 主函数
#[tokio::main]
async fn main() -> Result<()> {
    println!("🚀 启动异步数据库操作示例");
    
    // 创建数据库连接池
    let connection_pool = Arc::new(DatabaseConnectionPool::new(10));
    
    // 创建用户服务
    let user_service = AsyncUserService::new(connection_pool);
    
    // 示例操作
    println!("\n📋 执行数据库操作示例:");
    
    // 1. 获取所有用户
    let users = user_service.get_all_users().await?;
    println!("📊 当前用户数: {}", users.len());
    
    // 2. 创建新用户
    let new_user = user_service.create_user(
        "王五".to_string(),
        "wangwu@example.com".to_string()
    ).await?;
    println!("👤 新用户: {:?}", new_user);
    
    // 3. 根据ID获取用户
    let user = user_service.get_user_by_id(new_user.id).await?;
    if let Some(user) = user {
        println!("👤 获取用户: {:?}", user);
    }
    
    // 4. 更新用户
    user_service.update_user(
        new_user.id,
        "王五（已更新）".to_string(),
        "wangwu_updated@example.com".to_string()
    ).await?;
    
    // 5. 批量创建用户
    let batch_users = vec![
        ("赵六".to_string(), "zhaoliu@example.com".to_string()),
        ("孙七".to_string(), "sunqi@example.com".to_string()),
        ("周八".to_string(), "zhouba@example.com".to_string()),
    ];
    
    let created_users = user_service.batch_create_users(batch_users).await?;
    println!("📦 批量创建的用户: {:?}", created_users);
    
    // 6. 事务示例
    println!("\n🔄 事务操作示例:");
    let connection_pool = Arc::new(DatabaseConnectionPool::new(5));
    let mut transaction = DatabaseTransaction::new(&connection_pool).await?;
    
    transaction.add_insert(User {
        id: 0,
        name: "事务用户1".to_string(),
        email: "transaction1@example.com".to_string(),
        created_at: chrono::Utc::now(),
    });
    
    transaction.add_insert(User {
        id: 0,
        name: "事务用户2".to_string(),
        email: "transaction2@example.com".to_string(),
        created_at: chrono::Utc::now(),
    });
    
    transaction.commit().await?;
    
    // 7. 缓存统计
    let (cache_count, cached_ids) = user_service.get_cache_stats().await;
    println!("📦 缓存统计: {} 个用户，IDs: {:?}", cache_count, cached_ids);
    
    // 8. 删除用户
    if let Some(user) = created_users.first() {
        user_service.delete_user(user.id).await?;
    }
    
    println!("\n✅ 异步数据库操作示例完成!");
    
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_database_connection() {
        let connection = DatabaseConnection::new().await.unwrap();
        assert!(connection.is_active);
        assert!(connection.id > 0);
    }
    
    #[tokio::test]
    async fn test_user_service() {
        let connection_pool = Arc::new(DatabaseConnectionPool::new(5));
        let user_service = AsyncUserService::new(connection_pool);
        
        // 测试创建用户
        let user = user_service.create_user(
            "测试用户".to_string(),
            "test@example.com".to_string()
        ).await.unwrap();
        
        assert_eq!(user.name, "测试用户");
        assert_eq!(user.email, "test@example.com");
        assert!(user.id > 0);
        
        // 测试获取用户
        let retrieved_user = user_service.get_user_by_id(user.id).await.unwrap();
        assert!(retrieved_user.is_some());
        assert_eq!(retrieved_user.unwrap().name, "测试用户");
    }
    
    #[tokio::test]
    async fn test_transaction() {
        let connection_pool = Arc::new(DatabaseConnectionPool::new(5));
        let mut transaction = DatabaseTransaction::new(&connection_pool).await.unwrap();
        
        transaction.add_insert(User {
            id: 0,
            name: "测试用户".to_string(),
            email: "test@example.com".to_string(),
            created_at: chrono::Utc::now(),
        });
        
        let result = transaction.commit().await.unwrap();
        assert!(result);
    }
}
