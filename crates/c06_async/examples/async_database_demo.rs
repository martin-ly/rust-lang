//! 异步数据库和缓存演示
//! 
//! 本示例展示了异步数据库和缓存操作：
//! - 数据库连接池管理
//! - 异步查询和事务
//! - 缓存操作和失效策略
//! - 批量操作优化
//! - 读写分离
//! - 分布式锁
//! 
//! 运行方式：
//! ```bash
//! cargo run --example async_database_demo
//! ```
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant, SystemTime};
use tokio::sync::{RwLock, Mutex, Semaphore, Notify};
use tokio::time::{sleep, timeout};
use anyhow::Result;
use serde::{Deserialize, Serialize};
use uuid::Uuid;

#[derive(Debug, Clone, Serialize, Deserialize)]
struct User {
    id: Uuid,
    name: String,
    email: String,
    created_at: SystemTime,
    updated_at: SystemTime,
}

#[derive(Debug, Clone)]
struct DatabaseConfig {
    max_connections: usize,
    connection_timeout: Duration,
    #[allow(dead_code)]
    query_timeout: Duration,
}

impl Default for DatabaseConfig {
    fn default() -> Self {
        Self {
            max_connections: 10,
            connection_timeout: Duration::from_secs(5),
            query_timeout: Duration::from_secs(10),
        }
    }
}

// 模拟数据库连接池
#[derive(Clone)]
struct ConnectionPool {
    config: DatabaseConfig,
    available_connections: Arc<Semaphore>,
    connection_stats: Arc<Mutex<ConnectionStats>>,
}

#[derive(Debug, Default, Clone)]
struct ConnectionStats {
    total_connections: usize,
    active_connections: usize,
    total_queries: usize,
    failed_queries: usize,
}

impl ConnectionPool {
    fn new(config: DatabaseConfig) -> Self {
        Self {
            available_connections: Arc::new(Semaphore::new(config.max_connections)),
            connection_stats: Arc::new(Mutex::new(ConnectionStats::default())),
            config,
        }
    }

    async fn get_connection(&self) -> Result<DatabaseConnection> {
        let _permit = timeout(
            self.config.connection_timeout,
            self.available_connections.acquire()
        ).await??;

        // 更新统计信息
        {
            let mut stats = self.connection_stats.lock().await;
            stats.active_connections += 1;
            stats.total_connections += 1;
        }

        Ok(DatabaseConnection {
            id: Uuid::new_v4(),
            pool: Arc::new(Semaphore::new(1)),
            stats: Arc::clone(&self.connection_stats),
        })
    }

    async fn get_stats(&self) -> ConnectionStats {
        self.connection_stats.lock().await.clone()
    }
}

// 模拟数据库连接
#[derive(Clone)]
struct DatabaseConnection {
    id: Uuid,
    pool: Arc<Semaphore>,
    stats: Arc<Mutex<ConnectionStats>>,
}

impl DatabaseConnection {
    async fn execute_query<T>(&self, _query: &str) -> Result<Vec<T>>
    where
        T: for<'de> Deserialize<'de> + Clone,
    {
        let _permit = self.pool.acquire().await.unwrap();
        
        // 模拟查询延迟
        sleep(Duration::from_millis(100)).await;
        
        // 更新统计信息
        {
            let mut stats = self.stats.lock().await;
            stats.total_queries += 1;
        }

        // 模拟查询结果
        Ok(Vec::new())
    }

    async fn execute_transaction<F, R>(&self, f: F) -> Result<R>
    where
        F: FnOnce() -> std::pin::Pin<Box<dyn std::future::Future<Output = Result<R>> + Send>>,
    {
        let _permit = self.pool.acquire().await.unwrap();
        
        println!("    🔄 开始事务");
        
        // 模拟事务处理
        let result = f().await?;
        
        // 模拟提交延迟
        sleep(Duration::from_millis(50)).await;
        
        println!("    ✅ 事务提交成功");
        Ok(result)
    }
}

impl Drop for DatabaseConnection {
    fn drop(&mut self) {
        // 在真实实现中，这里会释放连接回到池中
        println!("    🔓 释放数据库连接: {}", self.id);
    }
}

// 模拟缓存系统
struct CacheManager {
    cache: Arc<RwLock<HashMap<String, CacheEntry>>>,
    ttl: Duration,
    max_size: usize,
}

#[derive(Debug, Clone)]
struct CacheEntry {
    value: String,
    created_at: Instant,
    access_count: u64,
}

impl CacheManager {
    fn new(ttl: Duration, max_size: usize) -> Self {
        Self {
            cache: Arc::new(RwLock::new(HashMap::new())),
            ttl,
            max_size,
        }
    }

    async fn get(&self, key: &str) -> Option<String> {
        let mut cache = self.cache.write().await;
        
        if let Some(entry) = cache.get_mut(key) {
            // 检查是否过期
            if entry.created_at.elapsed() < self.ttl {
                entry.access_count += 1;
                return Some(entry.value.clone());
            } else {
                // 过期，删除
                cache.remove(key);
            }
        }
        
        None
    }

    async fn set(&self, key: String, value: String) -> Result<()> {
        let mut cache = self.cache.write().await;
        
        // 检查缓存大小限制
        if cache.len() >= self.max_size && !cache.contains_key(&key) {
            // 删除最少使用的条目
            if let Some((oldest_key, _)) = cache.iter()
                .min_by_key(|(_, entry)| entry.access_count)
                .map(|(k, _)| (k.clone(), ())) {
                cache.remove(&oldest_key);
            }
        }
        
        cache.insert(key, CacheEntry {
            value,
            created_at: Instant::now(),
            access_count: 1,
        });
        
        Ok(())
    }

    #[allow(dead_code)]
    async fn invalidate(&self, key: &str) {
        let mut cache = self.cache.write().await;
        cache.remove(key);
    }

    #[allow(dead_code)]
    async fn clear(&self) {
        let mut cache = self.cache.write().await;
        cache.clear();
    }

    async fn get_stats(&self) -> CacheStats {
        let cache = self.cache.read().await;
        let total_entries = cache.len();
        let expired_entries = cache.values()
            .filter(|entry| entry.created_at.elapsed() >= self.ttl)
            .count();
        
        CacheStats {
            total_entries,
            expired_entries,
            hit_rate: 0.0, // 简化实现，实际应该计算命中率
        }
    }
}

#[derive(Debug)]
struct CacheStats {
    total_entries: usize,
    expired_entries: usize,
    hit_rate: f64,
}

struct DatabaseDemo {
    connection_pool: ConnectionPool,
    cache: CacheManager,
}

impl DatabaseDemo {
    fn new() -> Self {
        Self {
            connection_pool: ConnectionPool::new(DatabaseConfig::default()),
            cache: CacheManager::new(Duration::from_secs(300), 1000), // 5分钟TTL，最大1000条
        }
    }

    async fn run(&self) -> Result<()> {
        println!("🗄️ 异步数据库和缓存演示");
        println!("================================");

        // 1. 连接池管理演示
        println!("\n🏊 1. 连接池管理演示");
        self.connection_pool_demo().await?;

        // 2. 异步查询演示
        println!("\n🔍 2. 异步查询演示");
        self.async_queries_demo().await?;

        // 3. 事务处理演示
        println!("\n🔄 3. 事务处理演示");
        self.transaction_demo().await?;

        // 4. 缓存操作演示
        println!("\n💾 4. 缓存操作演示");
        self.cache_operations_demo().await?;

        // 5. 批量操作演示
        println!("\n📦 5. 批量操作演示");
        self.batch_operations_demo().await?;

        // 6. 读写分离演示
        println!("\n📖📝 6. 读写分离演示");
        self.read_write_split_demo().await?;

        // 7. 分布式锁演示
        println!("\n🔒 7. 分布式锁演示");
        self.distributed_lock_demo().await?;

        Ok(())
    }

    async fn connection_pool_demo(&self) -> Result<()> {
        let mut handles = vec![];
        
        // 创建多个并发任务来测试连接池
        for i in 0..15 {
            let pool = self.connection_pool.clone();
            let handle = tokio::spawn(async move {
                println!("    🏊 任务 {} 请求连接", i);
                
                match pool.get_connection().await {
                    Ok(connection) => {
                        println!("    ✅ 任务 {} 获得连接: {}", i, connection.id);
                        
                        // 模拟数据库操作
                        sleep(Duration::from_millis(200)).await;
                        
                        println!("    🔓 任务 {} 释放连接", i);
                    }
                    Err(e) => {
                        println!("    ❌ 任务 {} 获取连接失败: {}", i, e);
                    }
                }
            });
            
            handles.push(handle);
        }
        
        // 等待所有任务完成
        for handle in handles {
            handle.await?;
        }
        
        // 显示连接池统计信息
        let stats = self.connection_pool.get_stats().await;
        println!("    连接池统计:");
        println!("      总连接数: {}", stats.total_connections);
        println!("      活跃连接数: {}", stats.active_connections);
        println!("      总查询数: {}", stats.total_queries);
        println!("      失败查询数: {}", stats.failed_queries);
        
        Ok(())
    }

    async fn async_queries_demo(&self) -> Result<()> {
        let connection = self.connection_pool.get_connection().await?;
        
        // 模拟多个并发查询
        let queries = vec![
            "SELECT * FROM users WHERE active = true",
            "SELECT COUNT(*) FROM orders WHERE created_at > NOW() - INTERVAL '1 day'",
            "SELECT product_id, SUM(quantity) FROM order_items GROUP BY product_id",
            "SELECT * FROM products WHERE price > 100 ORDER BY created_at DESC",
        ];
        
        let mut handles = vec![];
        
        for (i, query) in queries.iter().enumerate() {
            let conn = connection.clone();
            let query = query.to_string();
            
            let handle = tokio::spawn(async move {
                println!("    🔍 执行查询 {}: {}", i + 1, query);
                
                match conn.execute_query::<User>(&query).await {
                    Ok(_) => {
                        println!("    ✅ 查询 {} 完成", i + 1);
                    }
                    Err(e) => {
                        println!("    ❌ 查询 {} 失败: {}", i + 1, e);
                    }
                }
            });
            
            handles.push(handle);
        }
        
        // 等待所有查询完成
        for handle in handles {
            handle.await?;
        }
        
        Ok(())
    }

    async fn transaction_demo(&self) -> Result<()> {
        let connection = self.connection_pool.get_connection().await?;
        
        // 模拟事务操作
        let result = connection.execute_transaction(|| {
            Box::pin(async move {
                println!("      📝 更新用户信息");
                sleep(Duration::from_millis(100)).await;
                
                println!("      💰 更新账户余额");
                sleep(Duration::from_millis(100)).await;
                
                println!("      📧 发送通知邮件");
                sleep(Duration::from_millis(100)).await;
                
                Ok("事务执行成功".to_string())
            })
        }).await?;
        
        println!("      {}", result);
        Ok(())
    }

    async fn cache_operations_demo(&self) -> Result<()> {
        // 缓存写入
        println!("    💾 写入缓存数据");
        for i in 0..5 {
            let key = format!("user:{}", i);
            let value = format!("用户数据 {}", i);
            self.cache.set(key, value).await?;
        }
        
        // 缓存读取
        println!("    📖 读取缓存数据");
        for i in 0..7 {
            let key = format!("user:{}", i);
            match self.cache.get(&key).await {
                Some(value) => {
                    println!("      ✅ 缓存命中: {} = {}", key, value);
                }
                None => {
                    println!("      ❌ 缓存未命中: {}", key);
                }
            }
        }
        
        // 显示缓存统计
        let stats = self.cache.get_stats().await;
        println!("    📊 缓存统计:");
        println!("      总条目数: {}", stats.total_entries);
        println!("      过期条目数: {}", stats.expired_entries);
        println!("      命中率: {:.1}%", stats.hit_rate * 100.0);
        
        Ok(())
    }

    async fn batch_operations_demo(&self) -> Result<()> {
        println!("    📦 批量插入操作");
        
        let connection = self.connection_pool.get_connection().await?;
        let batch_size = 100;
        let total_records = 500;
        
        let start = std::time::Instant::now();
        
        for batch_start in (0..total_records).step_by(batch_size) {
            let batch_end = (batch_start + batch_size).min(total_records);
            
            println!("      📝 处理批次: {} - {}", batch_start, batch_end);
            
            // 模拟批量插入
            let mut futures = vec![];
            for _i in batch_start..batch_end {
                let _conn = &connection;
                let future = async move {
                    // 模拟单条插入
                    sleep(Duration::from_millis(10)).await;
                    Ok::<(), anyhow::Error>(())
                };
                futures.push(future);
            }
            
            // 并发执行批次内的插入
            futures::future::join_all(futures).await;
        }
        
        let duration = start.elapsed();
        println!("      ✅ 批量操作完成，耗时: {:?}", duration);
        println!("      📊 平均速度: {:.0} 记录/秒", total_records as f64 / duration.as_secs_f64());
        
        Ok(())
    }

    async fn read_write_split_demo(&self) -> Result<()> {
        // 模拟读写分离：读从从库，写从主库
        let read_connection = self.connection_pool.get_connection().await?;
        let write_connection = self.connection_pool.get_connection().await?;
        
        println!("    📖 从从库读取数据");
        // 模拟从从库读取
        read_connection.execute_query::<User>("SELECT * FROM users").await?;
        
        println!("    📝 向主库写入数据");
        // 模拟向主库写入
        write_connection.execute_query::<User>("INSERT INTO users (name, email) VALUES ('新用户', 'new@example.com')").await?;
        
        println!("    ✅ 读写分离操作完成");
        
        Ok(())
    }

    async fn distributed_lock_demo(&self) -> Result<()> {
        let lock_key = "distributed_lock:critical_section";
        let lock_timeout = Duration::from_secs(5);
        
        // 模拟分布式锁
        let lock_manager = Arc::new(Mutex::new(HashMap::<String, Instant>::new()));
        let notify = Arc::new(Notify::new());
        
        // 启动多个任务竞争锁
        let mut handles = vec![];
        
        for i in 0..3 {
            let lock_manager = Arc::clone(&lock_manager);
            let notify = Arc::clone(&notify);
            
            let handle = tokio::spawn(async move {
                println!("      🔒 任务 {} 尝试获取分布式锁", i);
                
                loop {
                    // 尝试获取锁
                    {
                        let mut locks = lock_manager.lock().await;
                        if !locks.contains_key(lock_key) || 
                           locks.get(lock_key).unwrap().elapsed() > lock_timeout {
                            locks.insert(lock_key.to_string(), Instant::now());
                            println!("      ✅ 任务 {} 获得分布式锁", i);
                            break;
                        }
                    }
                    
                    // 等待锁释放
                    notify.notified().await;
                }
                
                // 持有锁执行关键代码
                println!("      🔧 任务 {} 执行关键代码", i);
                sleep(Duration::from_millis(1000)).await;
                
                // 释放锁
                {
                    let mut locks = lock_manager.lock().await;
                    locks.remove(lock_key);
                    println!("      🔓 任务 {} 释放分布式锁", i);
                }
                
                // 通知其他等待的任务
                notify.notify_waiters();
            });
            
            handles.push(handle);
        }
        
        // 等待所有任务完成
        for handle in handles {
            handle.await?;
        }
        
        println!("    ✅ 分布式锁演示完成");
        
        Ok(())
    }
}

#[tokio::main]
async fn main() -> Result<()> {
    let demo = DatabaseDemo::new();
    demo.run().await?;

    println!("\n🎉 异步数据库和缓存演示完成！");
    Ok(())
}
