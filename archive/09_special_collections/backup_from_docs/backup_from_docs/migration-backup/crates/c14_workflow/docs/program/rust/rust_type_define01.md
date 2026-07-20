# Rust 自定义类型设计准则：工作流操作视角

## 目录

- [Rust 自定义类型设计准则：工作流操作视角](#rust-自定义类型设计准则工作流操作视角)
  - [目录](#目录)
  - [1. 创建与初始化工作流](#1-创建与初始化工作流)
    - [1.1 友好的构造模式](#11-友好的构造模式)
    - [1.2 构建器模式（细粒度控制）](#12-构建器模式细粒度控制)
  - [2. 转换与适配工作流](#2-转换与适配工作流)
    - [2.1 实现标准转换特征](#21-实现标准转换特征)
    - [2.2 创建适配器方法](#22-创建适配器方法)
  - [3. 验证与错误处理工作流](#3-验证与错误处理工作流)
    - [3.1 链式验证模式](#31-链式验证模式)
    - [3.2 错误传播与处理](#32-错误传播与处理)
  - [4. 异步操作工作流](#4-异步操作工作流)
    - [4.1 异步友好的接口设计](#41-异步友好的接口设计)
    - [4.2 流处理模式](#42-流处理模式)
  - [5. 资源管理工作流](#5-资源管理工作流)
    - [5.1 RAII 模式资源管理](#51-raii-模式资源管理)
    - [5.2 构建协作资源模式](#52-构建协作资源模式)
  - [6. 测试和调试工作流](#6-测试和调试工作流)
    - [6.1 可测试性设计](#61-可测试性设计)
    - [6.2 调试友好的类型设计](#62-调试友好的类型设计)
  - [7. 并发操作工作流](#7-并发操作工作流)
    - [7.1 线程安全接口设计](#71-线程安全接口设计)
    - [7.2 状态共享模式](#72-状态共享模式)
  - [8. 扩展和演进工作流](#8-扩展和演进工作流)
    - [8.1 可扩展接口设计](#81-可扩展接口设计)
    - [8.2 版本兼容性策略](#82-版本兼容性策略)
  - [9. 总结：工作流操作准则](#9-总结工作流操作准则)

从工作流操作的角度看，Rust 类型设计需要考虑如何让类型自然地融入开发流程，
使得开发者能够高效地创建、使用和维护这些类型。
以下是基于工作流操作的核心准则：

## 1. 创建与初始化工作流

### 1.1 友好的构造模式

```rust
// 推荐：多种构造方法适应不同场景
pub struct Configuration {
    host: String,
    port: u16,
    timeout: Duration,
    max_connections: u32,
}

impl Configuration {
    // 全参数构造
    pub fn new(host: String, port: u16, timeout: Duration, max_connections: u32) -> Self {
        Self { host, port, timeout, max_connections }
    }
    
    // 从配置文件构造
    pub fn from_file(path: &Path) -> Result<Self, ConfigError> {
        // 读取和解析配置文件
        /* ... */
    }
    
    // 使用默认值的简化构造
    pub fn new_default_timeout(host: String, port: u16) -> Self {
        Self {
            host,
            port,
            timeout: Duration::from_secs(30),
            max_connections: 100,
        }
    }
}
```

**准则**：
    提供多种构造方法，适应不同的工作流和使用场景。

### 1.2 构建器模式（细粒度控制）

```rust
// 推荐：构建器模式实现细粒度控制
pub struct ServerBuilder {
    port: Option<u16>,
    host: Option<String>,
    workers: Option<usize>,
    timeout: Option<Duration>,
}

impl ServerBuilder {
    pub fn new() -> Self {
        Self {
            port: None,
            host: None,
            workers: None,
            timeout: None,
        }
    }
    
    pub fn port(mut self, port: u16) -> Self {
        self.port = Some(port);
        self
    }
    
    pub fn host(mut self, host: String) -> Self {
        self.host = Some(host);
        self
    }
    
    // 更多设置方法...
    
    pub fn build(self) -> Result<Server, BuildError> {
        let port = self.port.ok_or(BuildError::MissingPort)?;
        let host = self.host.unwrap_or_else(|| "127.0.0.1".to_string());
        let workers = self.workers.unwrap_or(4);
        let timeout = self.timeout.unwrap_or(Duration::from_secs(30));
        
        Ok(Server {
            port,
            host,
            workers,
            timeout,
        })
    }
}

// 使用示例
let server = ServerBuilder::new()
    .port(8080)
    .host("localhost".to_string())
    .build()?;
```

**准则**：
    为复杂类型提供构建器模式，实现清晰的链式调用和细粒度控制。

## 2. 转换与适配工作流

### 2.1 实现标准转换特征

```rust
// 推荐：实现 From/Into 特征简化转换
struct UserId(u64);

// 从 u64 到 UserId 的转换
impl From<u64> for UserId {
    fn from(id: u64) -> Self {
        UserId(id)
    }
}

// 从 UserId 到 u64 的转换
impl From<UserId> for u64 {
    fn from(user_id: UserId) -> Self {
        user_id.0
    }
}

// 使用场景
fn process_user(id: impl Into<UserId>) {
    let user_id: UserId = id.into();
    // 现在可以接受 UserId 或 u64
}
```

**准则**：
    实现 `From`/`Into` 等转换特征，简化工作流中的类型转换。

### 2.2 创建适配器方法

```rust
// 推荐：适配器方法简化工作流
struct DatabaseUser {
    id: i64,
    username: String,
    email: String,
}

struct ApiUser {
    user_id: String,
    name: String,
    contact: String,
}

// 适配器方法
impl DatabaseUser {
    pub fn to_api(&self) -> ApiUser {
        ApiUser {
            user_id: self.id.to_string(),
            name: self.username.clone(),
            contact: self.email.clone(),
        }
    }
}

impl ApiUser {
    pub fn to_database(&self) -> Result<DatabaseUser, ParseError> {
        Ok(DatabaseUser {
            id: self.user_id.parse()?,
            username: self.name.clone(),
            email: self.contact.clone(),
        })
    }
}
```

**准则**：
    提供适配器方法转换相关但不同的数据表示，减少手动转换代码。

## 3. 验证与错误处理工作流

### 3.1 链式验证模式

```rust
// 推荐：链式验证流程
struct UserInput {
    username: String,
    email: String,
    password: String,
}

impl UserInput {
    pub fn validate(&self) -> Result<ValidatedInput, ValidationError> {
        // 链式验证
        self.validate_username()?
            .validate_email()?
            .validate_password()
    }
    
    fn validate_username(&self) -> Result<&Self, ValidationError> {
        if self.username.len() < 3 {
            return Err(ValidationError::UsernameTooShort);
        }
        // 更多验证...
        Ok(self)
    }
    
    fn validate_email(&self) -> Result<&Self, ValidationError> {
        if !self.email.contains('@') {
            return Err(ValidationError::InvalidEmail);
        }
        // 更多验证...
        Ok(self)
    }
    
    fn validate_password(&self) -> Result<ValidatedInput, ValidationError> {
        if self.password.len() < 8 {
            return Err(ValidationError::PasswordTooShort);
        }
        // 更多验证...
        Ok(ValidatedInput {
            username: self.username.clone(),
            email: self.email.clone(),
            password_hash: hash_password(&self.password),
        })
    }
}
```

**准则**：设计链式验证流程，让验证步骤清晰可见，易于理解和维护。

### 3.2 错误传播与处理

```rust
// 推荐：明确的错误类型和传播
#[derive(Debug, thiserror::Error)]
pub enum ServiceError {
    #[error("Database error: {0}")]
    Database(#[from] DatabaseError),
    
    #[error("Validation error: {0}")]
    Validation(#[from] ValidationError),
    
    #[error("Not found: {0}")]
    NotFound(String),
}

// 在工作流中使用
fn create_user(input: UserInput) -> Result<User, ServiceError> {
    // 错误会自动转换并传播
    let validated = input.validate()?;
    let user = db.insert_user(&validated)?;
    Ok(user)
}
```

**准则**：设计清晰的错误类型层次，支持工作流中的错误传播和处理。

## 4. 异步操作工作流

### 4.1 异步友好的接口设计

```rust
// 推荐：异步友好的接口
pub struct AsyncDatabase {
    pool: Pool,
}

impl AsyncDatabase {
    // 创建连接
    pub async fn connect(config: &Config) -> Result<Self, ConnectionError> {
        let pool = Pool::connect(config).await?;
        Ok(Self { pool })
    }
    
    // 异步查询
    pub async fn find_user(&self, id: UserId) -> Result<User, DatabaseError> {
        let row = self.pool.query_one("SELECT * FROM users WHERE id = $1", &[&id]).await?;
        Ok(User::from_row(row))
    }
    
    // 支持批量操作
    pub async fn find_users(&self, ids: &[UserId]) -> Result<Vec<User>, DatabaseError> {
        let mut users = Vec::with_capacity(ids.len());
        for id in ids {
            users.push(self.find_user(*id).await?);
        }
        Ok(users)
    }
}
```

**准则**：为异步工作流设计友好的接口，支持非阻塞操作和自然的操作顺序。

### 4.2 流处理模式

```rust
// 推荐：支持流式操作
use futures::stream::{self, StreamExt};

pub struct LogProcessor {
    // 配置和状态
}

impl LogProcessor {
    // 返回实现 Stream 特征的类型
    pub fn process_logs(&self, path: &Path) -> impl Stream<Item = Result<LogEntry, LogError>> {
        // 打开文件并处理每一行
        match tokio::fs::File::open(path) {
            Ok(file) => {
                let reader = BufReader::new(file);
                let lines = reader.lines();
                lines
                    .map(|line_result| {
                        line_result
                            .map_err(LogError::Io)
                            .and_then(|line| LogEntry::parse(&line).map_err(LogError::Parse))
                    })
                    .boxed()
            }
            Err(err) => {
                // 优雅处理错误情况
                stream::once(async move { Err(LogError::Io(err)) }).boxed()
            }
        }
    }
}

// 使用示例
async fn process() -> Result<(), Error> {
    let processor = LogProcessor::new();
    let mut log_stream = processor.process_logs(Path::new("app.log"));
    
    while let Some(entry_result) = log_stream.next().await {
        match entry_result {
            Ok(entry) => println!("Processed: {}", entry),
            Err(err) => eprintln!("Error: {}", err),
        }
    }
    
    Ok(())
}
```

**准则**：设计支持流处理的接口，使得大型数据集可以被递增处理。

## 5. 资源管理工作流

### 5.1 RAII 模式资源管理

```rust
// 推荐：RAII 模式自动管理资源
pub struct DatabaseTransaction {
    inner: Option<InnerTransaction>,
    committed: bool,
}

impl DatabaseTransaction {
    pub fn new(connection: &Connection) -> Result<Self, DbError> {
        let inner = connection.begin_transaction()?;
        Ok(Self {
            inner: Some(inner),
            committed: false,
        })
    }
    
    pub fn commit(&mut self) -> Result<(), DbError> {
        if let Some(inner) = self.inner.take() {
            inner.commit()?;
            self.committed = true;
            Ok(())
        } else {
            Err(DbError::TransactionAlreadyEnded)
        }
    }
}

impl Drop for DatabaseTransaction {
    fn drop(&mut self) {
        if !self.committed {
            if let Some(inner) = self.inner.take() {
                // 安全地回滚事务
                let _ = inner.rollback();
            }
        }
    }
}

// 使用示例
fn perform_operation() -> Result<(), Error> {
    let conn = get_connection()?;
    let mut transaction = DatabaseTransaction::new(&conn)?;
    
    // 执行数据库操作...
    
    // 如果成功，提交事务
    transaction.commit()?;
    Ok(())
    // 如果没有调用 commit 或发生错误，事务会自动回滚
}
```

**准则**：使用 RAII（资源获取即初始化）模式自动管理资源生命周期。

### 5.2 构建协作资源模式

```rust
// 推荐：协作资源模式
pub struct ConnectionPool {
    // 内部实现
}

pub struct PooledConnection<'a> {
    conn: Connection,
    pool: &'a ConnectionPool,
}

impl ConnectionPool {
    // 获取连接
    pub fn get(&self) -> Result<PooledConnection<'_>, PoolError> {
        let conn = /* 从池中获取连接 */;
        Ok(PooledConnection {
            conn,
            pool: self,
        })
    }
    
    // 内部方法：归还连接
    fn return_connection(&self, conn: Connection) {
        // 将连接归还到池中
    }
}

impl<'a> Drop for PooledConnection<'a> {
    fn drop(&mut self) {
        // 在连接超出作用域时自动归还到池中
        let conn = std::mem::replace(&mut self.conn, Connection::dummy());
        self.pool.return_connection(conn);
    }
}

// 使用示例
fn use_connection() -> Result<(), Error> {
    let pool = get_pool();
    
    // 获取连接，使用完后自动归还
    let conn = pool.get()?;
    
    // 使用连接...
    
    Ok(())
}
```

**准则**：设计协作资源模式，确保资源在使用后能够自动释放或归还。

## 6. 测试和调试工作流

### 6.1 可测试性设计

```rust
// 推荐：设计便于测试的接口
// 将依赖抽象为特征
pub trait UserRepository {
    fn find_by_id(&self, id: UserId) -> Result<User, RepositoryError>;
    fn save(&self, user: &User) -> Result<(), RepositoryError>;
}

// 实现依赖于抽象
pub struct UserService<R: UserRepository> {
    repository: R,
}

impl<R: UserRepository> UserService<R> {
    pub fn new(repository: R) -> Self {
        Self { repository }
    }
    
    pub fn update_email(&self, id: UserId, email: String) -> Result<User, ServiceError> {
        let mut user = self.repository.find_by_id(id)?;
        user.email = email;
        self.repository.save(&user)?;
        Ok(user)
    }
}

// 测试代码
#[cfg(test)]
mod tests {
    use super::*;
    use mockall::predicate::*;
    use mockall::*;
    
    mock! {
        UserRepo {}
        impl UserRepository for UserRepo {
            fn find_by_id(&self, id: UserId) -> Result<User, RepositoryError>;
            fn save(&self, user: &User) -> Result<(), RepositoryError>;
        }
    }
    
    #[test]
    fn test_update_email() {
        let mut repo = MockUserRepo::new();
        let user_id = UserId(1);
        let mut user = User { id: user_id, email: "old@example.com".to_string() };
        
        repo.expect_find_by_id()
            .with(eq(user_id))
            .times(1)
            .returning(move |_| Ok(user.clone()));
        
        repo.expect_save()
            .times(1)
            .returning(|_| Ok(()));
        
        let service = UserService::new(repo);
        let result = service.update_email(user_id, "new@example.com".to_string());
        
        assert!(result.is_ok());
        assert_eq!(result.unwrap().email, "new@example.com");
    }
}
```

**准则**：设计依赖于抽象而非具体实现的接口，便于单元测试和模拟。

### 6.2 调试友好的类型设计

```rust
// 推荐：调试友好的类型设计
#[derive(Debug)]
pub struct ComplexState {
    config: Config,
    status: Status,
    connections: Vec<Connection>,
    #[debug(skip)]  // 跳过敏感数据
    credentials: Credentials,
}

// 实现自定义调试格式
impl std::fmt::Display for ComplexState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ComplexState {{ status: {}, connections: {} }}", 
               self.status, self.connections.len())
    }
}

// 实现详细的错误类型
#[derive(Debug, thiserror::Error)]
pub enum AppError {
    #[error("Failed to connect to database at {host}:{port}: {source}")]
    DatabaseConnection {
        host: String,
        port: u16,
        #[source]
        source: DatabaseError,
    },
    // 更多错误类型...
}
```

**准则**：设计对调试友好的类型，提供有意义的调试表示和错误信息。

## 7. 并发操作工作流

### 7.1 线程安全接口设计

```rust
// 推荐：设计线程安全的接口
use std::sync::{Arc, Mutex};

// 明确标记为线程安全
pub struct ThreadSafeCache {
    // 内部使用 Arc 和 Mutex 实现线程安全
    inner: Arc<Mutex<HashMap<String, Value>>>,
}

impl ThreadSafeCache {
    pub fn new() -> Self {
        Self {
            inner: Arc::new(Mutex::new(HashMap::new())),
        }
    }
    
    pub fn insert(&self, key: String, value: Value) -> Result<(), CacheError> {
        let mut guard = self.inner.lock().map_err(|_| CacheError::LockFailed)?;
        guard.insert(key, value);
        Ok(())
    }
    
    pub fn get(&self, key: &str) -> Result<Option<Value>, CacheError> {
        let guard = self.inner.lock().map_err(|_| CacheError::LockFailed)?;
        Ok(guard.get(key).cloned())
    }
    
    // 支持克隆，便于在线程间共享
    pub fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

// 使用示例
fn process_concurrent() {
    let cache = ThreadSafeCache::new();
    
    let cache_clone = cache.clone();
    std::thread::spawn(move || {
        cache_clone.insert("key1".to_string(), Value::new(42)).unwrap();
    });
    
    // 主线程也可以安全访问
    if let Ok(Some(value)) = cache.get("key1") {
        println!("Value: {}", value);
    }
}
```

**准则**：设计显式支持并发访问的接口，使多线程操作安全而直观。

### 7.2 状态共享模式

```rust
// 推荐：安全的状态共享模式
use std::sync::atomic::{AtomicUsize, Ordering};

pub struct RequestCounter {
    count: AtomicUsize,
}

impl RequestCounter {
    pub fn new() -> Self {
        Self {
            count: AtomicUsize::new(0),
        }
    }
    
    pub fn increment(&self) -> usize {
        self.count.fetch_add(1, Ordering::SeqCst)
    }
    
    pub fn current(&self) -> usize {
        self.count.load(Ordering::SeqCst)
    }
}

// 使用共享状态
fn handle_request(counter: &RequestCounter) {
    let request_num = counter.increment();
    println!("Handling request #{}", request_num);
    // 处理请求...
}
```

**准则**：使用原子类型、锁或消息传递设计安全的状态共享模式。

## 8. 扩展和演进工作流

### 8.1 可扩展接口设计

```rust
// 推荐：可扩展的接口设计
pub trait Handler {
    fn handle(&self, request: &Request) -> Response;
}

// 中间件支持
pub struct Pipeline {
    middlewares: Vec<Box<dyn Middleware>>,
    handler: Box<dyn Handler>,
}

impl Pipeline {
    pub fn new(handler: impl Handler + 'static) -> Self {
        Self {
            middlewares: Vec::new(),
            handler: Box::new(handler),
        }
    }
    
    pub fn add_middleware(&mut self, middleware: impl Middleware + 'static) -> &mut Self {
        self.middlewares.push(Box::new(middleware));
        self
    }
    
    pub fn handle(&self, mut request: Request) -> Response {
        // 按顺序应用中间件
        for middleware in &self.middlewares {
            request = middleware.pre_process(request);
        }
        
        // 调用处理器
        let mut response = self.handler.handle(&request);
        
        // 逆序应用中间件后处理
        for middleware in self.middlewares.iter().rev() {
            response = middleware.post_process(response);
        }
        
        response
    }
}

// 使用示例
fn create_app() -> Pipeline {
    let mut pipeline = Pipeline::new(MyHandler::new());
    pipeline
        .add_middleware(LoggingMiddleware::new())
        .add_middleware(AuthMiddleware::new());
    pipeline
}
```

**准则**：设计可扩展的接口，允许通过组合或插件模式添加新功能。

### 8.2 版本兼容性策略

```rust
// 推荐：版本兼容策略
// v1 API
pub mod v1 {
    pub struct Config {
        pub server: String,
        pub port: u16,
    }
    
    impl Config {
        pub fn new(server: String, port: u16) -> Self {
            Self { server, port }
        }
    }
}

// v2 API（扩展但兼容 v1）
pub mod v2 {
    #[derive(Default)]
    pub struct Config {
        pub server: String,
        pub port: u16,
        pub timeout: Option<std::time::Duration>,  // 新字段
    }
    
    impl Config {
        pub fn new(server: String, port: u16) -> Self {
            Self { 
                server, 
                port, 
                timeout: None,
            }
        }
        
        // 新方法
        pub fn with_timeout(mut self, timeout: std::time::Duration) -> Self {
            self.timeout = Some(timeout);
            self
        }
    }
    
    // 从 v1 版本兼容升级
    impl From<super::v1::Config> for Config {
        fn from(old: super::v1::Config) -> Self {
            Self {
                server: old.server,
                port: old.port,
                timeout: None,
            }
        }
    }
}
```

**准则**：设计支持向前兼容的类型演进策略，确保用户代码在升级时不会中断。

## 9. 总结：工作流操作准则

1. **直观初始化**：提供多种构造方法和构建器模式，适应不同的初始化工作流
2. **流畅转换**：实现标准转换特征和适配器方法，简化类型转换工作流
3. **清晰验证**：设计链式验证流程和明确的错误传播机制
4. **异步友好**：为异步工作流设计自然的接口，支持非阻塞操作
5. **自动资源管理**：使用 RAII 模式自动管理资源的生命周期
6. **可测试性**：依赖于抽象而非具体实现，便于单元测试
7. **并发支持**：明确设计支持并发访问的接口
8. **可扩展性**：通过组合或插件模式允许功能扩展
9. **版本兼容**：设计支持向前兼容的类型演进策略

这些工作流导向的设计准则能够显著提高 Rust 代码的可用性和开发效率。通过优化常见工作流的操作体验，你的类型将更容易使用、更不容易误用，并且能够更自然地融入开发流程，减少摩擦和认知负担。
