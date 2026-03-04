# Async Rust 最佳实践指南

> 从生产环境总结的最佳实践

---

## 1. 代码组织

### 1.1 项目结构

```text
my-async-project/
├── Cargo.toml
├── src/
│   ├── main.rs              # 程序入口
│   ├── lib.rs               # 库入口 (可选)
│   ├──
│   ├── bin/                 # 多二进制
│   │   └── worker.rs
│   │
│   ├── app/                 # 应用层
│   │   ├── mod.rs
│   │   ├── server.rs        # 服务器启动
│   │   └── config.rs        # 配置管理
│   │
│   ├── handlers/            # 请求处理器
│   │   ├── mod.rs
│   │   ├── user.rs
│   │   └── health.rs
│   │
│   ├── services/            # 业务逻辑
│   │   ├── mod.rs
│   │   ├── user_service.rs
│   │   └── auth_service.rs
│   │
│   ├── repositories/        # 数据访问
│   │   ├── mod.rs
│   │   ├── user_repo.rs
│   │   └── connection.rs
│   │
│   ├── models/              # 数据模型
│   │   ├── mod.rs
│   │   ├── user.rs
│   │   └── error.rs         # 应用错误类型
│   │
│   ├── middleware/          # 中间件
│   │   ├── mod.rs
│   │   ├── auth.rs
│   │   └── logging.rs
│   │
│   └── utils/               # 工具函数
│       ├── mod.rs
│       └── validation.rs
│
├── tests/                   # 集成测试
│   ├── integration_tests.rs
│   └── helpers/
│
├── benches/                 # 基准测试
│   └── bench.rs
│
└── config/                  # 配置文件
    ├── development.toml
    ├── production.toml
    └── default.toml
```

### 1.2 模块组织原则

```rust
// src/handlers/mod.rs
// 统一导出处理器

mod user;
mod health;

pub use user::*;
pub use health::*;

// 公共提取器
use axum::extract::FromRequestParts;

pub struct AuthClaims {
    pub user_id: u64,
    pub roles: Vec<String>,
}

impl<S> FromRequestParts<S> for AuthClaims {
    type Rejection = AuthError;

    async fn from_request_parts(
        parts: &mut Parts,
        state: &S,
    ) -> Result<Self, Self::Rejection> {
        // 提取逻辑...
    }
}
```

### 1.3 错误类型设计

```rust
// src/models/error.rs
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AppError {
    #[error("database error: {0}")]
    Database(#[from] sqlx::Error),

    #[error("validation error: {0}")]
    Validation(String),

    #[error("not found: {0}")]
    NotFound(String),

    #[error("unauthorized")]
    Unauthorized,

    #[error("forbidden")]
    Forbidden,

    #[error("rate limited")]
    RateLimited,

    #[error("external service error: {0}")]
    ExternalService(String),

    #[error("internal error: {0}")]
    Internal(String),
}

impl AppError {
    pub fn status_code(&self) -> StatusCode {
        match self {
            AppError::Validation(_) => StatusCode::BAD_REQUEST,
            AppError::NotFound(_) => StatusCode::NOT_FOUND,
            AppError::Unauthorized => StatusCode::UNAUTHORIZED,
            AppError::Forbidden => StatusCode::FORBIDDEN,
            AppError::RateLimited => StatusCode::TOO_MANY_REQUESTS,
            AppError::ExternalService(_) => StatusCode::BAD_GATEWAY,
            _ => StatusCode::INTERNAL_SERVER_ERROR,
        }
    }
}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let status = self.status_code();
        let body = Json(json!({
            "error": self.to_string(),
            "code": status.as_u16(),
        }));
        (status, body).into_response()
    }
}
```

---

## 2. 错误处理

### 2.1 使用?操作符

```rust
// 好: 简洁的错误传播
async fn get_user(id: u64) -> Result<User, AppError> {
    let user = sqlx::query_as::<_, User>("SELECT * FROM users WHERE id = ?")
        .bind(id)
        .fetch_one(&pool)
        .await?;  // 自动转换 sqlx::Error -> AppError

    Ok(user)
}

// 更好: 添加上下文
async fn get_user(id: u64) -> Result<User, AppError> {
    let user = sqlx::query_as::<_, User>("SELECT * FROM users WHERE id = ?")
        .bind(id)
        .fetch_one(&pool)
        .await
        .map_err(|e| {
            tracing::error!("database error: {:?}", e);
            AppError::Database(e)
        })?;

    Ok(user)
}
```

### 2.2 错误上下文

```rust
use anyhow::{Context, Result};

async fn process_file(path: &str) -> Result<Data> {
    let content = tokio::fs::read_to_string(path)
        .await
        .with_context(|| format!("failed to read file: {}", path))?;

    let data = parse(&content)
        .context("failed to parse content")?;

    Ok(data)
}
```

### 2.3 错误恢复

```rust
use std::future::Future;
use std::time::Duration;
use tokio::time::sleep;

async fn with_retry<F, Fut, T>(
    mut f: F,
    max_retries: u32,
    delay: Duration,
) -> Result<T, Error>
where
    F: FnMut() -> Fut,
    Fut: Future<Output = Result<T, Error>>,
{
    let mut last_error = None;

    for attempt in 0..max_retries {
        match f().await {
            Ok(result) => return Ok(result),
            Err(e) => {
                tracing::warn!("attempt {} failed: {}", attempt, e);
                last_error = Some(e);
                if attempt < max_retries - 1 {
                    sleep(delay).await;
                }
            }
        }
    }

    Err(last_error.unwrap())
}

// 使用
let result = with_retry(
    || fetch_data(),
    3,
    Duration::from_secs(1),
).await?;
```

---

## 3. 资源管理

### 3.1 RAII模式

```rust
// 连接池管理
pub struct DbConnection {
    conn: PooledConnection,
}

impl DbConnection {
    pub async fn new(pool: &Pool) -> Result<Self> {
        let conn = pool.acquire().await?;
        Ok(Self { conn })
    }
}

impl Drop for DbConnection {
    fn drop(&mut self) {
        // 自动归还连接
    }
}

// 事务管理
pub struct Transaction {
    conn: Connection,
    committed: bool,
}

impl Transaction {
    pub async fn commit(mut self) -> Result<()> {
        self.conn.execute("COMMIT").await?;
        self.committed = true;
        Ok(())
    }
}

impl Drop for Transaction {
    fn drop(&mut self) {
        if !self.committed {
            // 异步清理
            tokio::spawn(async move {
                let _ = self.conn.execute("ROLLBACK").await;
            });
        }
    }
}
```

### 3.2 优雅关闭

```rust
use tokio::sync::mpsc;
use tokio::signal;

pub struct Shutdown {
    shutdown: bool,
    notify: mpsc::Sender<()>,
}

impl Shutdown {
    pub fn new(notify: mpsc::Sender<()>) -> Self {
        Self {
            shutdown: false,
            notify,
        }
    }

    pub fn is_shutdown(&self) -> bool {
        self.shutdown
    }

    pub async fn recv(&mut self) {
        if self.shutdown {
            return;
        }

        let _ = self.notify.recv().await;
        self.shutdown = true;
    }
}

// 在main中使用
#[tokio::main]
async fn main() {
    let (shutdown_tx, shutdown_rx) = mpsc::channel(1);
    let shutdown = Shutdown::new(shutdown_tx);

    // 启动服务
    let server = tokio::spawn(run_server(shutdown));

    // 等待关闭信号
    tokio::select! {
        _ = signal::ctrl_c() => {},
        _ = signal::unix::signal(...) => {},
    }

    // 通知关闭
    drop(shutdown_rx);

    // 等待服务关闭
    server.await.unwrap();
}
```

---

## 4. 并发控制

### 4.1 并发限制

```rust
use tokio::sync::Semaphore;

// 全局并发限制
static CONCURRENCY_LIMIT: Semaphore = Semaphore::const_new(100);

async fn limited_operation() -> Result<()> {
    let _permit = CONCURRENCY_LIMIT.acquire().await?;

    // 执行受限制的操作
    perform_work().await;

    // permit在drop时自动释放
    Ok(())
}

// 每个操作的分级限制
async fn fetch_with_limit(urls: Vec<String>) -> Vec<Result<Response>> {
    let semaphore = Arc::new(Semaphore::new(10));

    let futures = urls.into_iter().map(|url| {
        let sem = Arc::clone(&semaphore);
        async move {
            let _permit = sem.acquire().await?;
            reqwest::get(&url).await
        }
    });

    futures::future::join_all(futures).await
}
```

### 4.2 批处理

```rust
use futures::stream::{self, StreamExt};

// 批量处理
async fn process_batch(items: Vec<Item>) -> Vec<Result<Output>> {
    stream::iter(items)
        .map(|item| async move {
            process(item).await
        })
        .buffer_unordered(10)  // 最多10个并发
        .collect()
        .await
}

// 带背压的批处理
async fn process_with_backpressure(items: Vec<Item>) {
    let (tx, mut rx) = tokio::sync::mpsc::channel(100);

    // 生产者
    tokio::spawn(async move {
        for item in items {
            if tx.send(item).await.is_err() {
                break;
            }
        }
    });

    // 消费者 (控制速率)
    while let Some(item) = rx.recv().await {
        process(item).await;
    }
}
```

---

## 5. 性能优化

### 5.1 避免不必要的分配

```rust
// 坏: 每次调用都分配
async fn bad(input: &[u8]) -> Vec<u8> {
    let mut result = Vec::new();  // 分配
    result.extend_from_slice(input);
    result
}

// 好: 使用Bytes零拷贝
use bytes::BytesMut;

async fn good(input: &[u8]) -> BytesMut {
    let mut buf = BytesMut::with_capacity(input.len());
    buf.extend_from_slice(input);
    buf
}

// 更好: 重用缓冲区
thread_local! {
    static BUF: RefCell<BytesMut> = RefCell::new(BytesMut::with_capacity(8192));
}
```

### 5.2 批量IO

```rust
// 坏: 多次小写
for chunk in chunks {
    stream.write(chunk).await?;
}

// 好: 批量写入
use tokio::io::AsyncWriteExt;

let mut buf = Vec::with_capacity(8192);
for chunk in chunks {
    if buf.len() + chunk.len() > 8192 {
        stream.write_all(&buf).await?;
        buf.clear();
    }
    buf.extend_from_slice(chunk);
}
if !buf.is_empty() {
    stream.write_all(&buf).await?;
}
```

### 5.3 减少任务切换

```rust
// 坏: 频繁yield
for i in 0..100_000 {
    tokio::task::yield_now().await;  // 太频繁
    process(i);
}

// 好: 批量处理再yield
const BATCH: usize = 100;
for batch in (0..100_000).step_by(BATCH) {
    for i in batch..batch + BATCH {
        process(i);
    }
    tokio::task::yield_now().await;  // 合理间隔
}
```

### 5.4 使用正确的缓冲区大小

```rust
// TCP socket调优
let socket = TcpSocket::new_v4()?;
socket.set_recv_buffer_size(64 * 1024)?;
socket.set_send_buffer_size(64 * 1024)?;
socket.set_nodelay(true)?;
```

---

## 6. 测试策略

### 6.1 单元测试

```rust
#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn test_user_service() {
        // 使用内存数据库
        let pool = setup_test_db().await;
        let service = UserService::new(pool);

        let user = service.create_user("test@example.com").await.unwrap();

        assert_eq!(user.email, "test@example.com");
    }

    #[tokio::test]
    async fn test_with_timeout() {
        let result = tokio::time::timeout(
            Duration::from_secs(1),
            slow_operation(),
        ).await;

        assert!(result.is_err());  // 应该超时
    }
}
```

### 6.2 集成测试

```rust
// tests/integration_tests.rs
use my_app::app::create_app;

#[tokio::test]
async fn test_health_endpoint() {
    let app = create_app(test_config()).await;

    let response = app
        .oneshot(Request::builder()
            .uri("/health")
            .body(Body::empty())
            .unwrap())
        .await
        .unwrap();

    assert_eq!(response.status(), StatusCode::OK);
}

#[tokio::test]
async fn test_concurrent_requests() {
    let app = create_app(test_config()).await;

    let requests = (0..100).map(|_| {
        let app = app.clone();
        async move {
            app.oneshot(create_request()).await
        }
    });

    let results = futures::future::join_all(requests).await;

    assert!(results.iter().all(|r| r.is_ok()));
}
```

### 6.3 模拟/桩

```rust
use mockall::automock;

#[automock]
#[async_trait]
trait UserRepository {
    async fn find_by_id(&self, id: u64) -> Result<Option<User>>;
    async fn save(&self, user: &User) -> Result<()>;
}

#[tokio::test]
async fn test_with_mock() {
    let mut mock = MockUserRepository::new();

    mock.expect_find_by_id()
        .with(eq(1))
        .times(1)
        .returning(|_| Box::pin(async { Ok(Some(fake_user())) }));

    let service = UserService::new(mock);
    let user = service.get_user(1).await.unwrap();

    assert_eq!(user.id, 1);
}
```

---

## 7. 可观测性

### 7.1 结构化日志

```rust
use tracing::{info, instrument};

#[instrument(skip(db), fields(user_id = %id))]
async fn get_user(db: &Database, id: Uuid) -> Result<User> {
    info!("fetching user from database");

    let start = Instant::now();
    let user = db.query(id).await?;
    let elapsed = start.elapsed();

    info!(elapsed_ms = elapsed.as_millis(), "user fetched");

    Ok(user)
}
```

### 7.2 指标收集

```rust
use metrics::{counter, histogram, gauge};

async fn handle_request(req: Request) -> Response {
    let start = Instant::now();

    counter!("requests_total", 1, "path" => req.path());

    let response = process(req).await;

    let elapsed = start.elapsed();
    histogram!("request_duration_seconds", elapsed.as_secs_f64());

    counter!("responses_total", 1, "status" => response.status().as_str());

    response
}
```

### 7.3 分布式追踪

```rust
use tracing::{info_span, Instrument};

async fn process_request(req: Request) -> Response {
    async move {
        let user = fetch_user().await;
        let data = fetch_data().await;

        Response::new(user, data)
    }
    .instrument(info_span!("process_request", request_id = %req.id()))
    .await
}
```

---

**维护者**: Rust Async Specialty Team
**更新日期**: 2026-03-05
