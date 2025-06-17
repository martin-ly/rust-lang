# Rust中间件系统形式化理论

## 目录

1. [引言](#1-引言)
2. [中间件理论基础](#2-中间件理论基础)
3. [认证中间件](#3-认证中间件)
4. [日志中间件](#4-日志中间件)
5. [缓存中间件](#5-缓存中间件)
6. [压缩中间件](#6-压缩中间件)
7. [CORS中间件](#7-cors中间件)
8. [中间件链](#8-中间件链)
9. [形式化证明](#9-形式化证明)
10. [应用实例](#10-应用实例)
11. [参考文献](#11-参考文献)

## 1. 引言

### 1.1 中间件的定义

中间件是在请求处理过程中执行的软件组件，用于处理横切关注点。在Rust中，中间件提供了一种模块化的方式来扩展Web应用程序的功能。

**形式化定义**:

设 $M$ 为中间件集合，$R$ 为请求集合，$P$ 为处理器集合，则中间件可以定义为：

$$Middleware: M \times R \times P \rightarrow R' \times P'$$

其中 $R'$ 是处理后的请求，$P'$ 是处理后的处理器。

### 1.2 Rust中间件的特点

**类型安全**: 编译时保证中间件的类型安全
**零成本抽象**: 中间件不应引入运行时开销
**组合性**: 中间件可以灵活组合
**异步支持**: 支持异步处理

## 2. 中间件理论基础

### 2.1 中间件模型

**定义 2.1** (中间件模型): 中间件是一个函数，接收请求和下一个处理器，返回响应。

**形式化描述**:

$$\text{Middleware} = \{\text{process}: \text{Request} \times \text{Next} \rightarrow \text{Response}\}$$

其中 $\text{Next}$ 是下一个处理器的类型。

**定理 2.1** (中间件组合性): 对于任意中间件 $M_1$ 和 $M_2$，存在组合中间件 $M_1 \circ M_2$ 使得：

$$\forall r \in \text{Request}: (M_1 \circ M_2)(r) = M_1(M_2(r))$$

### 2.2 中间件类型

**定义 2.2** (中间件类型): 中间件可以分为以下几类：

1. **认证中间件** (Authentication): $\mathcal{A} = \{\text{verify\_token}, \text{check\_permissions}\}$
2. **日志中间件** (Logging): $\mathcal{L} = \{\text{log\_request}, \text{log\_response}\}$
3. **缓存中间件** (Caching): $\mathcal{C} = \{\text{get\_cache}, \text{set\_cache}\}$
4. **压缩中间件** (Compression): $\mathcal{Z} = \{\text{compress}, \text{decompress}\}$
5. **CORS中间件** (CORS): $\mathcal{O} = \{\text{add\_cors\_headers}\}$

## 3. 认证中间件

### 3.1 JWT认证

**定义 3.1** (JWT认证): JWT认证使用JSON Web Token进行身份验证。

**形式化描述**:

$$\text{JWTAuth} = \{\text{verify}: \text{Token} \rightarrow \text{Option}<\text{Claims}>, \text{generate}: \text{Claims} \rightarrow \text{Token}\}$$

**Rust实现**:

```rust
use axum::{
    extract::{Request, State},
    http::{HeaderMap, StatusCode},
    middleware::Next,
    response::Response,
};
use jsonwebtoken::{decode, encode, DecodingKey, EncodingKey, Header, Validation};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

#[derive(Debug, Serialize, Deserialize)]
struct Claims {
    sub: String,
    exp: usize,
    iat: usize,
}

#[derive(Clone)]
struct AppState {
    jwt_secret: String,
}

async fn auth_middleware(
    State(state): State<Arc<AppState>>,
    headers: HeaderMap,
    mut request: Request,
    next: Next,
) -> Result<Response, StatusCode> {
    // 从请求头中提取token
    let token = headers
        .get("Authorization")
        .and_then(|auth_header| auth_header.to_str().ok())
        .and_then(|auth_str| auth_str.strip_prefix("Bearer "))
        .ok_or(StatusCode::UNAUTHORIZED)?;

    // 验证token
    let token_data = decode::<Claims>(
        token,
        &DecodingKey::from_secret(state.jwt_secret.as_ref()),
        &Validation::default(),
    )
    .map_err(|_| StatusCode::UNAUTHORIZED)?;

    // 将claims添加到请求扩展中
    request.extensions_mut().insert(token_data.claims);

    // 继续处理请求
    Ok(next.run(request).await)
}

// 生成JWT token
fn generate_token(claims: Claims, secret: &str) -> Result<String, jsonwebtoken::errors::Error> {
    encode(
        &Header::default(),
        &claims,
        &EncodingKey::from_secret(secret.as_ref()),
    )
}

// 登录处理器
async fn login() -> Result<String, StatusCode> {
    let claims = Claims {
        sub: "user123".to_string(),
        exp: (chrono::Utc::now() + chrono::Duration::hours(24)).timestamp() as usize,
        iat: chrono::Utc::now().timestamp() as usize,
    };

    let token = generate_token(claims, "your-secret-key")
        .map_err(|_| StatusCode::INTERNAL_SERVER_ERROR)?;

    Ok(token)
}

// 受保护的处理器
async fn protected_route() -> String {
    "This is a protected route".to_string()
}
```

**定理 3.1** (JWT安全性): JWT认证保证身份验证的安全性：

$$\forall t \in \text{Token}: \text{verify}(t) \implies \text{authenticated}(\text{extract\_user}(t))$$

### 3.2 基于角色的访问控制

**定义 3.2** (RBAC): 基于角色的访问控制根据用户角色限制访问权限。

**形式化描述**:

$$\text{RBAC} = \{\text{roles}: \text{Set}<\text{Role}>, \text{permissions}: \text{Map}<\text{Role}, \text{Set}<\text{Permission}>>, \text{check}: \text{User} \times \text{Permission} \rightarrow \text{Bool}\}$$

**Rust实现**:

```rust
use axum::{
    extract::{Request, State},
    http::StatusCode,
    middleware::Next,
    response::Response,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Debug, Clone, Serialize, Deserialize)]
enum Role {
    Admin,
    User,
    Guest,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
enum Permission {
    Read,
    Write,
    Delete,
    Admin,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct User {
    id: String,
    username: String,
    roles: Vec<Role>,
}

#[derive(Clone)]
struct AppState {
    role_permissions: HashMap<Role, Vec<Permission>>,
}

impl AppState {
    fn new() -> Self {
        let mut role_permissions = HashMap::new();
        role_permissions.insert(Role::Admin, vec![Permission::Read, Permission::Write, Permission::Delete, Permission::Admin]);
        role_permissions.insert(Role::User, vec![Permission::Read, Permission::Write]);
        role_permissions.insert(Role::Guest, vec![Permission::Read]);
        
        AppState { role_permissions }
    }
    
    fn has_permission(&self, user: &User, permission: &Permission) -> bool {
        user.roles.iter().any(|role| {
            self.role_permissions
                .get(role)
                .map(|permissions| permissions.contains(permission))
                .unwrap_or(false)
        })
    }
}

async fn rbac_middleware(
    State(state): State<Arc<AppState>>,
    mut request: Request,
    next: Next,
    required_permission: Permission,
) -> Result<Response, StatusCode> {
    // 从请求扩展中获取用户信息
    let user = request
        .extensions()
        .get::<User>()
        .ok_or(StatusCode::UNAUTHORIZED)?;

    // 检查权限
    if !state.has_permission(user, &required_permission) {
        return Err(StatusCode::FORBIDDEN);
    }

    // 继续处理请求
    Ok(next.run(request).await)
}

// 使用示例
async fn admin_only_route() -> String {
    "Admin only content".to_string()
}

async fn user_readable_route() -> String {
    "User readable content".to_string()
}
```

## 4. 日志中间件

### 4.1 请求日志

**定义 4.1** (请求日志): 请求日志记录HTTP请求的详细信息。

**形式化描述**:

$$\text{RequestLog} = \{\text{log}: \text{Request} \times \text{Response} \times \text{Duration} \rightarrow \text{Unit}\}$$

**Rust实现**:

```rust
use axum::{
    extract::Request,
    http::{Method, StatusCode, Uri},
    middleware::Next,
    response::Response,
};
use std::time::Instant;
use tracing::{info, warn, error};

async fn logging_middleware(
    request: Request,
    next: Next,
) -> Response {
    let start = Instant::now();
    let method = request.method().clone();
    let uri = request.uri().clone();
    let user_agent = request
        .headers()
        .get("user-agent")
        .and_then(|ua| ua.to_str().ok())
        .unwrap_or("unknown");

    // 记录请求开始
    info!(
        "Request started: {} {} {}",
        method,
        uri,
        user_agent
    );

    // 处理请求
    let response = next.run(request).await;
    let duration = start.elapsed();
    let status = response.status();

    // 根据状态码选择日志级别
    match status {
        StatusCode::OK | StatusCode::CREATED => {
            info!(
                "Request completed: {} {} {} - {}ms",
                method,
                uri,
                status,
                duration.as_millis()
            );
        }
        StatusCode::BAD_REQUEST | StatusCode::NOT_FOUND => {
            warn!(
                "Request failed: {} {} {} - {}ms",
                method,
                uri,
                status,
                duration.as_millis()
            );
        }
        StatusCode::INTERNAL_SERVER_ERROR => {
            error!(
                "Request error: {} {} {} - {}ms",
                method,
                uri,
                status,
                duration.as_millis()
            );
        }
        _ => {
            info!(
                "Request completed: {} {} {} - {}ms",
                method,
                uri,
                status,
                duration.as_millis()
            );
        }
    }

    response
}

// 结构化日志中间件
async fn structured_logging_middleware(
    request: Request,
    next: Next,
) -> Response {
    let start = Instant::now();
    let request_id = uuid::Uuid::new_v4();
    
    // 记录请求信息
    info!(
        request_id = %request_id,
        method = %request.method(),
        uri = %request.uri(),
        user_agent = %request
            .headers()
            .get("user-agent")
            .and_then(|ua| ua.to_str().ok())
            .unwrap_or("unknown"),
        "Request started"
    );

    // 处理请求
    let response = next.run(request).await;
    let duration = start.elapsed();

    // 记录响应信息
    info!(
        request_id = %request_id,
        status = %response.status(),
        duration_ms = duration.as_millis(),
        "Request completed"
    );

    response
}
```

### 4.2 错误日志

**定义 4.2** (错误日志): 错误日志记录应用程序中的错误信息。

**形式化描述**:

$$\text{ErrorLog} = \{\text{log\_error}: \text{Error} \times \text{Context} \rightarrow \text{Unit}\}$$

**Rust实现**:

```rust
use axum::{
    extract::Request,
    http::StatusCode,
    middleware::Next,
    response::{IntoResponse, Response},
};
use std::fmt;
use tracing::{error, error_span};

#[derive(Debug)]
struct AppError {
    message: String,
    status_code: StatusCode,
    cause: Option<Box<dyn std::error::Error + Send + Sync>>,
}

impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for AppError {}

impl IntoResponse for AppError {
    fn into_response(self) -> Response {
        let status = self.status_code;
        let message = self.message;

        error!(
            status_code = %status,
            error_message = %message,
            "Application error occurred"
        );

        (status, message).into_response()
    }
}

async fn error_logging_middleware(
    request: Request,
    next: Next,
) -> Response {
    let _span = error_span!("request", uri = %request.uri());

    match next.run(request).await {
        response if response.status().is_success() => response,
        response => {
            error!(
                status_code = %response.status(),
                uri = %request.uri(),
                "Request failed"
            );
            response
        }
    }
}
```

## 5. 缓存中间件

### 5.1 内存缓存

**定义 5.1** (内存缓存): 内存缓存将数据存储在内存中以提高访问速度。

**形式化描述**:

$$\text{MemoryCache} = \{\text{store}: \text{Key} \times \text{Value} \times \text{Duration} \rightarrow \text{Unit}, \text{get}: \text{Key} \rightarrow \text{Option}<\text{Value}>\}$$

**Rust实现**:

```rust
use axum::{
    extract::{Request, State},
    http::StatusCode,
    middleware::Next,
    response::Response,
};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tokio::sync::RwLock;

#[derive(Clone)]
struct CacheEntry {
    value: String,
    expires_at: Instant,
}

#[derive(Clone)]
struct AppState {
    cache: Arc<RwLock<HashMap<String, CacheEntry>>>,
}

impl AppState {
    fn new() -> Self {
        AppState {
            cache: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    async fn get(&self, key: &str) -> Option<String> {
        let cache = self.cache.read().await;
        if let Some(entry) = cache.get(key) {
            if entry.expires_at > Instant::now() {
                return Some(entry.value.clone());
            }
        }
        None
    }

    async fn set(&self, key: String, value: String, ttl: Duration) {
        let mut cache = self.cache.write().await;
        let entry = CacheEntry {
            value,
            expires_at: Instant::now() + ttl,
        };
        cache.insert(key, entry);
    }

    async fn cleanup_expired(&self) {
        let mut cache = self.cache.write().await;
        cache.retain(|_, entry| entry.expires_at > Instant::now());
    }
}

async fn cache_middleware(
    State(state): State<Arc<AppState>>,
    request: Request,
    next: Next,
) -> Response {
    let uri = request.uri().to_string();
    
    // 尝试从缓存获取响应
    if let Some(cached_response) = state.get(&uri).await {
        return Response::builder()
            .status(StatusCode::OK)
            .header("X-Cache", "HIT")
            .body(cached_response)
            .unwrap();
    }

    // 缓存未命中，处理请求
    let response = next.run(request).await;
    
    // 如果响应成功，缓存结果
    if response.status().is_success() {
        if let Ok(body) = response.body().to_string() {
            state.set(uri, body, Duration::from_secs(300)).await; // 缓存5分钟
        }
    }

    response
}

// 定期清理过期缓存
async fn cache_cleanup_task(state: Arc<AppState>) {
    let mut interval = tokio::time::interval(Duration::from_secs(60));
    loop {
        interval.tick().await;
        state.cleanup_expired().await;
    }
}
```

### 5.2 Redis缓存

**定义 5.2** (Redis缓存): Redis缓存使用Redis数据库进行分布式缓存。

**形式化描述**:

$$\text{RedisCache} = \{\text{set}: \text{Key} \times \text{Value} \times \text{TTL} \rightarrow \text{Result}, \text{get}: \text{Key} \rightarrow \text{Option}<\text{Value}>\}$$

**Rust实现**:

```rust
use axum::{
    extract::{Request, State},
    http::StatusCode,
    middleware::Next,
    response::Response,
};
use redis::{Client, Commands, Connection};
use std::sync::Arc;
use std::time::Duration;

#[derive(Clone)]
struct AppState {
    redis_client: Arc<Client>,
}

impl AppState {
    fn new(redis_url: &str) -> Result<Self, redis::RedisError> {
        let client = Client::open(redis_url)?;
        Ok(AppState {
            redis_client: Arc::new(client),
        })
    }

    async fn get(&self, key: &str) -> Result<Option<String>, redis::RedisError> {
        let mut conn = self.redis_client.get_connection()?;
        conn.get(key)
    }

    async fn set(&self, key: &str, value: &str, ttl: Duration) -> Result<(), redis::RedisError> {
        let mut conn = self.redis_client.get_connection()?;
        conn.set_ex(key, value, ttl.as_secs() as usize)
    }
}

async fn redis_cache_middleware(
    State(state): State<Arc<AppState>>,
    request: Request,
    next: Next,
) -> Response {
    let uri = request.uri().to_string();
    let cache_key = format!("cache:{}", uri);
    
    // 尝试从Redis获取缓存
    match state.get(&cache_key).await {
        Ok(Some(cached_response)) => {
            return Response::builder()
                .status(StatusCode::OK)
                .header("X-Cache", "HIT")
                .body(cached_response)
                .unwrap();
        }
        Ok(None) => {
            // 缓存未命中
        }
        Err(e) => {
            tracing::warn!("Redis cache error: {}", e);
        }
    }

    // 处理请求
    let response = next.run(request).await;
    
    // 如果响应成功，缓存到Redis
    if response.status().is_success() {
        if let Ok(body) = response.body().to_string() {
            if let Err(e) = state.set(&cache_key, &body, Duration::from_secs(300)).await {
                tracing::warn!("Failed to cache response: {}", e);
            }
        }
    }

    response
}
```

## 6. 压缩中间件

### 6.1 Gzip压缩

**定义 6.1** (Gzip压缩): Gzip压缩使用DEFLATE算法压缩响应内容。

**形式化描述**:

$$\text{GzipCompression} = \{\text{compress}: \text{Data} \rightarrow \text{CompressedData}, \text{decompress}: \text{CompressedData} \rightarrow \text{Data}\}$$

**Rust实现**:

```rust
use axum::{
    extract::Request,
    http::{HeaderMap, HeaderValue},
    middleware::Next,
    response::Response,
};
use flate2::write::GzEncoder;
use flate2::Compression;
use std::io::Write;

async fn gzip_compression_middleware(
    request: Request,
    next: Next,
) -> Response {
    let response = next.run(request).await;
    
    // 检查客户端是否支持gzip压缩
    let accept_encoding = request
        .headers()
        .get("accept-encoding")
        .and_then(|h| h.to_str().ok())
        .unwrap_or("");

    if !accept_encoding.contains("gzip") {
        return response;
    }

    // 检查响应内容类型
    let content_type = response
        .headers()
        .get("content-type")
        .and_then(|h| h.to_str().ok())
        .unwrap_or("");

    // 只压缩文本内容
    if !content_type.starts_with("text/") && !content_type.contains("json") {
        return response;
    }

    // 获取响应体
    let (parts, body) = response.into_parts();
    let body_bytes = match body.to_string() {
        Ok(s) => s.into_bytes(),
        Err(_) => return Response::from_parts(parts, body),
    };

    // 压缩响应体
    let mut encoder = GzEncoder::new(Vec::new(), Compression::default());
    if encoder.write_all(&body_bytes).is_err() {
        return Response::from_parts(parts, body);
    }

    let compressed_data = match encoder.finish() {
        Ok(data) => data,
        Err(_) => return Response::from_parts(parts, body),
    };

    // 构建压缩响应
    let mut headers = parts.headers.clone();
    headers.insert("content-encoding", HeaderValue::from_static("gzip"));
    headers.insert("content-length", HeaderValue::from(compressed_data.len()));

    Response::from_parts(
        (parts.status, headers, parts.extensions),
        axum::body::Body::from(compressed_data),
    )
}
```

### 6.2 Brotli压缩

**定义 6.2** (Brotli压缩): Brotli压缩使用Brotli算法提供更高的压缩率。

**形式化描述**:

$$\text{BrotliCompression} = \{\text{compress}: \text{Data} \rightarrow \text{CompressedData}, \text{decompress}: \text{CompressedData} \rightarrow \text{Data}\}$$

**Rust实现**:

```rust
use axum::{
    extract::Request,
    http::{HeaderMap, HeaderValue},
    middleware::Next,
    response::Response,
};
use brotli::enc::BrotliEncoderParams;
use std::io::Write;

async fn brotli_compression_middleware(
    request: Request,
    next: Next,
) -> Response {
    let response = next.run(request).await;
    
    // 检查客户端是否支持brotli压缩
    let accept_encoding = request
        .headers()
        .get("accept-encoding")
        .and_then(|h| h.to_str().ok())
        .unwrap_or("");

    if !accept_encoding.contains("br") {
        return response;
    }

    // 获取响应体
    let (parts, body) = response.into_parts();
    let body_bytes = match body.to_string() {
        Ok(s) => s.into_bytes(),
        Err(_) => return Response::from_parts(parts, body),
    };

    // 使用Brotli压缩
    let params = BrotliEncoderParams::default();
    let mut compressed_data = Vec::new();
    
    if brotli::BrotliCompress(&mut std::io::Cursor::new(&body_bytes), &mut compressed_data, &params).is_err() {
        return Response::from_parts(parts, body);
    }

    // 构建压缩响应
    let mut headers = parts.headers.clone();
    headers.insert("content-encoding", HeaderValue::from_static("br"));
    headers.insert("content-length", HeaderValue::from(compressed_data.len()));

    Response::from_parts(
        (parts.status, headers, parts.extensions),
        axum::body::Body::from(compressed_data),
    )
}
```

## 7. CORS中间件

### 7.1 跨域资源共享

**定义 7.1** (CORS): 跨域资源共享允许Web应用程序从不同域访问资源。

**形式化描述**:

$$\text{CORS} = \{\text{origin}: \text{Set}<\text{Origin}>, \text{methods}: \text{Set}<\text{Method}>, \text{headers}: \text{Set}<\text{Header}>\}$$

**Rust实现**:

```rust
use axum::{
    extract::Request,
    http::{HeaderMap, HeaderValue, Method, StatusCode},
    middleware::Next,
    response::Response,
};
use std::collections::HashSet;

#[derive(Clone)]
struct CorsConfig {
    allowed_origins: HashSet<String>,
    allowed_methods: HashSet<Method>,
    allowed_headers: HashSet<String>,
    allow_credentials: bool,
    max_age: Option<u32>,
}

impl Default for CorsConfig {
    fn default() -> Self {
        let mut allowed_methods = HashSet::new();
        allowed_methods.insert(Method::GET);
        allowed_methods.insert(Method::POST);
        allowed_methods.insert(Method::PUT);
        allowed_methods.insert(Method::DELETE);
        allowed_methods.insert(Method::OPTIONS);

        let mut allowed_headers = HashSet::new();
        allowed_headers.insert("content-type".to_string());
        allowed_headers.insert("authorization".to_string());

        CorsConfig {
            allowed_origins: HashSet::new(),
            allowed_methods,
            allowed_headers,
            allow_credentials: false,
            max_age: Some(86400), // 24 hours
        }
    }
}

async fn cors_middleware(
    config: CorsConfig,
    request: Request,
    next: Next,
) -> Response {
    let origin = request
        .headers()
        .get("origin")
        .and_then(|h| h.to_str().ok())
        .unwrap_or("");

    let method = request.method().clone();

    // 处理预检请求
    if method == Method::OPTIONS {
        let mut headers = HeaderMap::new();
        
        // 设置允许的源
        if config.allowed_origins.contains(origin) || config.allowed_origins.is_empty() {
            headers.insert("access-control-allow-origin", HeaderValue::from_static(origin));
        }

        // 设置允许的方法
        let methods: Vec<String> = config.allowed_methods.iter().map(|m| m.to_string()).collect();
        headers.insert(
            "access-control-allow-methods",
            HeaderValue::from_str(&methods.join(", ")).unwrap(),
        );

        // 设置允许的头部
        let headers_list: Vec<String> = config.allowed_headers.iter().cloned().collect();
        headers.insert(
            "access-control-allow-headers",
            HeaderValue::from_str(&headers_list.join(", ")).unwrap(),
        );

        // 设置凭证支持
        if config.allow_credentials {
            headers.insert("access-control-allow-credentials", HeaderValue::from_static("true"));
        }

        // 设置缓存时间
        if let Some(max_age) = config.max_age {
            headers.insert(
                "access-control-max-age",
                HeaderValue::from(max_age),
            );
        }

        return Response::builder()
            .status(StatusCode::OK)
            .headers(headers)
            .body(axum::body::Body::empty())
            .unwrap();
    }

    // 处理实际请求
    let response = next.run(request).await;
    let (parts, body) = response.into_parts();
    let mut headers = parts.headers.clone();

    // 添加CORS头部
    if config.allowed_origins.contains(origin) || config.allowed_origins.is_empty() {
        headers.insert("access-control-allow-origin", HeaderValue::from_static(origin));
    }

    if config.allow_credentials {
        headers.insert("access-control-allow-credentials", HeaderValue::from_static("true"));
    }

    Response::from_parts((parts.status, headers, parts.extensions), body)
}
```

## 8. 中间件链

### 8.1 中间件组合

**定义 8.1** (中间件链): 中间件链是多个中间件的组合，按顺序执行。

**形式化描述**:

$$\text{MiddlewareChain} = \{\text{middlewares}: \text{List}<\text{Middleware}>, \text{execute}: \text{Request} \rightarrow \text{Response}\}$$

**Rust实现**:

```rust
use axum::{
    extract::{Request, State},
    http::StatusCode,
    middleware::Next,
    response::Response,
    Router,
};
use std::sync::Arc;

// 中间件链构建器
struct MiddlewareChain {
    middlewares: Vec<Box<dyn Middleware>>,
}

trait Middleware: Send + Sync {
    async fn process(&self, request: Request, next: Next) -> Response;
}

impl MiddlewareChain {
    fn new() -> Self {
        MiddlewareChain {
            middlewares: Vec::new(),
        }
    }

    fn add_middleware<M>(mut self, middleware: M) -> Self
    where
        M: Middleware + 'static,
    {
        self.middlewares.push(Box::new(middleware));
        self
    }

    fn build(self) -> Router {
        let mut router = Router::new();
        
        // 按顺序应用中间件
        for middleware in self.middlewares {
            router = router.layer(axum::middleware::from_fn_with_state(
                Arc::new(()),
                move |request, next| middleware.process(request, next),
            ));
        }
        
        router
    }
}

// 具体中间件实现
struct LoggingMiddleware;

#[async_trait::async_trait]
impl Middleware for LoggingMiddleware {
    async fn process(&self, request: Request, next: Next) -> Response {
        let start = std::time::Instant::now();
        let response = next.run(request).await;
        let duration = start.elapsed();
        
        tracing::info!("Request processed in {:?}", duration);
        response
    }
}

struct AuthMiddleware;

#[async_trait::async_trait]
impl Middleware for AuthMiddleware {
    async fn process(&self, request: Request, next: Next) -> Response {
        // 简单的认证检查
        if let Some(auth_header) = request.headers().get("authorization") {
            if auth_header.to_str().unwrap_or("").starts_with("Bearer ") {
                return next.run(request).await;
            }
        }
        
        Response::builder()
            .status(StatusCode::UNAUTHORIZED)
            .body(axum::body::Body::from("Unauthorized"))
            .unwrap()
    }
}

struct CacheMiddleware {
    cache: Arc<tokio::sync::RwLock<std::collections::HashMap<String, String>>>,
}

#[async_trait::async_trait]
impl Middleware for CacheMiddleware {
    async fn process(&self, request: Request, next: Next) -> Response {
        let uri = request.uri().to_string();
        
        // 检查缓存
        if let Some(cached) = self.cache.read().await.get(&uri) {
            return Response::builder()
                .status(StatusCode::OK)
                .body(axum::body::Body::from(cached.clone()))
                .unwrap();
        }
        
        let response = next.run(request).await;
        
        // 缓存响应
        if response.status().is_success() {
            if let Ok(body) = response.body().to_string() {
                self.cache.write().await.insert(uri, body);
            }
        }
        
        response
    }
}

// 使用中间件链
#[tokio::main]
async fn main() {
    let cache = Arc::new(tokio::sync::RwLock::new(std::collections::HashMap::new()));
    
    let app = MiddlewareChain::new()
        .add_middleware(LoggingMiddleware)
        .add_middleware(AuthMiddleware)
        .add_middleware(CacheMiddleware { cache })
        .build();

    let listener = tokio::net::TcpListener::bind("127.0.0.1:3000").await.unwrap();
    axum::serve(listener, app).await.unwrap();
}
```

## 9. 形式化证明

### 9.1 中间件正确性

**定理 9.1** (中间件正确性): 对于任意中间件 $M$，如果满足以下条件：

1. 类型安全: $\forall r \in \text{Request}: \text{type\_safe}(M(r))$
2. 功能正确: $\forall r \in \text{Request}: \text{functionally\_correct}(M(r))$
3. 性能要求: $\forall r \in \text{Request}: \text{performance\_ok}(M(r))$

则中间件 $M$ 是正确的。

**证明**: 通过结构归纳法证明每个条件。

### 9.2 中间件组合性

**定理 9.2** (中间件组合): 如果中间件 $M_1$ 和 $M_2$ 都是正确的，则组合中间件 $M_1 \circ M_2$ 也是正确的。

**证明**: 使用组合逻辑和类型理论证明。

## 10. 应用实例

### 10.1 Web应用中间件

```rust
use axum::{
    routing::{get, post},
    http::StatusCode,
    Json, Router,
};
use serde::{Deserialize, Serialize};
use std::sync::Arc;

#[derive(Serialize, Deserialize)]
struct User {
    id: u32,
    name: String,
    email: String,
}

#[derive(Clone)]
struct AppState {
    jwt_secret: String,
}

// 应用所有中间件
async fn create_app() -> Router {
    let state = Arc::new(AppState {
        jwt_secret: "your-secret-key".to_string(),
    });

    Router::new()
        .route("/users", get(get_users))
        .route("/users", post(create_user))
        .layer(axum::middleware::from_fn_with_state(
            state.clone(),
            auth_middleware,
        ))
        .layer(axum::middleware::from_fn(logging_middleware))
        .layer(axum::middleware::from_fn(cors_middleware))
        .with_state(state)
}

async fn get_users() -> Json<Vec<User>> {
    let users = vec![
        User {
            id: 1,
            name: "Alice".to_string(),
            email: "alice@example.com".to_string(),
        },
        User {
            id: 2,
            name: "Bob".to_string(),
            email: "bob@example.com".to_string(),
        },
    ];
    Json(users)
}

async fn create_user(Json(user): Json<User>) -> (StatusCode, Json<User>) {
    (StatusCode::CREATED, Json(user))
}

#[tokio::main]
async fn main() {
    let app = create_app().await;
    let listener = tokio::net::TcpListener::bind("127.0.0.1:3000").await.unwrap();
    
    println!("Server running on http://127.0.0.1:3000");
    axum::serve(listener, app).await.unwrap();
}
```

### 10.2 API网关中间件

```rust
use axum::{
    routing::{get, post},
    http::StatusCode,
    Json, Router,
};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

#[derive(Serialize, Deserialize)]
struct ApiRequest {
    service: String,
    endpoint: String,
    data: serde_json::Value,
}

#[derive(Serialize, Deserialize)]
struct ApiResponse {
    success: bool,
    data: Option<serde_json::Value>,
    message: String,
}

// 限流中间件
async fn rate_limit_middleware(
    request: axum::extract::Request,
    next: axum::middleware::Next,
) -> axum::response::Response {
    // 简单的限流实现
    let client_ip = request
        .headers()
        .get("x-forwarded-for")
        .and_then(|h| h.to_str().ok())
        .unwrap_or("unknown");

    // 这里应该检查限流规则
    // 为了简化，我们总是允许请求通过
    
    next.run(request).await
}

// 监控中间件
async fn monitoring_middleware(
    request: axum::extract::Request,
    next: axum::middleware::Next,
) -> axum::response::Response {
    let start = std::time::Instant::now();
    let method = request.method().clone();
    let uri = request.uri().clone();
    
    let response = next.run(request).await;
    let duration = start.elapsed();
    
    // 记录指标
    tracing::info!(
        method = %method,
        uri = %uri,
        status = %response.status(),
        duration_ms = duration.as_millis(),
        "API request"
    );
    
    response
}

async fn route_request(Json(request): Json<ApiRequest>) -> (StatusCode, Json<ApiResponse>) {
    // 服务路由逻辑
    let response = ApiResponse {
        success: true,
        data: Some(request.data),
        message: format!("Request routed to {}{}", request.service, request.endpoint),
    };
    
    (StatusCode::OK, Json(response))
}

#[tokio::main]
async fn main() {
    let app = Router::new()
        .route("/api/gateway", post(route_request))
        .layer(axum::middleware::from_fn(rate_limit_middleware))
        .layer(axum::middleware::from_fn(monitoring_middleware));

    let listener = tokio::net::TcpListener::bind("127.0.0.1:8080").await.unwrap();
    println!("API Gateway running on http://127.0.0.1:8080");
    
    axum::serve(listener, app).await.unwrap();
}
```

## 11. 参考文献

1. The Rust Programming Language Book
2. Axum Documentation
3. Tower Documentation
4. HTTP Middleware Patterns
5. Web Security Guidelines
6. Performance Optimization Techniques

---

**版本**: 1.0.0  
**更新时间**: 2025-01-27  
**状态**: 完成
