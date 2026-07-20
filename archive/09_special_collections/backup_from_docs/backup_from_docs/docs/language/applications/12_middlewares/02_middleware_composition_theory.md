# 中间件组合理论

## 📊 目录

- [中间件组合理论](#中间件组合理论)
  - [📊 目录](#-目录)
  - [概述](#概述)
  - [理论基础](#理论基础)
    - [1. 中间件函数定义](#1-中间件函数定义)
    - [2. 类型安全的中间件](#2-类型安全的中间件)
    - [3. 组合律和恒等元](#3-组合律和恒等元)
  - [具体中间件实现](#具体中间件实现)
    - [1. 日志中间件](#1-日志中间件)
    - [2. 认证中间件](#2-认证中间件)
    - [3. 限流中间件](#3-限流中间件)
  - [高级组合模式](#高级组合模式)
    - [1. 条件中间件](#1-条件中间件)
    - [2. 错误处理中间件](#2-错误处理中间件)
    - [3. 并行中间件](#3-并行中间件)
  - [类型级组合验证](#类型级组合验证)
    - [1. 编译时组合检查](#1-编译时组合检查)
    - [2. 中间件堆栈构建器](#2-中间件堆栈构建器)
  - [实际应用示例](#实际应用示例)
    - [1. Web服务器中间件栈](#1-web服务器中间件栈)
    - [2. 数据处理管道](#2-数据处理管道)
  - [性能考虑](#性能考虑)
    - [1. 零成本抽象](#1-零成本抽象)
    - [2. 内存效率优化](#2-内存效率优化)
  - [相关模块](#相关模块)
  - [参考资料](#参考资料)

## 概述

中间件组合理论研究如何通过函数组合和类型系统构建可组合、可重用的中间件系统。本文档建立了Rust中间件的数学基础和组合规律。

## 理论基础

### 1. 中间件函数定义

**定义 1.1**: 中间件函数是一个高阶函数：

```text
Middleware<Req, Res, Next> = (Req, Next) → Future<Res>
其中 Next = Req → Future<Res>
```

**定义 1.2**: 中间件组合 `∘` 满足结合律：

```text
(m₁ ∘ m₂) ∘ m₃ = m₁ ∘ (m₂ ∘ m₃)
```

### 2. 类型安全的中间件

```rust
use std::future::Future;
use std::pin::Pin;

// 中间件特质定义
pub trait Middleware<Req, Res> {
    type Future: Future<Output = Res>;

    fn call(&self, req: Req, next: Box<dyn Fn(Req) -> Pin<Box<dyn Future<Output = Res>>>>) -> Self::Future;
}

// 中间件组合器
pub struct MiddlewareComposer<M1, M2> {
    first: M1,
    second: M2,
}

impl<M1, M2, Req, Res> Middleware<Req, Res> for MiddlewareComposer<M1, M2>
where
    M1: Middleware<Req, Res>,
    M2: Middleware<Req, Res>,
    Req: 'static,
    Res: 'static,
{
    type Future = Pin<Box<dyn Future<Output = Res>>>;

    fn call(&self, req: Req, next: Box<dyn Fn(Req) -> Pin<Box<dyn Future<Output = Res>>>>) -> Self::Future {
        let second = &self.second;
        Box::pin(self.first.call(req, Box::new(move |req| {
            second.call(req, next)
        })))
    }
}
```

### 3. 组合律和恒等元

**定理 1.1**: 恒等中间件作为组合的单位元

```rust
pub struct IdentityMiddleware;

impl<Req, Res> Middleware<Req, Res> for IdentityMiddleware
where
    Req: 'static,
    Res: 'static,
{
    type Future = Pin<Box<dyn Future<Output = Res>>>;

    fn call(&self, req: Req, next: Box<dyn Fn(Req) -> Pin<Box<dyn Future<Output = Res>>>>) -> Self::Future {
        next(req)
    }
}

// 恒等律：id ∘ m = m ∘ id = m
```

## 具体中间件实现

### 1. 日志中间件

```rust
use tracing::{info, instrument};

pub struct LoggingMiddleware {
    log_requests: bool,
    log_responses: bool,
}

impl LoggingMiddleware {
    pub fn new() -> Self {
        Self {
            log_requests: true,
            log_responses: true,
        }
    }
}

impl<Req, Res> Middleware<Req, Res> for LoggingMiddleware
where
    Req: std::fmt::Debug + 'static,
    Res: std::fmt::Debug + 'static,
{
    type Future = Pin<Box<dyn Future<Output = Res>>>;

    #[instrument]
    fn call(&self, req: Req, next: Box<dyn Fn(Req) -> Pin<Box<dyn Future<Output = Res>>>>) -> Self::Future {
        Box::pin(async move {
            if self.log_requests {
                info!("Request: {:?}", req);
            }

            let response = next(req).await;

            if self.log_responses {
                info!("Response: {:?}", response);
            }

            response
        })
    }
}
```

### 2. 认证中间件

```rust
use std::collections::HashMap;

#[derive(Debug)]
pub struct AuthRequest<T> {
    pub token: Option<String>,
    pub inner: T,
}

#[derive(Debug)]
pub enum AuthError {
    MissingToken,
    InvalidToken,
    Unauthorized,
}

pub struct AuthMiddleware {
    valid_tokens: HashMap<String, String>, // token -> user_id
}

impl AuthMiddleware {
    pub fn new(tokens: HashMap<String, String>) -> Self {
        Self { valid_tokens: tokens }
    }

    fn validate_token(&self, token: &str) -> Result<String, AuthError> {
        self.valid_tokens
            .get(token)
            .cloned()
            .ok_or(AuthError::InvalidToken)
    }
}

impl<T, Res> Middleware<AuthRequest<T>, Result<Res, AuthError>> for AuthMiddleware
where
    T: 'static,
    Res: 'static,
{
    type Future = Pin<Box<dyn Future<Output = Result<Res, AuthError>>>>;

    fn call(
        &self,
        req: AuthRequest<T>,
        next: Box<dyn Fn(AuthRequest<T>) -> Pin<Box<dyn Future<Output = Result<Res, AuthError>>>>>
    ) -> Self::Future {
        Box::pin(async move {
            match req.token {
                Some(token) => {
                    match self.validate_token(&token) {
                        Ok(_user_id) => next(req).await,
                        Err(auth_error) => Err(auth_error),
                    }
                }
                None => Err(AuthError::MissingToken),
            }
        })
    }
}
```

### 3. 限流中间件

```rust
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use std::collections::HashMap;

#[derive(Debug)]
pub struct RateLimitError {
    pub retry_after: Duration,
}

pub struct RateLimitMiddleware {
    requests: Arc<Mutex<HashMap<String, Vec<Instant>>>>,
    max_requests: usize,
    window: Duration,
}

impl RateLimitMiddleware {
    pub fn new(max_requests: usize, window: Duration) -> Self {
        Self {
            requests: Arc::new(Mutex::new(HashMap::new())),
            max_requests,
            window,
        }
    }

    fn check_rate_limit(&self, client_id: &str) -> Result<(), RateLimitError> {
        let mut requests = self.requests.lock().unwrap();
        let now = Instant::now();

        let client_requests = requests.entry(client_id.to_string()).or_insert_with(Vec::new);

        // 清理过期请求
        client_requests.retain(|&time| now.duration_since(time) < self.window);

        if client_requests.len() >= self.max_requests {
            return Err(RateLimitError {
                retry_after: self.window,
            });
        }

        client_requests.push(now);
        Ok(())
    }
}

#[derive(Debug)]
pub struct RateLimitRequest<T> {
    pub client_id: String,
    pub inner: T,
}

impl<T, Res> Middleware<RateLimitRequest<T>, Result<Res, RateLimitError>> for RateLimitMiddleware
where
    T: 'static,
    Res: 'static,
{
    type Future = Pin<Box<dyn Future<Output = Result<Res, RateLimitError>>>>;

    fn call(
        &self,
        req: RateLimitRequest<T>,
        next: Box<dyn Fn(RateLimitRequest<T>) -> Pin<Box<dyn Future<Output = Result<Res, RateLimitError>>>>>
    ) -> Self::Future {
        Box::pin(async move {
            match self.check_rate_limit(&req.client_id) {
                Ok(()) => next(req).await,
                Err(error) => Err(error),
            }
        })
    }
}
```

## 高级组合模式

### 1. 条件中间件

```rust
pub struct ConditionalMiddleware<M, P> {
    middleware: M,
    predicate: P,
}

impl<M, P> ConditionalMiddleware<M, P> {
    pub fn new(middleware: M, predicate: P) -> Self {
        Self { middleware, predicate }
    }
}

impl<M, P, Req, Res> Middleware<Req, Res> for ConditionalMiddleware<M, P>
where
    M: Middleware<Req, Res>,
    P: Fn(&Req) -> bool,
    Req: 'static,
    Res: 'static,
{
    type Future = Pin<Box<dyn Future<Output = Res>>>;

    fn call(&self, req: Req, next: Box<dyn Fn(Req) -> Pin<Box<dyn Future<Output = Res>>>>) -> Self::Future {
        if (self.predicate)(&req) {
            self.middleware.call(req, next)
        } else {
            next(req)
        }
    }
}
```

### 2. 错误处理中间件

```rust
use std::error::Error;

pub struct ErrorHandlingMiddleware<F> {
    handler: F,
}

impl<F> ErrorHandlingMiddleware<F> {
    pub fn new(handler: F) -> Self {
        Self { handler }
    }
}

impl<F, Req, Res, E> Middleware<Req, Result<Res, E>> for ErrorHandlingMiddleware<F>
where
    F: Fn(E) -> Res + 'static,
    E: Error + 'static,
    Req: 'static,
    Res: 'static,
{
    type Future = Pin<Box<dyn Future<Output = Result<Res, E>>>>;

    fn call(
        &self,
        req: Req,
        next: Box<dyn Fn(Req) -> Pin<Box<dyn Future<Output = Result<Res, E>>>>>
    ) -> Self::Future {
        let handler = &self.handler;
        Box::pin(async move {
            match next(req).await {
                Ok(res) => Ok(res),
                Err(err) => Ok(handler(err)),
            }
        })
    }
}
```

### 3. 并行中间件

```rust
use futures::future::join_all;

pub struct ParallelMiddleware<M> {
    middlewares: Vec<M>,
}

impl<M> ParallelMiddleware<M> {
    pub fn new(middlewares: Vec<M>) -> Self {
        Self { middlewares }
    }
}

impl<M, Req, Res> Middleware<Req, Vec<Res>> for ParallelMiddleware<M>
where
    M: Middleware<Req, Res>,
    Req: Clone + 'static,
    Res: 'static,
{
    type Future = Pin<Box<dyn Future<Output = Vec<Res>>>>;

    fn call(
        &self,
        req: Req,
        _next: Box<dyn Fn(Req) -> Pin<Box<dyn Future<Output = Vec<Res>>>>>
    ) -> Self::Future {
        let futures: Vec<_> = self.middlewares
            .iter()
            .map(|middleware| {
                let req_clone = req.clone();
                middleware.call(req_clone, Box::new(|_| Box::pin(async { unreachable!() })))
            })
            .collect();

        Box::pin(async move {
            join_all(futures).await
        })
    }
}
```

## 类型级组合验证

### 1. 编译时组合检查

```rust
// 使用类型系统验证中间件兼容性
pub struct CompatibleMiddleware<In, Out, M> {
    middleware: M,
    _phantom: std::marker::PhantomData<(In, Out)>,
}

impl<In, Out, M> CompatibleMiddleware<In, Out, M>
where
    M: Middleware<In, Out>,
{
    pub fn new(middleware: M) -> Self {
        Self {
            middleware,
            _phantom: std::marker::PhantomData,
        }
    }

    // 只允许兼容的中间件组合
    pub fn compose<M2, Out2>(
        self,
        other: CompatibleMiddleware<Out, Out2, M2>
    ) -> CompatibleMiddleware<In, Out2, MiddlewareComposer<M, M2>>
    where
        M2: Middleware<Out, Out2>,
    {
        CompatibleMiddleware::new(MiddlewareComposer {
            first: self.middleware,
            second: other.middleware,
        })
    }
}
```

### 2. 中间件堆栈构建器

```rust
pub struct MiddlewareStack<Req, Res> {
    middlewares: Vec<Box<dyn Middleware<Req, Res>>>,
}

impl<Req, Res> MiddlewareStack<Req, Res>
where
    Req: 'static,
    Res: 'static,
{
    pub fn new() -> Self {
        Self {
            middlewares: Vec::new(),
        }
    }

    pub fn add<M>(mut self, middleware: M) -> Self
    where
        M: Middleware<Req, Res> + 'static,
    {
        self.middlewares.push(Box::new(middleware));
        self
    }

    pub fn build(self) -> impl Middleware<Req, Res> {
        StackMiddleware {
            middlewares: self.middlewares,
        }
    }
}

struct StackMiddleware<Req, Res> {
    middlewares: Vec<Box<dyn Middleware<Req, Res>>>,
}

impl<Req, Res> Middleware<Req, Res> for StackMiddleware<Req, Res>
where
    Req: 'static,
    Res: 'static,
{
    type Future = Pin<Box<dyn Future<Output = Res>>>;

    fn call(&self, req: Req, final_handler: Box<dyn Fn(Req) -> Pin<Box<dyn Future<Output = Res>>>>) -> Self::Future {
        let mut next = final_handler;

        // 从后向前组合中间件
        for middleware in self.middlewares.iter().rev() {
            let current_next = next;
            next = Box::new(move |req| middleware.call(req, current_next));
        }

        next(req)
    }
}
```

## 实际应用示例

### 1. Web服务器中间件栈

```rust
use axum::{Router, response::Json};
use serde_json::Value;

pub fn create_web_app() -> Router {
    let middleware_stack = MiddlewareStack::new()
        .add(LoggingMiddleware::new())
        .add(AuthMiddleware::new(create_token_map()))
        .add(RateLimitMiddleware::new(100, Duration::from_secs(60)))
        .add(ErrorHandlingMiddleware::new(|err| {
            Json(serde_json::json!({
                "error": err.to_string()
            }))
        }))
        .build();

    Router::new()
        .route("/api/data", get(handle_data))
        .layer(middleware_stack)
}

async fn handle_data() -> Json<Value> {
    Json(serde_json::json!({
        "message": "Hello, World!"
    }))
}

fn create_token_map() -> HashMap<String, String> {
    let mut tokens = HashMap::new();
    tokens.insert("token123".to_string(), "user1".to_string());
    tokens.insert("token456".to_string(), "user2".to_string());
    tokens
}
```

### 2. 数据处理管道

```rust
pub struct DataProcessingPipeline<T> {
    _phantom: std::marker::PhantomData<T>,
}

impl<T> DataProcessingPipeline<T>
where
    T: 'static,
{
    pub fn new() -> Self {
        Self {
            _phantom: std::marker::PhantomData,
        }
    }

    pub fn with_validation<V>(self, validator: V) -> Self
    where
        V: Fn(&T) -> Result<(), ValidationError> + 'static,
    {
        // 添加验证中间件
        self
    }

    pub fn with_transformation<F, U>(self, transformer: F) -> DataProcessingPipeline<U>
    where
        F: Fn(T) -> U + 'static,
        U: 'static,
    {
        // 添加转换中间件
        DataProcessingPipeline {
            _phantom: std::marker::PhantomData,
        }
    }

    pub fn with_caching(self) -> Self {
        // 添加缓存中间件
        self
    }
}

#[derive(Debug)]
pub struct ValidationError(String);
```

## 性能考虑

### 1. 零成本抽象

```rust
// 编译时中间件组合，运行时零开销
macro_rules! compose_middleware {
    ($first:expr) => {
        $first
    };
    ($first:expr, $($rest:expr),+) => {
        MiddlewareComposer {
            first: $first,
            second: compose_middleware!($($rest),+),
        }
    };
}

// 使用示例
let composed = compose_middleware!(
    LoggingMiddleware::new(),
    AuthMiddleware::new(tokens),
    RateLimitMiddleware::new(100, Duration::from_secs(60))
);
```

### 2. 内存效率优化

```rust
// 使用引用计数避免不必要的克隆
pub struct SharedMiddleware<M> {
    inner: Arc<M>,
}

impl<M> Clone for SharedMiddleware<M> {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl<M, Req, Res> Middleware<Req, Res> for SharedMiddleware<M>
where
    M: Middleware<Req, Res>,
{
    type Future = M::Future;

    fn call(&self, req: Req, next: Box<dyn Fn(Req) -> Pin<Box<dyn Future<Output = Res>>>>) -> Self::Future {
        self.inner.call(req, next)
    }
}
```

## 相关模块

- [05_concurrency](../05_concurrency/00_index.md): 并发中间件模式
- [06_async_await](../06_async_await/00_index.md): 异步中间件
- [11_frameworks](../11_frameworks/00_index.md): Web框架集成
- [13_microservices](../13_microservices/00_index.md): 服务间中间件

## 参考资料

1. **理论基础**:
   - "Composable and Scalable Web APIs" - Leonard Richardson
   - "Functional Programming in Scala" - Paul Chiusano
   - "Category Theory for Programmers" - Bartosz Milewski

2. **实践指南**:
   - [Axum Middleware Guide](https://docs.rs/axum/latest/axum/middleware/)
   - [Tower Service Trait](https://docs.rs/tower-service/)
   - [Hyper Middleware](https://hyper.rs/)

---

**文档版本**: 1.0
**最后更新**: 2025-06-30
**维护者**: Rust中间件研究组
