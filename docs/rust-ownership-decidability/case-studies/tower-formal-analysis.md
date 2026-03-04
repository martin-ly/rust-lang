# Tower 服务抽象形式化分析

> **主题**: 可组合的服务层
>
> **形式化框架**: Service Trait + Layer组合
>
> **参考**: Tower Documentation

---

## 目录

- [Tower 服务抽象形式化分析](#tower-服务抽象形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. Service Trait](#2-service-trait)
    - [2.1 核心抽象](#21-核心抽象)
    - [定义 2.1 (Service Trait)](#定义-21-service-trait)
    - [定理 2.1 (统一抽象)](#定理-21-统一抽象)
    - [2.2 poll\_ready语义](#22-poll_ready语义)
    - [定理 2.2 (就绪协议)](#定理-22-就绪协议)
  - [3. Layer组合](#3-layer组合)
    - [定义 3.1 (Layer Trait)](#定义-31-layer-trait)
    - [定理 3.1 (中间件组合)](#定理-31-中间件组合)
  - [4. 中间件生态](#4-中间件生态)
  - [5. 背压模型](#5-背压模型)
    - [定理 5.1 (全局背压)](#定理-51-全局背压)
  - [6. 反例](#6-反例)
    - [反例 6.1 (忘记poll\_ready)](#反例-61-忘记poll_ready)
    - [反例 6.2 (层级顺序)](#反例-62-层级顺序)

---

## 1. 引言

Tower提供:

- Service trait抽象
- Layer组合系统
- 丰富的中间件
- 跨框架兼容

---

## 2. Service Trait

### 2.1 核心抽象

### 定义 2.1 (Service Trait)

```rust
pub trait Service<Request> {
    type Response;
    type Error;
    type Future: Future<Output = Result<Self::Response, Self::Error>>;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>>;
    fn call(&mut self, req: Request) -> Self::Future;
}
```

### 定理 2.1 (统一抽象)

> 任何请求-响应模式可实现为Service。

∎

### 2.2 poll_ready语义

### 定理 2.2 (就绪协议)

> 必须poll_ready返回Ready后才能call。

```rust
// 正确用法
if service.poll_ready(cx).is_ready() {
    let future = service.call(request);
}

// 违反协议可能导致panic或错误
```

**形式化**:

$$
\text{call}(S, req) \text{ valid} \iff \text{poll_ready}(S) = \text{Ready}
$$

∎

---

## 3. Layer组合

### 定义 3.1 (Layer Trait)

```rust
pub trait Layer<S> {
    type Service;
    fn layer(&self, inner: S) -> Self::Service;
}
```

### 定理 3.1 (中间件组合)

> Layer可嵌套组合。

```rust
let service = ServiceBuilder::new()
    .timeout(Duration::from_secs(10))
    .retry(policy)
    .rate_limit(100, Duration::from_secs(1))
    .service(inner);
```

**类型**:

$$
\text{Timeout} \circ \text{Retry} \circ \text{RateLimit} \circ S
$$

∎

---

## 4. 中间件生态

| 中间件 | 功能 |
|--------|------|
| timeout | 请求超时 |
| retry | 失败重试 |
| limit | 并发限制 |
| buffer | 请求缓冲 |
| load_shed | 负载削减 |

---

## 5. 背压模型

### 定理 5.1 (全局背压)

> Tower通过poll_ready实现端到端背压。

```rust
// 每一层都能施加背压
impl Service<Req> for RateLimit<S> {
    fn poll_ready(&mut self, cx: &mut Context) -> Poll<Result<(), Error>> {
        // 限流检查
        if !self.rate_limiter.check() {
            return Poll::Pending;  // 施加背压
        }
        self.inner.poll_ready(cx)
    }
}
```

∎

---

## 6. 反例

### 反例 6.1 (忘记poll_ready)

```rust
// 错误: 直接call
let response = service.call(request).await;

// 正确: 先检查就绪
ready!(service.poll_ready(cx))?;
let response = service.call(request).await;
```

### 反例 6.2 (层级顺序)

```rust
// 错误顺序: 重试在超时外
let service = ServiceBuilder::new()
    .retry(policy)     // 先重试
    .timeout(dur)      // 后超时
    .service(inner);
// 效果: 每次重试有单独超时

// 正确: 超时在外层
let service = ServiceBuilder::new()
    .timeout(dur)      // 总超时
    .retry(policy)     // 内层重试
    .service(inner);
```

---

*文档版本: 1.0.0*
*定理数量: 7个*
