# Async Closures (异步闭包)

> **特性**: `async_closure`
> **状态**: 🧪 不稳定 (Unstable)
> **预计稳定**: Rust 1.96+
> **跟踪 Issue**: [#62290](https://github.com/rust-lang/rust/issues/62290)

---

## 📋 目录

- [Async Closures (异步闭包)](#async-closures-异步闭包)
  - [📋 目录](#-目录)
  - [🎯 问题与动机](#-问题与动机)
    - [当前的问题](#当前的问题)
    - [动机](#动机)
  - [💡 解决方案](#-解决方案)
  - [📐 语法详解](#-语法详解)
    - [基础语法](#基础语法)
    - [捕获模式](#捕获模式)
    - [与 async move 对比](#与-async-move-对比)
  - [🚀 实际应用](#-实际应用)
    - [回调函数](#回调函数)
    - [事件处理器](#事件处理器)
    - [中间件链](#中间件链)
  - [🔍 实现细节](#-实现细节)
    - [AsyncFn Trait](#asyncfn-trait)
  - [⚠️ 注意事项](#️-注意事项)
    - [当前限制](#当前限制)
  - [🔗 参考资源](#-参考资源)

---

## 🎯 问题与动机

### 当前的问题

```rust
// ❌ 当前 Rust: 需要嵌套 async move
fn get_callback() -> impl Fn() -> impl Future<Output = i32> {
    || async move {
        tokio::time::sleep(Duration::from_secs(1)).await;
        42
    }
}

// 问题:
// 1. 语法冗长
// 2. 需要显式写出 Future 类型
// 3. 捕获语义不清晰
```

### 动机

1. **更清晰的语法**: `async || { }` 比 `|| async move { }` 更直观
2. **更好的类型推断**: 编译器可以更好地推断返回类型
3. **灵活的捕获**: 可以选择 `move` 或非 `move`

---

## 💡 解决方案

```rust
#![feature(async_closure)]

// ✅ 新的 async 闭包语法
fn get_callback() -> impl AsyncFn() -> i32 {
    async || {
        tokio::time::sleep(Duration::from_secs(1)).await;
        42
    }
}

// 带参数的 async 闭包
fn get_processor() -> impl AsyncFn(i32, i32) -> i32 {
    async |a, b| {
        tokio::time::sleep(Duration::from_millis(100)).await;
        a + b
    }
}
```

---

## 📐 语法详解

### 基础语法

```rust
#![feature(async_closure)]

use std::future::Future;

fn main() {
    // 无参数
    let f = async || {
        println!("Hello from async closure");
        42
    };

    // 带参数
    let add = async |a: i32, b: i32| -> i32 {
        tokio::time::sleep(Duration::from_millis(10)).await;
        a + b
    };

    // 使用
    let result = add(1, 2).await;
}
```

### 捕获模式

```rust
#![feature(async_closure)]

async fn capture_examples() {
    let data = vec![1, 2, 3];

    // 1. 引用捕获 (默认)
    let f = async || {
        // 通过引用捕获 data
        println!("{:?}", data);
    };

    // data 仍然可用
    println!("{:?}", data);
    f().await;

    // 2. 移动捕获
    let data2 = vec![4, 5, 6];
    let g = async move || {
        // 移动 data2
        println!("{:?}", data2);
    };

    // data2 不再可用
    g().await;

    // 3. 强制 move
    let data3 = String::from("hello");
    let h = async || {
        // 如果需要在闭包中修改，需要 move
        let _s = data3;
    };
}
```

### 与 async move 对比

| 特性 | `|| async move {}` | `async &#124;&#124; {}` |
|------|---------------------|-------------------------|
| **语法** | 冗长 | 简洁 |
| **捕获** | 总是 move | 可选择 |
| **返回类型** | 需要显式写出 | 自动推断 |
| **Fn trait** | `Fn() -> impl Future` | `AsyncFn` |

```rust
#![feature(async_closure)]

// 对比示例
fn traditional() -> impl FnOnce() -> Pin<Box<dyn Future<Output = i32> + Send>>> {
    || Box::pin(async move {
        tokio::time::sleep(Duration::from_secs(1)).await;
        42
    })
}

fn new_way() -> impl async FnOnce() -> i32 {
    async || {
        tokio::time::sleep(Duration::from_secs(1)).await;
        42
    }
}
```

---

## 🚀 实际应用

### 回调函数

```rust
#![feature(async_closure)]

use std::collections::HashMap;

struct AsyncEventEmitter {
    handlers: HashMap<String, Vec<Box<dyn AsyncFn() + Send + Sync>>>,
}

impl AsyncEventEmitter {
    fn new() -> Self {
        Self {
            handlers: HashMap::new(),
        }
    }

    fn on<F>(&mut self, event: &str, handler: F)
    where
        F: AsyncFn() + Send + Sync + 'static,
    {
        self.handlers
            .entry(event.to_string())
            .or_default()
            .push(Box::new(handler));
    }

    async fn emit(&self, event: &str) {
        if let Some(handlers) = self.handlers.get(event) {
            for handler in handlers {
                handler().await;
            }
        }
    }
}

// 使用
async fn example() {
    let mut emitter = AsyncEventEmitter::new();

    let counter = std::sync::Arc::new(std::sync::atomic::AtomicU32::new(0));
    let counter2 = counter.clone();

    emitter.on("click", async move || {
        counter2.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        println!("Clicked!");
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
    });

    emitter.emit("click").await;
}
```

### 事件处理器

```rust
#![feature(async_closure)]

use tokio::sync::mpsc;

struct AsyncHandler<T> {
    handler: Box<dyn AsyncFn(T) + Send + Sync>,
}

impl<T> AsyncHandler<T> {
    fn new<F>(handler: F) -> Self
    where
        F: AsyncFn(T) + Send + Sync + 'static,
    {
        Self {
            handler: Box::new(handler),
        }
    }

    async fn handle(&self, event: T) {
        (self.handler)(event).await;
    }
}

// 使用: WebSocket 消息处理器
async fn websocket_server() {
    let (tx, mut rx) = mpsc::channel::<String>(100);

    let handler = AsyncHandler::new(async |msg: String| {
        println!("Received: {}", msg);
        tokio::time::sleep(std::time::Duration::from_millis(10)).await;
        println!("Processed");
    });

    while let Some(msg) = rx.recv().await {
        handler.handle(msg).await;
    }
}
```

### 中间件链

```rust
#![feature(async_closure)]

use std::pin::Pin;
use std::future::Future;

type Next = Box<dyn AsyncFn(Request) -> Response + Send + Sync>;

struct Request {
    path: String,
    headers: Vec<(String, String)>,
}

struct Response {
    status: u16,
    body: String,
}

struct MiddlewareStack {
    middlewares: Vec<Box<dyn AsyncFn(Request, Next) -> Response + Send + Sync>>,
}

impl MiddlewareStack {
    fn new() -> Self {
        Self {
            middlewares: Vec::new(),
        }
    }

    fn add<F>(&mut self, middleware: F)
    where
        F: AsyncFn(Request, Next) -> Response + Send + Sync + 'static,
    {
        self.middlewares.push(Box::new(middleware));
    }

    async fn execute(&self, req: Request, final_handler: impl AsyncFn(Request) -> Response + Send + Sync + 'static) -> Response {
        let mut next: Next = Box::new(async move |req: Request| {
            final_handler(req).await
        });

        for middleware in self.middlewares.iter().rev() {
            let prev = next;
            next = Box::new(async move |req: Request| {
                middleware(req, prev).await
            });
        }

        next(req).await
    }
}

// 使用
async fn middleware_example() {
    let mut stack = MiddlewareStack::new();

    // 日志中间件
    stack.add(async |req: Request, next: Next| {
        println!("-> Request: {}", req.path);
        let resp = next(req).await;
        println!("<- Response: {}", resp.status);
        resp
    });

    // 认证中间件
    stack.add(async |req: Request, next: Next| {
        if req.headers.iter().any(|(k, _)| k == "Authorization") {
            next(req).await
        } else {
            Response {
                status: 401,
                body: "Unauthorized".to_string(),
            }
        }
    });

    // 最终处理器
    let handler = async |req: Request| {
        Response {
            status: 200,
            body: format!("Hello from {}", req.path),
        }
    };

    let req = Request {
        path: "/api/users".to_string(),
        headers: vec![("Authorization".to_string(), "Bearer xxx".to_string())],
    };

    let resp = stack.execute(req, handler).await;
}
```

---

## 🔍 实现细节

### AsyncFn Trait

```rust
// 简化表示
pub trait AsyncFn<Args> {
    type Output;
    type CallRefFuture<'a>: Future<Output = Self::Output>;

    fn async_call(&self, args: Args) -> Self::CallRefFuture<'_>;
}

pub trait AsyncFnMut<Args>: AsyncFn<Args> {
    fn async_call_mut(&mut self, args: Args) -> Self::CallRefFuture<'_>;
}

pub trait AsyncFnOnce<Args>: AsyncFnMut<Args> {
    type CallOnceFuture: Future<Output = Self::Output>;

    fn async_call_once(self, args: Args) -> Self::CallOnceFuture;
}
```

---

## ⚠️ 注意事项

### 当前限制

```rust
#![feature(async_closure)]

// ❌ 错误: 不能直接在 trait 中使用
// trait MyTrait {
//     async fn method(&self) -> i32;  // 不稳定
// }

// ✅ 正确: 使用现有的 async_trait 宏
#[async_trait::async_trait]
trait MyTrait {
    async fn method(&self) -> i32;
}

// ❌ 错误: 递归类型可能有问题
let f = async || {
    f().await;  // 递归调用
};
```

---

## 🔗 参考资源

- [Tracking Issue](https://github.com/rust-lang/rust/issues/62290)
- [RFC: Async Closures](https://rust-lang.github.io/rfcs/3668-async-closures.html)

---

**最后更新**: 2026-03-15
**状态**: 🧪 不稳定特性，需要 nightly
