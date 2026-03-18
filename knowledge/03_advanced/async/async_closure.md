# Async Closures 异步闭包

> **Rust 1.85+ 稳定特性：异步闭包开启函数式异步编程新纪元**
>
> **预计时间**: 6 小时

## 🎯 学习目标

- [ ] 理解 `async || {}` 语法及其工作原理
- [ ] 掌握异步闭包与普通闭包、async fn 的区别
- [ ] 熟练使用 `AsyncFn`/`AsyncFnMut`/`AsyncFnOnce` trait
- [ ] 在迭代器、流、回调中应用异步闭包
- [ ] 理解 `async move` 闭包的捕获语义
- [ ] 掌握异步闭包在并发模式中的最佳实践

## 📋 先决条件

- 熟练使用 async/await 语法
- 理解闭包和三种 Fn trait (FnOnce/FnMut/Fn)
- 了解 Future trait 和 Pin
- 具备 tokio 或 async-std 使用经验
- Rust 1.85 或更高版本

## 🧠 核心概念

### 1. 什么是异步闭包 (Rust 1.85 稳定)

异步闭包是 Rust 1.85 引入的稳定特性，它允许你创建返回 Future 的闭包，使用 `async || {}` 语法：

```rust
// 传统方式：需要 async fn 或手动返回 impl Future
async fn fetch_url(url: &str) -> Result<String, Error> {
    reqwest::get(url).await?.text().await
}

// 异步闭包：内联的、可捕获环境的异步代码块
let fetch = async |url: &str| -> Result<String, Error> {
    reqwest::get(url).await?.text().await
};

// 调用方式
let html = fetch("https://rust-lang.org").await?;
```

异步闭包的本质是：**一个可以捕获环境并返回 Future 的匿名函数**。

### 2. async || {} 语法详解

```rust
// 基本语法
let greet = async |name: &str| {
    tokio::time::sleep(Duration::from_millis(100)).await;
    format!("Hello, {name}!")
};

// 带返回类型注解
let compute = async |x: i32, y: i32| -> i32 {
    tokio::task::yield_now().await;
    x + y
};

// 异步闭包实现了 AsyncFn/AsyncFnMut/AsyncFnOnce trait
fn use_async_closure<F>(f: F)
where
    F: AsyncFn(&str) -> String,
{
    let future = f.call(("World",)); // 返回 impl Future
}
```

### 3. 与常规闭包的区别

| 特性 | 常规闭包 `\|x\| {}` | 异步闭包 `async \|x\| {}` |
|------|---------------------|---------------------------|
| 返回值 | 立即返回 T | 返回 impl Future<Output = T> |
| 调用方式 | `closure(args)` | `closure(args).await` |
| 执行时机 | 立即执行 | 惰性求值，await 时执行 |
| Trait | Fn/FnMut/FnOnce | AsyncFn/AsyncFnMut/AsyncFnOnce |
| 内部 await | ❌ 不允许 | ✅ 允许 |

```rust
// 关键区别示例
let regular = |x: i32| x + 1;           // 立即计算
let async_version = async |x: i32| {    // 返回 Future
    tokio::task::yield_now().await;
    x + 1
};

let result1 = regular(5);                // 直接得到 6
let result2 = async_version(5).await;    // 需要 .await
```

### 4. FnOnce/FnMut/Fn + async 的组合

Rust 1.85 引入了专门的异步闭包 trait：

```rust
// AsyncFnOnce: 只能调用一次
let consume = async move |data: Vec<u8>| -> String {
    process(data).await  // data 被 move 进闭包
};

// AsyncFnMut: 可以多次调用，可能修改捕获的状态
let mut counter = 0;
let mut increment = async || -> i32 {
    counter += 1;
    save_counter(counter).await;
    counter
};
let first = increment().await;   // 1
let second = increment().await;  // 2

// AsyncFn: 可以多次调用，不修改状态（纯异步闭包）
let fetcher = async |url: &str| -> Result<String, Error> {
    reqwest::get(url).await?.text().await
};
// 可以并发调用
let (r1, r2) = tokio::join!(
    fetcher("https://api1.example.com"),
    fetcher("https://api2.example.com"),
);
```

### 5. 使用场景和模式

#### 模式 1: 异步回调处理

```rust
// 事件处理器注册
struct EventHub {
    handlers: Vec<Box<dyn AsyncFn(Event) -> () + Send + Sync>>,
}

impl EventHub {
    fn on_event<F>(&mut self, handler: F)
    where
        F: AsyncFn(Event) -> () + Send + Sync + 'static,
    {
        self.handlers.push(Box::new(handler));
    }

    async fn emit(&self, event: Event) {
        for handler in &self.handlers {
            handler.call((event.clone(),)).await;
        }
    }
}

// 使用
let mut hub = EventHub::new();
hub.on_event(async |evt| {
    println!("Received: {:?}", evt);
    log_event(evt).await;
});
```

#### 模式 2: 异步迭代器适配器

```rust
use futures::stream::{self, StreamExt};

async fn process_users(user_ids: Vec<u64>) -> Vec<User> {
    let fetch_user = async |id: u64| -> Result<User, Error> {
        db.query("SELECT * FROM users WHERE id = ?", id)
            .await?.fetch_one().await
    };

    stream::iter(user_ids)
        .map(|id| fetch_user(id))
        .buffer_unordered(10)  // 最多 10 个并发
        .filter_map(|r| async { r.ok() })
        .collect().await
}
```

#### 模式 3: 延迟执行的异步工厂

```rust
struct TaskFactory<F> {
    creator: F,
}

impl<F, Fut> TaskFactory<F>
where
    F: AsyncFn() -> Fut + Send + Sync + Clone + 'static,
    Fut: Future<Output = TaskResult> + Send + 'static,
{
    fn spawn(&self) -> tokio::task::JoinHandle<TaskResult> {
        let creator = self.creator.clone();
        tokio::spawn(async move { creator.call(()).await })
    }
}

// 使用
let factory = TaskFactory {
    creator: async || {
        init_resources().await;
        execute_task().await
    },
};
let handle = factory.spawn();
```

### 6. async move 闭包

```rust
let data = Arc::new(Mutex::new(vec![1, 2, 3]));

// 引用捕获 - 需要生命周期管理
let processor = async |item: &Item| -> Result<()> {
    let guard = data.lock().await;
    process_with(&guard, item).await
};

// move 捕获 - 所有权转移
let owned_data = data.clone();
let consumer = async move |items: Vec<Item>| -> Vec<Result<()>> {
    futures::future::join_all(
        items.into_iter().map(|item| async {
            let guard = owned_data.lock().await;
            process_with(&guard, &item).await
        })
    ).await
};
```

### 7. 在迭代器和流中使用

```rust
use futures::stream::{self, StreamExt, TryStreamExt};

async fn concurrent_workflow() {
    let urls = vec!["https://api1.example.com", "https://api2.example.com"];

    // 使用异步闭包进行并发映射
    let responses: Vec<_> = stream::iter(urls)
        .map(async |url| {
            let client = reqwest::Client::new();
            client.get(url).send().await?.json::<ApiResponse>().await
        })
        .buffered(3)
        .try_collect().await?;

    // 带状态的有状态异步闭包
    let mut retry_count = 0;
    let with_retry = async |url: &str| -> Result<Response, Error> {
        loop {
            match fetch(url).await {
                Ok(resp) => return Ok(resp),
                Err(e) if retry_count < 3 => {
                    retry_count += 1;
                    tokio::time::sleep(Duration::from_secs(1)).await;
                }
                Err(e) => return Err(e),
            }
        }
    };
}
```

## 💡 最佳实践

### 1. 选择合适的捕获方式

```rust
// ✅ 优先使用引用捕获，避免不必要的克隆
let processor = async |item: &Item| { /* ... */ };

// ✅ 需要所有权时使用 async move
let consumer = async move |items: Vec<Item>| { /* ... */ };

// ✅ 复杂场景使用显式 Clone
let shared = Arc::new(config);
let f1 = {
    let shared = shared.clone();
    async move || { /* 使用 shared */ }
};
```

### 2. 限制并发度

```rust
// ✅ 总是考虑并发控制
stream::iter(items)
    .map(async |item| process(item).await)
    .buffer_unordered(10)  // 明确限制并发
    .collect::<Vec<_>>().await;
```

### 3. 错误处理

```rust
// ✅ 在异步闭包内部处理错误，或传播到外部
let safe_process = async |item: &Item| -> Result<Output, Error> {
    match risky_operation(item).await {
        Ok(result) => Ok(result),
        Err(e) => {
            tracing::error!("处理失败: {}", e);
            Err(e)
        }
    }
};
```

## ⚠️ 常见陷阱

### 1. 忘记 .await

```rust
// ❌ 错误：异步闭包返回的是 Future，不是结果
let result: String = fetch_data().await;

// ✅ 正确
let fetch = async || reqwest::get("...").await?.text().await;
let result = fetch().await?;  // 调用得 Future，await 得结果
```

### 2. 生命周期陷阱

```rust
// ❌ 错误：返回引用到捕获的变量
let bad_closure = async || -> &str {
    let s = String::from("local");
    &s  // s 在闭包结束时被 drop
};

// ✅ 正确：返回所有权
let good_closure = async move || -> String {
    let s = String::from("owned");
    s  // 所有权转移
};
```

### 3. Send/Sync 边界

```rust
// ⚠️ 跨线程使用需要 Send bound
let handler: Box<dyn AsyncFn() -> () + Send> =
    Box::new(async || { /* ... */ });

// tokio::spawn 要求 Future 是 Send
tokio::spawn(async move {
    async_closure().await  // 确保闭包满足 Send
});
```

## 🎮 动手练习

### 练习 1: 异步管道构建器

```rust
struct AsyncPipeline<T> {
    stages: Vec<Box<dyn AsyncFn(T) -> T + Send>>,
}

impl<T: Send + 'static> AsyncPipeline<T> {
    fn new() -> Self { Self { stages: vec![] } }

    fn add_stage<F>(mut self, f: F) -> Self
    where F: AsyncFn(T) -> T + Send + 'static {
        self.stages.push(Box::new(f)); self
    }

    async fn process(&self, input: T) -> T {
        let mut current = input;
        for stage in &self.stages {
            current = stage.call((current,)).await;
        }
        current
    }
}

let pipeline = AsyncPipeline::new()
    .add_stage(async |data| validate(data).await)
    .add_stage(async |data| transform(data).await);
let result = pipeline.process(raw_data).await;
```

### 练习 2: 带退避的重试机制

```rust
fn with_exponential_backoff<F, T, E>(
    max_retries: u32,
    operation: F,
) -> impl AsyncFn() -> Result<T, E>
where F: AsyncFn() -> Result<T, E> + Clone,
{
    async move || {
        let mut retries = 0;
        loop {
            match operation.call(()).await {
                Ok(result) => return Ok(result),
                Err(e) if retries < max_retries => {
                    let delay = Duration::from_millis(100 * 2_u64.pow(retries));
                    tokio::time::sleep(delay).await;
                    retries += 1;
                }
                Err(e) => return Err(e),
            }
        }
    }
}
```

### 练习 3: 并发限流下载器

```rust
async fn download_with_rate_limit(
    urls: Vec<String>,
    max_concurrent: usize,
) -> Vec<Result<Bytes, Error>> {
    let client = Arc::new(reqwest::Client::new());

    stream::iter(urls)
        .map(async move |url| {
            let client = client.clone();
            async move {
                client.get(&url).send().await?.bytes().await
            }.await
        })
        .buffer_unordered(max_concurrent)
        .collect().await
}
```

## 📖 延伸阅读

- [Rust 1.85 Release Notes - Async Closures](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0.html)
- [RFC 3668 - Async Closures](https://rust-lang.github.io/rfcs/3668-async-closures.html)
- [Async Book - 闭包章节](https://rust-lang.github.io/async-book/03_async_await/01_chapter.html)
- [futures crate 文档](https://docs.rs/futures/latest/futures/)
- [tokio 文档 - Streams](https://tokio.rs/tokio/tutorial/streams)

---

> 💡 **提示**: 异步闭包是 Rust 异步编程的重要里程碑，它统一了同步和异步的闭包语义。结合 Edition 2024 的改进，现在可以写出更简洁、更直观的异步代码。
