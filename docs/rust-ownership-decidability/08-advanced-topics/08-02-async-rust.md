# 异步Rust与所有权深度解析

> **权威来源**: Rust Async Book, Pin API RFC, Tokio Documentation, async-std Documentation

## 目录

- [异步Rust与所有权深度解析](#异步rust与所有权深度解析)
  - [目录](#目录)
  - [1. 异步编程基础](#1-异步编程基础)
    - [1.1 为什么需要异步编程](#11-为什么需要异步编程)
    - [1.2 异步编程的核心概念](#12-异步编程的核心概念)
    - [1.3 协作式调度 vs 抢占式调度](#13-协作式调度-vs-抢占式调度)
  - [2. Future Trait深入理解](#2-future-trait深入理解)
    - [2.1 Future的生命周期](#21-future的生命周期)
    - [2.2 Future的组合与链式调用](#22-future的组合与链式调用)
    - [2.3 Future的内存布局](#23-future的内存布局)
  - [3. Pin与自引用类型](#3-pin与自引用类型)
    - [3.1 为什么需要Pin](#31-为什么需要pin)
    - [3.2 Pin的类型系统](#32-pin的类型系统)
    - [3.3 安全地自引用结构体](#33-安全地自引用结构体)
    - [3.4 Pin在异步代码中的应用](#34-pin在异步代码中的应用)
  - [4. async/await原理](#4-asyncawait原理)
    - [4.1 语法糖展开](#41-语法糖展开)
    - [4.2 生命周期与捕获](#42-生命周期与捕获)
    - [4.3 async trait的挑战](#43-async-trait的挑战)
  - [5. 异步运行时比较](#5-异步运行时比较)
    - [5.1 Tokio运行时架构](#51-tokio运行时架构)
    - [5.2 async-std运行时](#52-async-std运行时)
    - [5.3 运行时比较](#53-运行时比较)
    - [5.4 运行时选择指南](#54-运行时选择指南)
  - [6. 流处理与Stream Trait](#6-流处理与stream-trait)
    - [6.1 Stream基础](#61-stream基础)
    - [6.2 高级流操作](#62-高级流操作)
    - [6.3 背压与流量控制](#63-背压与流量控制)
  - [7. 高级所有权模式](#7-高级所有权模式)
    - [7.1 跨await的所有权转移](#71-跨await的所有权转移)
    - [7.2 生命周期与异步闭包](#72-生命周期与异步闭包)
    - [7.3 取消安全](#73-取消安全)
  - [8. 性能分析与优化](#8-性能分析与优化)
    - [8.1 任务调度优化](#81-任务调度优化)
    - [8.2 内存优化](#82-内存优化)
    - [8.3 性能分析工具](#83-性能分析工具)
  - [9. 实际应用案例](#9-实际应用案例)
    - [9.1 高性能Web服务器](#91-高性能web服务器)
    - [9.2 数据库连接池](#92-数据库连接池)
    - [9.3 消息队列消费者](#93-消息队列消费者)
  - [总结](#总结)
  - [参考资源](#参考资源)

---

## 1. 异步编程基础

### 1.1 为什么需要异步编程

在传统的同步编程中，当程序执行 I/O 操作（如网络请求、文件读写）时，线程会被阻塞，无法执行其他任务。异步编程允许在等待 I/O 完成时释放线程去处理其他任务，从而显著提高资源利用率。

```rust
// 同步代码 - 线程阻塞
fn fetch_data_sync() -> String {
    let response = reqwest::blocking::get("https://api.example.com").unwrap();
    response.text().unwrap()  // 线程在这里阻塞
}

// 异步代码 - 线程不阻塞
async fn fetch_data_async() -> String {
    let response = reqwest::get("https://api.example.com").await.unwrap();
    response.text().await.unwrap()  // 线程可以执行其他任务
}
```

### 1.2 异步编程的核心概念

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};

// Future trait 是异步Rust的核心
trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}

// Poll 枚举表示异步操作的状态
enum Poll<T> {
    Ready(T),      // 操作完成，返回结果
    Pending,       // 操作未完成，需要稍后重试
}
```

### 1.3 协作式调度 vs 抢占式调度

```rust
// Rust使用协作式调度 - 任务显式让出控制权
async fn cooperative_task() {
    loop {
        do_some_work().await;  // 让出控制权
        tokio::time::sleep(Duration::from_millis(100)).await;  // 让出控制权
    }
}

// 对比：线程是抢占式调度
fn threaded_task() {
    loop {
        do_some_work();  // 可能被强制中断
        std::thread::sleep(Duration::from_millis(100));
    }
}
```

---

## 2. Future Trait深入理解

### 2.1 Future的生命周期

```rust
use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll};
use std::time::Duration;

// 自定义Future实现
struct Delay {
    when: std::time::Instant,
}

impl Delay {
    fn new(duration: Duration) -> Self {
        Self {
            when: std::time::Instant::now() + duration,
        }
    }
}

impl Future for Delay {
    type Output = &'static str;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if std::time::Instant::now() >= self.when {
            // 时间到了，返回Ready
            Poll::Ready("done")
        } else {
            // 时间还没到，注册唤醒器
            let waker = cx.waker().clone();
            let when = self.when;

            std::thread::spawn(move || {
                let now = std::time::Instant::now();
                if when > now {
                    std::thread::sleep(when - now);
                }
                waker.wake();
            });

            Poll::Pending
        }
    }
}
```

### 2.2 Future的组合与链式调用

```rust
use futures::future::{self, FutureExt, TryFutureExt};

async fn future_composition() -> Result<String, Error> {
    // and_then: 在成功时继续
    let result = fetch_user_id()
        .and_then(|id| fetch_user_name(id))
        .and_then(|name| fetch_user_profile(name))
        .await;

    // map: 转换结果
    let transformed = fetch_data()
        .map(|data| data.to_uppercase())
        .await;

    // or_else: 在失败时恢复
    let recovered = fetch_data()
        .or_else(|_| fetch_fallback_data())
        .await;

    Ok(result?)
}

// 使用 async 块组合复杂的异步逻辑
async fn complex_composition(user_id: u64) -> Result<UserProfile, Error> {
    let profile = async {
        let user = fetch_user(user_id).await?;
        let settings = fetch_settings(user_id).await?;
        let permissions = fetch_permissions(user.id).await?;

        Ok(UserProfile {
            user,
            settings,
            permissions,
        })
    }.await;

    profile
}
```

### 2.3 Future的内存布局

```rust
// async函数返回的Future是一个状态机
async fn example() -> i32 {
    let x = 1;           // 状态1
    some_async_op().await;  // 状态2
    let y = 2;           // 状态3
    another_op().await;  // 状态4
    x + y                // 完成
}

// 编译器生成的状态机大致如下：
enum ExampleFuture {
    Start,
    WaitingOnSomeAsyncOp { x: i32 },
    WaitingOnAnotherOp { x: i32, y: i32 },
    Done,
}

// 每个.await点都是一个状态转换点
impl Future for ExampleFuture {
    type Output = i32;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<i32> {
        loop {
            match *self {
                ExampleFuture::Start => {
                    let x = 1;
                    *self = ExampleFuture::WaitingOnSomeAsyncOp { x };
                }
                ExampleFuture::WaitingOnSomeAsyncOp { x } => {
                    match some_async_op().poll(cx) {
                        Poll::Ready(_) => {
                            let y = 2;
                            *self = ExampleFuture::WaitingOnAnotherOp { x, y };
                        }
                        Poll::Pending => return Poll::Pending,
                    }
                }
                ExampleFuture::WaitingOnAnotherOp { x, y } => {
                    match another_op().poll(cx) {
                        Poll::Ready(_) => {
                            *self = ExampleFuture::Done;
                            return Poll::Ready(x + y);
                        }
                        Poll::Pending => return Poll::Pending,
                    }
                }
                ExampleFuture::Done => panic!("poll after completion"),
            }
        }
    }
}
```

---

## 3. Pin与自引用类型

### 3.1 为什么需要Pin

```rust
// 问题：自引用结构体在移动时会出问题
struct SelfReferential {
    data: String,
    ptr_to_data: *const String,  // 指向data的指针
}

impl SelfReferential {
    fn new(data: String) -> Self {
        let mut s = Self {
            data,
            ptr_to_data: std::ptr::null(),
        };
        s.ptr_to_data = &s.data;
        s
    }
}

fn problem_demo() {
    let s1 = SelfReferential::new(String::from("hello"));
    // s1.ptr_to_data 指向 s1.data

    let s2 = s1;  // 移动！
    // 现在 s1.ptr_to_data 指向已释放的内存（悬垂指针）
}
```

### 3.2 Pin的类型系统

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

// Unpin trait: 可以安全移动的类型
pub auto trait Unpin {}

// !Unpin 类型不能安全移动
impl !Unpin for SelfReferential {}

// 或者使用 PhantomPinned
struct SelfReferential {
    data: String,
    ptr_to_data: *const String,
    _pin: PhantomPinned,  // 自动实现 !Unpin
}

// Pin<P<T>> 保证 T 不会被移动（如果 T: !Unpin）
fn pin_operations() {
    // 创建Pin
    let data = String::from("pinned");
    let pinned: Pin<Box<String>> = Box::pin(data);

    // 可以从Pin获取引用，但不能获取所有权
    let ref_to_string: &String = pinned.as_ref().get_ref();

    // 对于Unpin类型，可以从Pin解出
    let unpinned: Box<String> = Pin::into_inner(pinned);
}
```

### 3.3 安全地自引用结构体

```rust
use std::pin::Pin;
use std::marker::PhantomPinned;

struct AsyncDataBuffer {
    buffer: Vec<u8>,
    read_ptr: *const u8,   // 指向buffer内部
    write_ptr: *mut u8,    // 指向buffer内部
    _pin: PhantomPinned,
}

impl AsyncDataBuffer {
    fn new(capacity: usize) -> Pin<Box<Self>> {
        let buffer = vec![0u8; capacity];
        let mut boxed = Box::new(Self {
            buffer,
            read_ptr: std::ptr::null(),
            write_ptr: std::ptr::null_mut(),
            _pin: PhantomPinned,
        });

        // 初始化指针
        let ptr = boxed.buffer.as_mut_ptr();
        boxed.read_ptr = ptr;
        boxed.write_ptr = ptr;

        Box::into_pin(boxed)
    }

    // 自修改方法需要Pin<&mut Self>
    fn advance_read(self: Pin<&mut Self>, n: usize) {
        // SAFETY: 我们不会移动self，只是修改指针
        unsafe {
            let this = self.get_unchecked_mut();
            this.read_ptr = this.read_ptr.add(n);
        }
    }

    fn advance_write(self: Pin<&mut Self>, n: usize) {
        unsafe {
            let this = self.get_unchecked_mut();
            this.write_ptr = this.write_ptr.add(n);
        }
    }

    fn readable_slice(self: Pin<&Self>) -> &[u8] {
        unsafe {
            let this = self.get_ref();
            let len = this.write_ptr.offset_from(this.read_ptr) as usize;
            std::slice::from_raw_parts(this.read_ptr, len)
        }
    }

    fn writable_slice(self: Pin<&mut Self>) -> &mut [u8] {
        unsafe {
            let this = self.get_unchecked_mut();
            let offset = this.write_ptr.offset_from(this.buffer.as_ptr()) as usize;
            let len = this.buffer.len() - offset;
            std::slice::from_raw_parts_mut(this.write_ptr, len)
        }
    }
}
```

### 3.4 Pin在异步代码中的应用

```rust
use std::pin::Pin;
use std::future::Future;
use std::task::{Context, Poll};

// 异步块可能包含自引用
async fn async_with_self_reference() {
    let local_data = vec![1, 2, 3, 4, 5];

    // 这个异步块可能持有指向local_data的引用
    async {
        // 引用local_data
        println!("{:?}", &local_data);
        some_async_op().await;
        println!("{:?}", &local_data);  // 引用在await后仍然有效
    }.await;
}

// 手动实现的Future使用Pin
struct MyFuture<'a> {
    data: &'a [u8],
    state: State,
}

enum State {
    Start,
    Waiting,
    Done,
}

impl<'a> Future for MyFuture<'a> {
    type Output = usize;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<usize> {
        // self是Pin<&mut Self>，保证self不会被移动
        // 因此self.data引用在整个poll过程中保持有效
        let this = unsafe { self.get_unchecked_mut() };

        match this.state {
            State::Start => {
                // 处理数据
                let len = this.data.len();
                this.state = State::Waiting;

                // 注册唤醒
                cx.waker().wake_by_ref();
                Poll::Pending
            }
            State::Waiting => {
                this.state = State::Done;
                Poll::Ready(this.data.len())
            }
            State::Done => panic!("poll after completion"),
        }
    }
}
```

---

## 4. async/await原理

### 4.1 语法糖展开

```rust
// 原始async代码
async fn fetch_and_process(url: &str) -> Result<String, Error> {
    let response = fetch(url).await?;
    let text = response.text().await?;
    let processed = process(text).await?;
    Ok(processed)
}

// 编译器大致转换后的代码
fn fetch_and_process<'a>(url: &'a str) -> impl Future<Output = Result<String, Error>> + 'a {
    async move {
        let response = fetch(url).await?;
        let text = response.text().await?;
        let processed = process(text).await?;
        Ok(processed)
    }
}

// 状态机展开（简化版）
enum FetchAndProcessFuture<'a> {
    Start { url: &'a str },
    WaitingFetch { url: &'a str },
    WaitingText { response: Response },
    WaitingProcess { text: String },
    Done,
}

impl<'a> Future for FetchAndProcessFuture<'a> {
    type Output = Result<String, Error>;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        loop {
            match *self {
                FetchAndProcessFuture::Start { url } => {
                    let fut = fetch(url);
                    *self = FetchAndProcessFuture::WaitingFetch { url };
                    // 实际上这里会poll fetch future
                }
                // ... 其他状态
                _ => panic!("poll after completion"),
            }
        }
    }
}
```

### 4.2 生命周期与捕获

```rust
// async fn 与 async move 的区别

// async fn: 参数按引用捕获
async fn borrow_params(data: &str) -> usize {
    println!("{}", data);  // 借用data
    sleep(Duration::from_secs(1)).await;
    data.len()  // 在await后仍可使用
}

// async move: 按值捕获（移动）
fn move_capture() {
    let data = String::from("hello");

    let future = async move {
        // data被移动进async块
        println!("{}", data);
        sleep(Duration::from_secs(1)).await;
        println!("{}", data);  // 仍然拥有data
    };

    // data在这里不可用
}

// 混合捕获模式
fn mixed_capture() {
    let owned = String::from("owned");
    let borrowed = String::from("borrowed");

    // 创建借用和移动的组合
    let borrowed_ref = &borrowed;

    let future = async move {
        // owned被移动
        println!("{}", owned);

        // borrowed_ref被移动，但它指向borrowed
        println!("{}", borrowed_ref);

        sleep(Duration::from_secs(1)).await;

        // 仍然有效
        println!("{}", owned);
        println!("{}", borrowed_ref);
    };

    // borrowed必须存活到future完成
    drop(borrowed); // 错误！future还在借用
}
```

### 4.3 async trait的挑战

```rust
// 问题：async fn在trait中的问题
trait AsyncProcessor {
    async fn process(&self, data: Vec<u8>) -> Result<Vec<u8>, Error>;
    // 错误：trait中的async fn返回impl Future，但trait不能包含impl Trait
}

// 解决方案1：使用async-trait宏
use async_trait::async_trait;

#[async_trait]
trait AsyncProcessor {
    async fn process(&self, data: Vec<u8>) -> Result<Vec<u8>, Error>;
}

#[async_trait]
impl AsyncProcessor for MyProcessor {
    async fn process(&self, data: Vec<u8>) -> Result<Vec<u8>, Error> {
        // 实现
        Ok(data)
    }
}

// 解决方案2：手动返回Pin<Box<dyn Future>>
trait AsyncProcessorManual {
    fn process(&self, data: Vec<u8>) -> Pin<Box<dyn Future<Output = Result<Vec<u8>, Error>> + Send + '_>>;
}

impl AsyncProcessorManual for MyProcessor {
    fn process(&self, data: Vec<u8>) -> Pin<Box<dyn Future<Output = Result<Vec<u8>, Error>> + Send + '_>> {
        Box::pin(async move {
            // 实现
            Ok(data)
        })
    }
}

// 解决方案3：使用关联类型（Rust 1.75+）
trait AsyncProcessorAssoc {
    type Future<'a>: Future<Output = Result<Vec<u8>, Error>> + Send
    where
        Self: 'a;

    fn process(&self, data: Vec<u8>) -> Self::Future<'_>;
}

// 解决方案4：RPITIT (Return Position Impl Trait In Traits) - Rust 1.75+
trait AsyncProcessorRPITIT {
    fn process(&self, data: Vec<u8>) -> impl Future<Output = Result<Vec<u8>, Error>> + Send;
}
```

---

## 5. 异步运行时比较

### 5.1 Tokio运行时架构

```rust
use tokio::runtime::{Builder, Runtime};
use tokio::task;

// 创建多线程运行时
fn create_tokio_runtime() -> Runtime {
    Builder::new_multi_thread()
        .worker_threads(4)           // 工作线程数
        .max_blocking_threads(512)   // 最大阻塞线程数
        .thread_stack_size(3 * 1024 * 1024)  // 线程栈大小
        .enable_all()                // 启用所有功能
        .build()
        .unwrap()
}

// 单线程运行时（用于资源受限环境）
fn create_current_thread_runtime() -> Runtime {
    Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
}

// Tokio任务类型
tokio::spawn(async {
    // 异步任务 - 在工作者线程上执行
});

tokio::task::spawn_blocking(|| {
    // 阻塞任务 - 在专用线程池上执行
    std::thread::sleep(Duration::from_secs(10));
});

// LocalSet用于!Send的Future
tokio::task::LocalSet::new().run_until(async {
    let rc = std::rc::Rc::new(1);
    tokio::task::spawn_local(async move {
        // 可以使用Rc，不需要Send
        println!("{}", rc);
    }).await;
}).await;
```

### 5.2 async-std运行时

```rust
use async_std::task;

// async-std使用全局运行时
async fn async_std_example() {
    // spawn创建新任务
    let handle = task::spawn(async {
        println!("Hello from async-std");
        42
    });

    let result = handle.await;

    // 阻塞操作
    task::spawn_blocking(|| {
        std::thread::sleep(Duration::from_secs(1));
        "done"
    }).await;
}

// 配置运行时
fn configure_async_std() {
    // async-std使用环境变量配置
    // ASYNC_STD_THREAD_COUNT: 工作线程数
    // ASYNC_STD_THREAD_NAME: 线程名前缀
}
```

### 5.3 运行时比较

| 特性 | Tokio | async-std | smol |
|------|-------|-----------|------|
| 调度策略 | 多线程工作窃取 | 多线程工作窃取 | 简单单/多线程 |
| 阻塞任务 | spawn_blocking | spawn_blocking | spawn |
| 生态系统 | 最丰富 | 中等 | 轻量 |
| 二进制大小 | 较大 | 中等 | 较小 |
| 启动时间 | 稍慢 | 中等 | 快 |
| 定制化 | 高 | 中 | 低 |

```rust
// smol运行时示例
use smol::future;

fn smol_example() {
    smol::block_on(async {
        // smol使用更简单的API
        let task = smol::spawn(async {
            println!("Hello from smol");
        });

        task.await;
    });
}

// 自定义运行时组合
use tokio::runtime::Handle;

async fn mixed_runtime() {
    // 在Tokio中运行async-std兼容代码
    let handle = Handle::current();

    let result = handle.spawn(async {
        // Tokio任务
        tokio::time::sleep(Duration::from_millis(100)).await;
        "tokio result"
    }).await.unwrap();
}
```

### 5.4 运行时选择指南

```rust
// 使用Tokio的场景：
// - 大型网络应用
// - 需要完整的生态（HTTP, WebSocket, gRPC等）
// - 需要高级功能（如tracing集成）

// 使用async-std的场景：
// - 喜欢标准库风格的API
// - 中等规模项目

// 使用smol的场景：
// - 嵌入式或资源受限环境
// - 需要最小依赖
// - 学习目的

// 无运行时（裸Future）：
use futures::executor::block_on;

fn no_runtime() {
    // 最简单的执行器，仅用于测试
    block_on(async {
        println!("No runtime");
    });
}
```

---

## 6. 流处理与Stream Trait

### 6.1 Stream基础

```rust
use futures::stream::{self, Stream, StreamExt};
use std::pin::Pin;
use std::task::{Context, Poll};

// Stream trait类似于异步的Iterator
trait Stream {
    type Item;
    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>>;
}

// 基本流操作
async fn stream_basics() {
    // 从集合创建流
    let mut stream = stream::iter(vec![1, 2, 3, 4, 5]);

    // 遍历流
    while let Some(value) = stream.next().await {
        println!("{}", value);
    }

    // 使用for_each
    let stream = stream::iter(vec![1, 2, 3]);
    stream.for_each(|x| async move {
        println!("{}", x);
    }).await;
}
```

### 6.2 高级流操作

```rust
use futures::stream::{StreamExt, TryStreamExt};
use tokio_stream::StreamExt as TokioStreamExt;

async fn advanced_stream_operations() {
    let stream = tokio_stream::iter(vec![1, 2, 3, 4, 5]);

    // 映射
    let mapped = stream.map(|x| x * 2);

    // 过滤
    let filtered = mapped.filter(|x| *x > 4);

    // 缓冲/批处理
    let buffered = filtered.buffered(3);  // 并发处理3个

    // 节流
    let throttled = buffered.throttle(Duration::from_millis(100));

    // 超时
    let timeout = throttled.timeout(Duration::from_secs(5));

    // 合并多个流
    let stream1 = tokio_stream::iter(vec![1, 2, 3]);
    let stream2 = tokio_stream::iter(vec![4, 5, 6]);
    let merged = stream1.merge(stream2);

    // 链式操作
    let result: Vec<i32> = tokio_stream::iter(vec![1, 2, 3, 4, 5])
        .map(|x| x * x)
        .filter(|x| *x > 4)
        .take(3)
        .collect()
        .await;
}

// 自定义Stream实现
struct IntervalStream {
    interval: Duration,
    next: Instant,
}

impl Stream for IntervalStream {
    type Item = Instant;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let now = Instant::now();

        if now >= self.next {
            let item = self.next;
            self.next = now + self.interval;
            Poll::Ready(Some(item))
        } else {
            // 注册定时器
            let waker = cx.waker().clone();
            let sleep_duration = self.next - now;

            tokio::spawn(async move {
                tokio::time::sleep(sleep_duration).await;
                waker.wake();
            });

            Poll::Pending
        }
    }
}
```

### 6.3 背压与流量控制

```rust
use futures::channel::mpsc;
use futures::stream::StreamExt;

async fn backpressure_example() {
    // 有界通道提供背压
    let (mut tx, mut rx) = mpsc::channel::<i32>(100);  // 缓冲区大小100

    // 生产者
    let producer = async move {
        for i in 0..1000 {
            // 当缓冲区满时，send会等待
            tx.send(i).await.unwrap();
            println!("Produced: {}", i);
        }
    };

    // 消费者
    let consumer = async move {
        while let Some(item) = rx.next().await {
            // 模拟慢速消费
            tokio::time::sleep(Duration::from_millis(10)).await;
            println!("Consumed: {}", item);
        }
    };

    futures::join!(producer, consumer);
}

// 速率限制
async fn rate_limiting() {
    use governor::{Quota, RateLimiter};
    use nonzero_ext::nonzero;

    let limiter = RateLimiter::direct(
        Quota::per_second(nonzero!(10u32))  // 每秒10个请求
    );

    let stream = stream::iter(0..100);

    stream.for_each(|i| async {
        limiter.until_ready().await;
        println!("Processing: {}", i);
    }).await;
}
```

---

## 7. 高级所有权模式

### 7.1 跨await的所有权转移

```rust
use std::sync::Arc;
use tokio::sync::RwLock;

// 模式1：Arc<RwLock<T>> 共享可变状态
async fn shared_mutable_state() {
    let data = Arc::new(RwLock::new(vec![1, 2, 3]));

    let mut handles = vec![];

    for i in 0..10 {
        let data = Arc::clone(&data);
        let handle = tokio::spawn(async move {
            let mut guard = data.write().await;
            guard.push(i);
            // 锁在这里自动释放
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.await.unwrap();
    }
}

// 模式2：Owned缓冲区模式
async fn owned_buffer_pattern() {
    let mut buffer = vec![0u8; 1024];

    loop {
        // 将buffer的所有权移入异步操作
        let (result, returned_buffer) = read_data(buffer).await;
        buffer = returned_buffer;

        if result == 0 {
            break;
        }

        process(&buffer[..result]);
    }
}

async fn read_data(mut buf: Vec<u8>) -> (usize, Vec<u8>) {
    // 读取数据到buf
    let n = 100; // 模拟读取
    (n, buf)
}
```

### 7.2 生命周期与异步闭包

```rust
// 异步闭包的生命周期挑战
fn async_closure_lifetime() {
    let data = String::from("hello");

    // 需要显式标注生命周期
    let closure = |x: &str| -> Pin<Box<dyn Future<Output = String> + '_>> {
        Box::pin(async move {
            format!("{} {}", data, x)
        })
    };

    // 使用
    let result = closure("world");
}

// 更好的方法：使用async_closure crate或手动实现
struct AsyncClosure<F> {
    data: String,
    func: F,
}

impl<F, Fut> AsyncClosure<F>
where
    F: Fn(String, &str) -> Fut,
    Fut: Future<Output = String>,
{
    async fn call(&self, arg: &str) -> String {
        (self.func)(self.data.clone(), arg).await
    }
}
```

### 7.3 取消安全

```rust
use tokio::select;

// 取消安全问题
async fn cancel_unsafe() {
    let mut buffer = vec![0u8; 1024];

    select! {
        result = read_into_buffer(&mut buffer) => {
            // 如果另一个分支先完成，read_into_buffer会被取消
            // buffer可能处于不一致状态
        }
        _ = tokio::time::sleep(Duration::from_secs(1)) => {
            // 超时
        }
    }
}

// 取消安全的实现
async fn cancel_safe() {
    // 方法1：使用单独的异步块
    let read_future = async {
        let mut buffer = vec![0u8; 1024];
        let n = read_into_buffer(&mut buffer).await?;
        Ok((buffer, n))
    };

    select! {
        result = read_future => {
            match result {
                Ok((buffer, n)) => {
                    // 安全使用buffer
                }
                Err(e) => {
                    // 处理错误
                }
            }
        }
        _ = tokio::time::sleep(Duration::from_secs(1)) => {
            // read_future被取消，没有不一致状态
        }
    }
}

// 取消安全的数据结构
use tokio::io::AsyncReadExt;

struct CancelSafeReader<R> {
    reader: R,
    buffer: Vec<u8>,
    read_pos: usize,
}

impl<R: AsyncRead + Unpin> CancelSafeReader<R> {
    async fn read_line(&mut self) -> Result<String, Error> {
        loop {
            // 在已有buffer中查找换行符
            if let Some(pos) = self.buffer[self.read_pos..].iter().position(|&b| b == b'\n') {
                let line_end = self.read_pos + pos;
                let line = String::from_utf8_lossy(&self.buffer[..line_end]).to_string();

                // 移动未处理数据到buffer开头
                self.buffer.copy_within(line_end + 1.., 0);
                self.buffer.truncate(self.buffer.len() - line_end - 1);
                self.read_pos = 0;

                return Ok(line);
            }

            // 需要更多数据
            self.read_pos = self.buffer.len();
            let mut temp = [0u8; 1024];
            let n = self.reader.read(&mut temp).await?;

            if n == 0 {
                // EOF
                let line = String::from_utf8_lossy(&self.buffer).to_string();
                self.buffer.clear();
                return Ok(line);
            }

            self.buffer.extend_from_slice(&temp[..n]);
        }
    }
}
```

---

## 8. 性能分析与优化

### 8.1 任务调度优化

```rust
use tokio::task;

// CPU密集型任务应在blocking线程池执行
async fn cpu_intensive_work(data: Vec<u8>) -> Vec<u8> {
    task::spawn_blocking(move || {
        // 加密、压缩等CPU密集型操作
        expensive_computation(data)
    }).await.unwrap()
}

// 批量处理减少上下文切换
async fn batch_processing(items: Vec<Item>) -> Vec<Result> {
    const BATCH_SIZE: usize = 100;

    let mut results = Vec::new();

    for chunk in items.chunks(BATCH_SIZE) {
        // 使用FuturesUnordered实现真正的并发
        let batch_futures: FuturesUnordered<_> = chunk
            .iter()
            .map(|item| process_item(item))
            .collect();

        let batch_results: Vec<_> = batch_futures.collect().await;
        results.extend(batch_results);
    }

    results
}

// 避免过多的小任务
async fn coalesced_work() {
    let (tx, mut rx) = mpsc::channel(100);

    // 收集器任务
    let collector = tokio::spawn(async move {
        let mut batch = Vec::new();
        let mut deadline = tokio::time::interval(Duration::from_millis(10));

        loop {
            tokio::select! {
                Some(item) = rx.recv() => {
                    batch.push(item);
                    if batch.len() >= 100 {
                        process_batch(std::mem::take(&mut batch)).await;
                    }
                }
                _ = deadline.tick() => {
                    if !batch.is_empty() {
                        process_batch(std::mem::take(&mut batch)).await;
                    }
                }
            }
        }
    });
}
```

### 8.2 内存优化

```rust
use bytes::BytesMut;

// 使用Bytes减少复制
async fn efficient_buffer_management() {
    let mut buf = BytesMut::with_capacity(4096);

    loop {
        // 读取数据
        let n = reader.read_buf(&mut buf).await.unwrap();

        if n == 0 {
            break;
        }

        // 分割出完整的消息
        while let Some(pos) = find_message_end(&buf) {
            let message = buf.split_to(pos);
            // message是Bytes，引用计数，零拷贝
            process_message(message.freeze()).await;
        }

        // 保留未完成的片段，复用内存
        if buf.len() > buf.capacity() / 2 {
            buf.reserve(4096);
        }
    }
}

// 减少Future的大小
async fn shrink_future_size() {
    // 不好：Future包含大量数据
    let big_data = vec![0u8; 1000000];
    let future = async move {
        // big_data被包含在Future中
        process(big_data).await;
    };

    // 好：将大数据放在堆上
    let big_data = Arc::new(vec![0u8; 1000000]);
    let future = async move {
        let data = Arc::clone(&big_data);
        process_arc(data).await;
    };
}
```

### 8.3 性能分析工具

```rust
// 使用tracing进行性能追踪
use tracing::{info_span, Instrument};

async fn instrumented_operation() {
    let result = async {
        // 业务逻辑
        expensive_work().await
    }
    .instrument(info_span!("expensive_operation", item_id = %id))
    .await;
}

// 使用tokio-console进行运行时分析
#[tokio::main]
async fn main() {
    // 启用console-subscriber
    console_subscriber::init();

    // 运行应用
    run_app().await;
}
```

---

## 9. 实际应用案例

### 9.1 高性能Web服务器

```rust
use tokio::net::{TcpListener, TcpStream};
use tokio::io::{AsyncReadExt, AsyncWriteExt};

async fn run_server() -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:8080").await?;

    println!("Server listening on 127.0.0.1:8080");

    loop {
        let (socket, addr) = listener.accept().await?;
        println!("New connection from: {}", addr);

        // 为每个连接生成任务
        tokio::spawn(async move {
            if let Err(e) = handle_connection(socket).await {
                eprintln!("Error handling connection: {}", e);
            }
        });
    }
}

async fn handle_connection(mut socket: TcpStream) -> Result<(), Box<dyn std::error::Error>> {
    let mut buf = vec![0u8; 1024];

    loop {
        let n = socket.read(&mut buf).await?;

        if n == 0 {
            println!("Client disconnected");
            return Ok(());
        }

        let request = String::from_utf8_lossy(&buf[..n]);
        println!("Received: {}", request);

        let response = format!(
            "HTTP/1.1 200 OK\r\nContent-Length: {}\r\n\r\n{}",
            request.len(),
            request
        );

        socket.write_all(response.as_bytes()).await?;
    }
}
```

### 9.2 数据库连接池

```rust
use deadpool::managed::{Manager, Pool, RecycleResult};
use tokio_postgres::{Client, Config, NoTls};

struct PostgresManager {
    config: Config,
}

#[async_trait]
impl Manager for PostgresManager {
    type Type = Client;
    type Error = tokio_postgres::Error;

    async fn create(&self) -> Result<Client, tokio_postgres::Error> {
        let (client, connection) = self.config.connect(NoTls).await?;

        // 在后台运行连接
        tokio::spawn(async move {
            if let Err(e) = connection.await {
                eprintln!("Connection error: {}", e);
            }
        });

        Ok(client)
    }

    async fn recycle(&self, client: &mut Client) -> RecycleResult<tokio_postgres::Error> {
        // 验证连接是否仍然有效
        match client.simple_query("SELECT 1").await {
            Ok(_) => Ok(()),
            Err(e) => Err(e.into()),
        }
    }
}

async fn use_connection_pool() {
    let manager = PostgresManager {
        config: Config::new(),
    };

    let pool = Pool::builder(manager)
        .max_size(16)
        .build()
        .unwrap();

    // 使用连接
    let client = pool.get().await.unwrap();
    let rows = client.query("SELECT * FROM users", &[]).await.unwrap();

    for row in &rows {
        let id: i32 = row.get(0);
        let name: String = row.get(1);
        println!("User: {} - {}", id, name);
    }
    // 连接自动归还到池中
}
```

### 9.3 消息队列消费者

```rust
use lapin::{Connection, ConnectionProperties, Consumer, options::*};
use futures::StreamExt;

async fn run_consumer() -> Result<(), Box<dyn std::error::Error>> {
    let conn = Connection::connect(
        "amqp://guest:guest@localhost:5672/%2f",
        ConnectionProperties::default(),
    ).await?;

    let channel = conn.create_channel().await?;

    let mut consumer = channel.basic_consume(
        "my_queue",
        "my_consumer",
        BasicConsumeOptions::default(),
        FieldTable::default(),
    ).await?;

    println!("Waiting for messages...");

    while let Some(delivery) = consumer.next().await {
        let delivery = delivery?;

        // 在单独的任务中处理消息
        tokio::spawn(async move {
            match process_message(&delivery.data).await {
                Ok(_) => {
                    delivery.ack(BasicAckOptions::default()).await.ok();
                }
                Err(e) => {
                    eprintln!("Error processing message: {}", e);
                    delivery.nack(BasicNackOptions::default()).await.ok();
                }
            }
        });
    }

    Ok(())
}

async fn process_message(data: &[u8]) -> Result<(), Box<dyn std::error::Error>> {
    let message: Message = serde_json::from_slice(data)?;

    // 幂等处理
    if is_already_processed(&message.id).await? {
        return Ok(());
    }

    // 实际处理
    let result = do_work(message).await;

    // 记录处理状态
    mark_as_processed(&message.id).await?;

    result
}
```

---

## 总结

异步Rust提供了强大的工具来构建高性能、高并发的应用程序。关键要点：

1. **理解Future状态机**：async/await是语法糖，底层是状态机实现
2. **正确使用Pin**：自引用类型需要Pin保证内存安全
3. **选择合适的运行时**：Tokio功能最全，async-std和smol更轻量
4. **处理所有权与生命周期**：跨await点的借用需要特别注意
5. **取消安全**：确保任务被取消时不会留下不一致状态
6. **流处理**：使用Stream trait处理异步序列数据
7. **性能优化**：合理使用阻塞线程池、批量处理、减少内存分配

---

## 参考资源

- [Rust Async Book](https://rust-lang.github.io/async-book/)
- [Tokio Documentation](https://tokio.rs/)
- [Pin API RFC](https://rust-lang.github.io/rfcs/2349-pin.html)
- [async-std Documentation](https://docs.rs/async-std/)
- [futures crate Documentation](https://docs.rs/futures/)
