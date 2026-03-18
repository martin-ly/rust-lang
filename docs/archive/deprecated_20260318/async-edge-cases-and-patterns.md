# Async边界情况与高级模式

> Async编程的边界情况、陷阱与高级模式

---

## 目录

- [Async边界情况与高级模式](#async边界情况与高级模式)
  - [目录](#目录)
  - [1. 递归Async函数](#1-递归async函数)
    - [1.1 问题: 无限类型递归](#11-问题-无限类型递归)
    - [1.2 解决方案](#12-解决方案)
  - [2. 异步递归数据结构遍历](#2-异步递归数据结构遍历)
    - [2.1 树遍历的async版本](#21-树遍历的async版本)
  - [3. 异步Drop模式](#3-异步drop模式)
    - [3.1 问题: Drop是同步的](#31-问题-drop是同步的)
    - [3.2 解决方案: AsyncDrop模式](#32-解决方案-asyncdrop模式)
  - [4. Select! 并发模式详解](#4-select-并发模式详解)
    - [4.1 select!宏的完整语义](#41-select宏的完整语义)
    - [4.2 Select与取消安全](#42-select与取消安全)
  - [5. Stream模式与背压](#5-stream模式与背压)
    - [5.1 自定义Stream实现](#51-自定义stream实现)
    - [5.2 Buffer与并发控制](#52-buffer与并发控制)
  - [6. 类型擦除与动态分发](#6-类型擦除与动态分发)
    - [6.1 BoxFuture与类型擦除](#61-boxfuture与类型擦除)
    - [6.2 自定义Future组合子](#62-自定义future组合子)
  - [7. 内存布局优化](#7-内存布局优化)
    - [7.1 Future大小优化](#71-future大小优化)
    - [7.2 零分配Future](#72-零分配future)
  - [8. 测试异步代码](#8-测试异步代码)
    - [8.1 时间控制测试](#81-时间控制测试)
    - [8.2 Mock异步服务](#82-mock异步服务)

## 1. 递归Async函数

### 1.1 问题: 无限类型递归

```rust
// 编译错误: 递归async函数
async fn fib(n: u32) -> u32 {
    if n <= 1 {
        n
    } else {
        fib(n - 1).await + fib(n - 2).await  // 错误!
    }
}

// 错误信息:
// error: recursion in an `async fn` requires boxing
```

**问题分析**:

$$
\text{type}(\text{fib}) = \text{Future}<\text{Output}=\text{u32}, \text{State}=\text{FibFuture}>
$$

$$
\text{FibFuture} \text{ contains } \text{fib}(n-1) \text{ and } \text{fib}(n-2) \text{ futures}
$$

$$
\text{type}(\text{fib}(n)) \text{ depends on } \text{type}(\text{fib}(n-1))
$$

导致**无限递归类型**!

### 1.2 解决方案

```rust
use std::pin::Pin;
use std::future::Future;

// 方案1: 使用Box::pin
fn fib(n: u32) -> Pin<Box<dyn Future<Output = u32>>> {
    Box::pin(async move {
        if n <= 1 {
            n
        } else {
            fib(n - 1).await + fib(n - 2).await
        }
    })
}

// 方案2: 使用递归枚举
enum FibFuture {
    Ready(u32),
    Computing {
        n: u32,
        state: FibState,
    },
}

enum FibState {
    Start,
    WaitingLeft(Pin<Box<FibFuture>>),
    WaitingRight(u32, Pin<Box<FibFuture>>),
}

impl Future for FibFuture {
    type Output = u32;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<u32> {
        // 实现状态机...
        todo!()
    }
}
```

---

## 2. 异步递归数据结构遍历

### 2.1 树遍历的async版本

```rust
use std::pin::Pin;
use std::future::Future;

struct Node {
    value: i32,
    children: Vec<Node>,
}

// 异步遍历树
fn async_walk(node: &Node) -> Pin<Box<dyn Future<Output = i32> + '_>> {
    Box::pin(async move {
        let mut sum = node.value;

        for child in &node.children {
            sum += async_walk(child).await;
        }

        sum
    })
}

// 更高效的迭代版本 (避免栈溢出)
async fn async_walk_iterative(root: &Node) -> i32 {
    let mut stack = vec![root];
    let mut sum = 0;

    while let Some(node) = stack.pop() {
        sum += node.value;

        // 异步保存检查点
        if stack.len() % 100 == 0 {
            tokio::task::yield_now().await;
        }

        stack.extend(&node.children);
    }

    sum
}
```

---

## 3. 异步Drop模式

### 3.1 问题: Drop是同步的

```rust
struct AsyncResource {
    connection: Connection,
}

impl Drop for AsyncResource {
    fn drop(&mut self) {
        // 错误: 无法在这里await!
        // self.connection.close().await;
    }
}
```

### 3.2 解决方案: AsyncDrop模式

```rust
// 方案1: 显式关闭方法
struct AsyncResource {
    connection: Connection,
}

impl AsyncResource {
    async fn close(mut self) {
        self.connection.close().await;
        // self在这里被消耗，不会调用Drop
    }
}

// 方案2: 使用scopeguard模式
use scopeguard::defer;

async fn use_resource() {
    let resource = AsyncResource::new();

    defer! {
        // 同步清理
    }

    resource.do_work().await;

    resource.close().await;  // 显式异步关闭
}

// 方案3: 使用tokio::spawn清理
impl Drop for AsyncResource {
    fn drop(&mut self) {
        if let Some(conn) = self.connection.take() {
            tokio::spawn(async move {
                conn.close().await;
            });
        }
    }
}
```

---

## 4. Select! 并发模式详解

### 4.1 select!宏的完整语义

```rust
tokio::select! {
    // 模式1: 基础分支
    result = future1 => {
        // future1完成时执行
    }

    // 模式2: 带错误处理
    Ok(result) = future2 => {
        // future2成功完成
    }
    Err(e) = future2 => {
        // future2返回错误
    }

    // 模式3: 模式匹配
    Some(v) = stream.next() => {
        // stream产生值
    }

    // 模式4: 取消安全分支
    _ = cancellation_token.cancelled() => {
        // 收到取消信号
    }

    // 模式5: 超时
    _ = tokio::time::sleep(Duration::from_secs(5)) => {
        // 超时处理
    }

    // 模式6: 默认分支
    else => {
        // 所有future都Pending时
    }
}
```

**形式化语义 SELECT-1**:

$$
\text{select}(\{ f_1, f_2, \ldots, f_n \}) = f_i \text{ where } \text{poll}(f_i) = \text{Ready}(v) \text{ first}
$$

**公平性保证**:

$$
\forall f_i.\ P(\text{selected}(f_i)) \geq \frac{1}{n} \text{ (轮询调度)}
$$

### 4.2 Select与取消安全

```rust
// 取消不安全的select使用
async fn unsafe_pattern() {
    loop {
        tokio::select! {
            // 如果future1完成，future2被取消
            // 但future2可能已部分处理数据
            v = future1 => { process(v).await; }
            v = future2 => { process(v).await; }
        }
    }
}

// 取消安全的版本
async fn safe_pattern() {
    let mut f1 = future1.fuse();
    let mut f2 = future2.fuse();

    loop {
        tokio::select! {
            v = f1 => {
                if f2.is_terminated() {
                    // 确保f2不会丢失数据
                }
                process(v).await;
            }
            v = f2 => { process(v).await; }
            complete => break,  // 所有stream完成
        }
    }
}
```

---

## 5. Stream模式与背压

### 5.1 自定义Stream实现

```rust
use std::pin::Pin;
use std::task::{Context, Poll};
use tokio::stream::Stream;

// 带背压控制的Stream
pub struct BackpressureStream<T> {
    receiver: mpsc::Receiver<T>,
    max_inflight: usize,
    inflight: Arc<AtomicUsize>,
}

impl<T> Stream for BackpressureStream<T> {
    type Item = T;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<T>> {
        // 检查背压
        let current = self.inflight.load(Ordering::Acquire);

        if current >= self.max_inflight {
            // 达到上限，注册waker等待
            cx.waker().wake_by_ref();
            return Poll::Pending;
        }

        // 尝试接收
        match self.receiver.poll_recv(cx) {
            Poll::Ready(Some(item)) => {
                self.inflight.fetch_add(1, Ordering::Release);
                Poll::Ready(Some(item))
            }
            other => other,
        }
    }
}

// 处理完成时减少计数
impl<T> Drop for BackpressureGuard<T> {
    fn drop(&mut self) {
        self.inflight.fetch_sub(1, Ordering::Release);
    }
}
```

### 5.2 Buffer与并发控制

```rust
use tokio::stream::StreamExt;

stream
    // 缓冲: 允许最多10个未处理元素
    .buffered(10)

    // 并发处理: 最多4个并发任务
    .map(|x| async move { process(x).await })
    .buffer_unordered(4)

    // 限流: 每100ms最多一个元素
    .throttle(Duration::from_millis(100))

    // 超时: 每个元素最多5秒
    .timeout(Duration::from_secs(5))

    // 收集结果
    .collect::<Vec<_>>()
    .await;
```

---

## 6. 类型擦除与动态分发

### 6.1 BoxFuture与类型擦除

```rust
use std::pin::Pin;
use std::future::Future;

// 类型擦除的Future
pub type BoxFuture<'a, T> = Pin<Box<dyn Future<Output = T> + Send + 'a>>;

// 在集合中存储不同类型Future
pub struct TaskQueue {
    tasks: Vec<BoxFuture<'static, ()>>,
}

impl TaskQueue {
    pub fn push<F>(&mut self, future: F)
    where
        F: Future<Output = ()> + Send + 'static,
    {
        self.tasks.push(Box::pin(future));
    }

    pub async fn run_all(mut self) {
        for task in self.tasks {
            task.await;
        }
    }
}

// 动态trait对象
pub trait AsyncService: Send {
    fn call(&self, req: Request) -> BoxFuture<'_, Response>;
}

impl AsyncService for MyService {
    fn call(&self, req: Request) -> BoxFuture<'_, Response> {
        Box::pin(async move {
            // 处理请求
            Response::new()
        })
    }
}
```

### 6.2 自定义Future组合子

```rust
// OrElse组合子
pub struct OrElse<Fut, F> {
    future: Fut,
    f: Option<F>,
}

impl<Fut, F, Fut2> Future for OrElse<Fut, F>
where
    Fut: Future,
    F: FnOnce(Fut::Error) -> Fut2,
    Fut2: Future<Output = Result<Fut::Item, Fut2::Error>>,
{
    type Item = Fut::Item;
    type Error = Fut2::Error;

    fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
        match self.future.poll() {
            Ok(Async::Ready(v)) => Ok(Async::Ready(v)),
            Ok(Async::NotReady) => Ok(Async::NotReady),
            Err(e) => {
                let f = self.f.take().expect("polled twice");
                // 转换到替代Future...
            }
        }
    }
}
```

---

## 7. 内存布局优化

### 7.1 Future大小优化

```rust
// 未优化的版本: 占用空间大
async fn unoptimized() -> u8 {
    let large_data = [0u8; 1024];  // 占用1KB
    async { }.await;
    42
}

// 优化版本: 使用Box减少栈空间
async fn optimized() -> u8 {
    let large_data = Box::new([0u8; 1024]);
    async { }.await;
    42
}

// 使用Box::pin优化递归
fn recursive_optimized(n: usize) -> Pin<Box<dyn Future<Output = ()>>> {
    Box::pin(async move {
        if n > 0 {
            recursive_optimized(n - 1).await;
        }
    })
}
```

### 7.2 零分配Future

```rust
// 使用pin-project-lite减少开销
use pin_project_lite::pin_project;

pin_project! {
    pub struct CustomFuture<T> {
        // 内联存储，无额外分配
        state: State,
        data: T,
    }
}

// 使用const泛型优化
pub struct ArrayFuture<const N: usize> {
    data: [u8; N],
}

// 静态future
pub static STATIC_FUTURE: Ready<()> = Ready::new(());
```

---

## 8. 测试异步代码

### 8.1 时间控制测试

```rust
use tokio::time::{pause, resume, advance, Instant};

#[tokio::test]
async fn test_with_time_control() {
    // 暂停时间
    pause();

    let start = Instant::now();

    let task = tokio::spawn(async {
        tokio::time::sleep(Duration::from_secs(60)).await;
        "completed"
    });

    // 快进时间60秒
    advance(Duration::from_secs(60)).await;

    let result = task.await.unwrap();
    assert_eq!(result, "completed");

    // 恢复时间
    resume();
}
```

### 8.2 Mock异步服务

```rust
use mockall::automock;

#[automock]
#[async_trait]
trait AsyncService {
    async fn fetch(&self, id: u64) -> Result<Data, Error>;
}

#[tokio::test]
async fn test_with_mock() {
    let mut mock = MockAsyncService::new();

    mock.expect_fetch()
        .with(eq(42))
        .times(1)
        .returning(|_| Box::pin(async { Ok(Data::default()) }));

    let result = mock.fetch(42).await;
    assert!(result.is_ok());
}
```

---

**状态**: ✅ 边界情况与高级模式文档完成
