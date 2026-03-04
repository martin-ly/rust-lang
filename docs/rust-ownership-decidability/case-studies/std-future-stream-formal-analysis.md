# Rust标准库 Future与Stream 形式化分析

> **主题**: 异步计算的基础抽象与组合
>
> **形式化框架**: 计算单子 + 延迟求值
>
> **参考**: Rust Standard Library; Future/Poll

---

## 目录

- [Rust标准库 Future与Stream 形式化分析](#rust标准库-future与stream-形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. Future trait形式化](#2-future-trait形式化)
    - [2.1 类型定义](#21-类型定义)
    - [定义 2.1 (Future trait)](#定义-21-future-trait)
    - [2.2 Poll语义](#22-poll语义)
    - [定理 2.1 (Poll契约)](#定理-21-poll契约)
    - [2.3 与Monad的关系](#23-与monad的关系)
    - [定理 2.2 (Future是Monad)](#定理-22-future是monad)
  - [3. Context与Waker](#3-context与waker)
    - [3.1 唤醒机制](#31-唤醒机制)
    - [定义 3.1 (Waker)](#定义-31-waker)
    - [定理 3.1 (唤醒保证)](#定理-31-唤醒保证)
    - [3.2 Waker内存安全](#32-waker内存安全)
    - [定理 3.2 (Waker线程安全)](#定理-32-waker线程安全)
  - [4. Stream trait](#4-stream-trait)
    - [4.1 异步迭代](#41-异步迭代)
    - [定义 4.1 (Stream trait)](#定义-41-stream-trait)
    - [4.2 与Future的关系](#42-与future的关系)
    - [定理 4.1 (Stream的累积是Future)](#定理-41-stream的累积是future)
  - [5. async/await语法糖](#5-asyncawait语法糖)
    - [5.1 状态机转换](#51-状态机转换)
    - [定理 5.1 (async fn状态机)](#定理-51-async-fn状态机)
    - [5.2 Pin与自引用](#52-pin与自引用)
    - [定理 5.2 (async fn自动Pin)](#定理-52-async-fn自动pin)
  - [6. 执行器(Executor)模型](#6-执行器executor模型)
    - [6.1 任务调度](#61-任务调度)
    - [定义 6.1 (Executor)](#定义-61-executor)
    - [定理 6.1 (任务生命周期)](#定理-61-任务生命周期)
    - [6.2 工作窃取](#62-工作窃取)
    - [定理 6.2 (Tokio工作窃取)](#定理-62-tokio工作窃取)
  - [7. 组合子分析](#7-组合子分析)
    - [7.1 then与map](#71-then与map)
    - [定理 7.1 (Future组合)](#定理-71-future组合)
    - [7.2 join与select](#72-join与select)
    - [定理 7.2 (并发组合)](#定理-72-并发组合)
  - [8. 内存安全](#8-内存安全)
    - [8.1 取消安全](#81-取消安全)
    - [定理 8.1 (取消安全定义)](#定理-81-取消安全定义)
    - [8.2 泄漏安全](#82-泄漏安全)
    - [定理 8.2 (异步泄漏)](#定理-82-异步泄漏)
  - [9. 反例与陷阱](#9-反例与陷阱)
    - [反例 9.1 (在async中阻塞)](#反例-91-在async中阻塞)
    - [反例 9.2 (忘记Pin)](#反例-92-忘记pin)
    - [反例 9.3 (递归async)](#反例-93-递归async)
    - [反例 9.4 (select后使用未完成Future)](#反例-94-select后使用未完成future)
  - [参考文献](#参考文献)

---

## 1. 引言

Future和Stream是Rust异步编程的核心抽象:

- **Future**: 代表单一的异步计算结果
- **Stream**: 代表一系列异步产生的值
- **async/await**: 语法糖简化异步代码编写

---

## 2. Future trait形式化

### 2.1 类型定义

### 定义 2.1 (Future trait)

```rust
trait Future {
    type Output;

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}

enum Poll<T> {
    Ready(T),
    Pending,
}
```

**形式化**:

$$
\text{Future}\langle \text{Output} = T \rangle = \text{poll}: \text{Pin}\langle \&mut \text{Self} \rangle \times \text{Context} \rightarrow \text{Poll}\langle T \rangle
$$

### 2.2 Poll语义

### 定理 2.1 (Poll契约)

> Future的poll必须满足以下契约:

1. **快速返回**: poll应快速返回，不做阻塞操作
2. **幂等性**: 返回Ready后，后续poll应返回Ready(或panic)
3. **上下文使用**: 如果返回Pending，必须注册waker

**形式化**:

$$
\begin{aligned}
\text{poll}(f, cx) &= \text{Ready}(v) \Rightarrow \forall cx'. \text{poll}(f, cx') = \text{Ready}(v) \\
\text{poll}(f, cx) &= \text{Pending} \Rightarrow \text{waker\_registered}(f, cx)
\end{aligned}
$$

∎

### 2.3 与Monad的关系

### 定理 2.2 (Future是Monad)

> Future实现了类似Monad的结构:

```rust
// return/pure: 将值包装为立即完成的Future
fn ready<T>(val: T) -> impl Future<Output = T>;

// bind/and_then: 顺序组合
fn and_then<Fut, F>(self, f: F) -> impl Future
where
    F: FnOnce(Self::Output) -> Fut,
    Fut: Future;
```

**Monad定律** (近似):

1. **Left Identity**: `ready(x).and_then(f)` ≈ `f(x)`
2. **Right Identity**: `fut.and_then(ready)` ≈ `fut`
3. **Associativity**: `(fut.and_then(f)).and_then(g)` ≈ `fut.and_then(|x| f(x).and_then(g))`

∎

---

## 3. Context与Waker

### 3.1 唤醒机制

### 定义 3.1 (Waker)

```rust
pub struct Waker {
    inner: RawWaker,
}

impl Waker {
    pub fn wake(self);
    pub fn wake_by_ref(&self);
}
```

### 定理 3.1 (唤醒保证)

> 调用waker.wake()保证关联的任务会被调度执行。

**流程**:

```text
Task (Blocked)
    │
    │ poll() returns Pending
    │
    ▼
Registers waker with resource
    │
    │ Resource becomes ready
    ▼
waker.wake() called
    │
    ▼
Task added to executor queue
    │
    ▼
Task scheduled
```

∎

### 3.2 Waker内存安全

### 定理 3.2 (Waker线程安全)

> Waker是Send + Sync，可跨线程唤醒。

**证明**:

```rust
impl Send for Waker {}
impl Sync for Waker {}
```

**实现**:

```rust
pub fn wake_by_ref(&self) {
    // 原子操作，线程安全
    unsafe { (self.vtable.wake)(self.data) }
}
```

∎

---

## 4. Stream trait

### 4.1 异步迭代

### 定义 4.1 (Stream trait)

```rust
trait Stream {
    type Item;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>>;
}
```

**与Iterator对比**:

| 特性 | Iterator | Stream |
|------|----------|--------|
| 同步性 | 同步 | 异步 |
| 返回 | `Option<Self::Item>` | `Poll<Option<Self::Item>>` |
| 阻塞 | 可能阻塞 | 非阻塞，返回Pending |

### 4.2 与Future的关系

### 定理 4.1 (Stream的累积是Future)

> 将Stream收集为集合是一个Future。

**实现**:

```rust
async fn collect<S: Stream>(stream: S) -> Vec<S::Item> {
    let mut items = Vec::new();
    while let Some(item) = stream.next().await {
        items.push(item);
    }
    items
}
```

**类型**:

$$
\text{collect}: \text{Stream}\langle T \rangle \rightarrow \text{Future}\langle \text{Vec}\langle T \rangle \rangle
$$

∎

---

## 5. async/await语法糖

### 5.1 状态机转换

### 定理 5.1 (async fn状态机)

> 每个async fn被编译为状态机。

**示例转换**:

```rust
// 源码
async fn example() -> i32 {
    let x = async_op1().await;
    let y = async_op2().await;
    x + y
}

// 展开后 (简化)
enum ExampleFuture {
    Start,
    Waiting1(/* saved state */),
    Waiting2(/* saved state */),
    Done,
}

impl Future for ExampleFuture {
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<i32> {
        loop {
            match *self {
                Start => {
                    let fut = async_op1();
                    *self = Waiting1(fut);
                }
                Waiting1(ref mut fut) => {
                    match fut.poll(cx) {
                        Ready(x) => {
                            let fut = async_op2();
                            *self = Waiting2(fut, x);
                        }
                        Pending => return Pending,
                    }
                }
                Waiting2(ref mut fut, x) => {
                    match fut.poll(cx) {
                        Ready(y) => {
                            *self = Done;
                            return Ready(x + y);
                        }
                        Pending => return Pending,
                    }
                }
                Done => panic!("polled after completion"),
            }
        }
    }
}
```

∎

### 5.2 Pin与自引用

### 定理 5.2 (async fn自动Pin)

> 生成的Future自动处理Pin约束。

**原因**:

```rust
async fn self_ref() {
    let local = String::from("hello");
    let ref_to_local = &local;  // 借用!

    some_async_op().await;  // 可能挂起

    // ref_to_local 必须仍然有效
    println!("{}", ref_to_local);
}
```

生成的状态机包含自引用，因此:

- 实现了 `!Unpin`
- poll需要 `Pin<&mut Self>`

∎

---

## 6. 执行器(Executor)模型

### 6.1 任务调度

### 定义 6.1 (Executor)

```rust
trait Executor {
    fn spawn(&self, future: impl Future);
}
```

### 定理 6.1 (任务生命周期)

```text
Created ──► Spawned ──► Running ──► Completed
                              ──► Cancelled
                              ──► Panicked
```

**状态转换**:

- Spawned: 加入任务队列
- Running: 执行器poll Future
- Completed: Future返回Ready
- Cancelled: 被显式取消
- Panicked: Future panic

∎

### 6.2 工作窃取

### 定理 6.2 (Tokio工作窃取)

> Tokio使用工作窃取调度任务。

**算法**:

```rust
// 每个线程有自己的队列
thread_local! {
    static LOCAL_QUEUE: Queue<Task>;
}

fn spawn(task: Task) {
    LOCAL_QUEUE.with(|q| q.push(task));
}

fn run() {
    loop {
        // 1. 尝试本地队列
        if let Some(task) = local_queue.pop() {
            task.poll();
            continue;
        }

        // 2. 尝试窃取其他线程
        if let Some(task) = steal_from_other() {
            task.poll();
            continue;
        }

        // 3. 阻塞等待
        park();
    }
}
```

∎

---

## 7. 组合子分析

### 7.1 then与map

### 定理 7.1 (Future组合)

```rust
// map: 转换结果
fn map<F, T>(self, f: F) -> Map<Self, F>
where F: FnOnce(Self::Output) -> T;

// then: 顺序组合
fn then<Fut, F>(self, f: F) -> Then<Self, F>
where F: FnOnce(Self::Output) -> Fut,
      Fut: Future;
```

**类型签名**:

$$
\begin{aligned}
\text{map} &: \text{Future}\langle A \rangle \times (A \rightarrow B) \rightarrow \text{Future}\langle B \rangle \\
\text{then} &: \text{Future}\langle A \rangle \times (A \rightarrow \text{Future}\langle B \rangle) \rightarrow \text{Future}\langle B \rangle
\end{aligned}
$$

∎

### 7.2 join与select

### 定理 7.2 (并发组合)

```rust
// join: 等待所有完成
async fn join<A, B>(a: A, b: B) -> (A::Output, B::Output);

// select: 等待任一完成
async fn select<A, B>(a: A, b: B) -> Either<A::Output, B::Output>;
```

**语义**:

- `join(a, b)`: 两者都完成
- `select(a, b)`: 任一完成，另一个可能被取消

∎

---

## 8. 内存安全

### 8.1 取消安全

### 定理 8.1 (取消安全定义)

> Future在poll返回Ready前停止执行是内存安全的。

**条件**:

- 不留下不一致状态
- 资源正确释放(Drop)

**示例**:

```rust
// 取消安全: 使用 RAII
async fn safe_operation() {
    let guard = acquire_resource();
    // ... await点 ...
    // guard 在drop时释放资源，即使取消
}

// 不安全: 手动管理
async fn unsafe_operation() {
    let ptr = allocate();
    // ... await点 ...
    // 如果在这里取消，内存泄漏!
    deallocate(ptr);
}
```

∎

### 8.2 泄漏安全

### 定理 8.2 (异步泄漏)

> 即使Future被泄漏(永不poll)，也不会违反内存安全。

**原因**:

- Future本身遵循所有权规则
- 不poll意味着不执行，也就不会产生不一致状态
- 但可能导致资源泄漏(不是内存安全问题)

∎

---

## 9. 反例与陷阱

### 反例 9.1 (在async中阻塞)

```rust
async fn bad() {
    std::thread::sleep(Duration::from_secs(1));  // 阻塞!
}

// 正确
async fn good() {
    tokio::time::sleep(Duration::from_secs(1)).await;
}
```

### 反例 9.2 (忘记Pin)

```rust
async fn bad(mut self_ref: SelfRef) {
    self_ref.setup();  // 创建自引用
    // 移动!
    some_async_op().await;
}

// 正确
async fn good(mut self_ref: Pin<Box<SelfRef>>) {
    // Pin保证不移动
}
```

### 反例 9.3 (递归async)

```rust
async fn recursive(n: usize) {
    if n > 0 {
        recursive(n - 1).await;  // 无限类型!
    }
}

// 正确: 使用Box::pin
async fn recursive(n: usize) {
    if n > 0 {
        Box::pin(recursive(n - 1)).await;
    }
}
```

### 反例 9.4 (select后使用未完成Future)

```rust
let a = slow_op();
let b = fast_op();

match select(a, b).await {
    Either::Left((result, unfinished_b)) => {
        // unfinished_b 可能已内部改变
        // 再次poll可能导致未定义行为
    }
}
```

---

## 参考文献

1. **Rust Standard Library.** (2024). `std::future::Future`. <https://doc.rust-lang.org/std/future/trait.Future.html>

2. **Rust Async Book.** (2024). *Asynchronous Programming in Rust*. <https://rust-lang.github.io/async-book/>

3. **Tokio Documentation.** (2024). *Tokio Runtime*. <https://docs.rs/tokio/>

---

*文档版本: 1.0.0*
*形式化深度: 高*
*定理数量: 12个*
*最后更新: 2026-03-04*
