# Futures 库形式化分析

> **主题**: 异步编程原语
>
> **形式化框架**: Future组合子 + 执行语义
>
> **参考**: futures crate Documentation

---

## 目录

- [Futures 库形式化分析](#futures-库形式化分析)
  - [目录](#目录)
  - [1. 引言](#1-引言)
  - [2. Future组合子](#2-future组合子)
    - [2.1 Then组合](#21-then组合)
    - [定理 2.1 (顺序组合)](#定理-21-顺序组合)
    - [2.2 Select组合](#22-select组合)
    - [定理 2.2 (竞争选择)](#定理-22-竞争选择)
  - [3. Stream处理](#3-stream处理)
    - [定义 3.1 (Stream Trait)](#定义-31-stream-trait)
    - [定理 3.1 (流组合)](#定理-31-流组合)
  - [4. Sink抽象](#4-sink抽象)
    - [定义 4.1 (Sink Trait)](#定义-41-sink-trait)
    - [定理 4.1 (背压支持)](#定理-41-背压支持)
  - [5. 并发原语](#5-并发原语)
    - [定理 5.1 (Join并发)](#定理-51-join并发)
  - [6. 反例](#6-反例)
    - [反例 6.1 (忘记poll)](#反例-61-忘记poll)
    - [反例 6.2 (Select取消)](#反例-62-select取消)

---

## 1. 引言

futures crate提供:

- Future组合子
- Stream处理
- Sink抽象
- 并发控制

---

## 2. Future组合子

### 2.1 Then组合

### 定理 2.1 (顺序组合)

> `then`创建顺序执行的Future链。

```rust
future_a.then(|result_a| async move {
    future_b(result_a).await
})
```

**语义**:

$$
\text{then}(F_1, F_2) = \lambda ctx. \begin{cases}
\text{Pending} & F_1(ctx) = \text{Pending} \\
F_2(v) & F_1(ctx) = \text{Ready}(v)
\end{cases}
$$

∎

### 2.2 Select组合

### 定理 2.2 (竞争选择)

> `select`等待多个Future，返回先完成的。

```rust
select! {
    a = future_a => { /* a完成 */ },
    b = future_b => { /* b完成 */ },
}
```

**公平性**: 伪随机选择，避免饥饿

∎

---

## 3. Stream处理

### 定义 3.1 (Stream Trait)

```rust
pub trait Stream {
    type Item;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>)
        -> Poll<Option<Self::Item>>;
}
```

### 定理 3.1 (流组合)

> Stream支持map、filter、fold等操作。

```rust
stream
    .map(|x| x * 2)
    .filter(|x| *x > 10)
    .take(5)
```

**性质**:

- 惰性求值
- 组合子链
- 取消安全

∎

---

## 4. Sink抽象

### 定义 4.1 (Sink Trait)

```rust
pub trait Sink<Item> {
    type Error;

    fn poll_ready(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>>;
    fn start_send(&mut self, item: Item) -> Result<(), Self::Error>;
    fn poll_flush(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>>;
    fn poll_close(&mut self, cx: &mut Context<'_>) -> Poll<Result<(), Self::Error>>;
}
```

### 定理 4.1 (背压支持)

> Sink通过`poll_ready`实现背压。

**协议**:

1. `poll_ready` → Ready表示可发送
2. `start_send` 发送数据
3. `poll_flush` 等待发送完成

∎

---

## 5. 并发原语

### 定理 5.1 (Join并发)

> `join!`同时执行多个Future。

```rust
let (a, b) = join!(future_a, future_b);
```

**时间复杂度**:

$$
T_{join} = \max(T_a, T_b)
$$

vs顺序执行的

$$
T_{seq} = T_a + T_b
$$

∎

---

## 6. 反例

### 反例 6.1 (忘记poll)

```rust
// 错误: 手动实现Future但忘记wake
impl Future for MyFuture {
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        if self.is_ready() {
            Poll::Ready(())
        } else {
            Poll::Pending  // 忘记调用cx.waker().wake()!
        }
    }
}
```

### 反例 6.2 (Select取消)

```rust
select! {
    a = async {
        resource.lock().await;  // 获取锁
        work().await;           // 可能取消，锁未释放!
    } => {},
    b = other_work() => {},
}

// 正确: 使用tokio::select!的取消安全版本
// 或使用作用域保护
```

---

*文档版本: 1.0.0*
*定理数量: 6个*
