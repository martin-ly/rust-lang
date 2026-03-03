# Async/Await 形式语义补充

> 本文档补充异步编程的形式化语义，包括Future状态机、生成器转换和跨await借用分析

---

## 目录

- [Async/Await 形式语义补充](#asyncawait-形式语义补充)
  - [目录](#目录)
  - [1. Future Trait 形式定义](#1-future-trait-形式定义)
    - [1.1 Future类型定义](#11-future类型定义)
    - [1.2 Poll结果类型](#12-poll结果类型)
  - [2. 异步函数状态机转换](#2-异步函数状态机转换)
    - [2.1 async fn 到状态机的转换](#21-async-fn-到状态机的转换)
    - [2.2 状态机形式语义](#22-状态机形式语义)
  - [3. 跨Await点借用分析](#3-跨await点借用分析)
    - [3.1 问题陈述](#31-问题陈述)
    - [3.2 生命周期边界规则](#32-生命周期边界规则)
    - [3.3 状态机捕获分析](#33-状态机捕获分析)
    - [3.4 自引用与Pin](#34-自引用与pin)
  - [4. Send与Sync对异步的影响](#4-send与sync对异步的影响)
    - [4.1 异步Send边界](#41-异步send边界)
    - [4.2 跨.await点持有Send/Sync](#42-跨await点持有sendsync)
  - [5. 异步借用检查器扩展](#5-异步借用检查器扩展)
    - [5.1 生成器状态分析](#51-生成器状态分析)
    - [5.2 借用检查扩展规则](#52-借用检查扩展规则)
  - [6. 异步形式化示例](#6-异步形式化示例)
    - [6.1 状态机展开示例](#61-状态机展开示例)
    - [6.2 借用冲突示例分析](#62-借用冲突示例分析)
  - [7. 异步与并发的交互](#7-异步与并发的交互)
    - [7.1 async/await与多线程](#71-asyncawait与多线程)
    - [7.2 异步同步原语](#72-异步同步原语)
  - [参考文献](#参考文献)

## 1. Future Trait 形式定义

### 1.1 Future类型定义

```rust
trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

**形式化定义**：

$$
\text{Future}\langle T \rangle \triangleq \mu F. \text{Pin}\langle \&mut \, F \rangle \times \text{Context} \to \text{Poll}\langle T \rangle
$$

其中：

- $\mu F$ 表示递归类型（状态机可以自引用）
- $\text{Poll}\langle T \rangle \triangleq \text{Pending} \mid \text{Ready}(T)$

### 1.2 Poll结果类型

$$
\text{Poll}\langle T \rangle ::= \text{Pending} \mid \text{Ready}(v: T)
$$

**语义**：

- `Pending`：异步计算尚未完成，需要等待
- `Ready(v)`：异步计算完成，返回结果 $v$

---

## 2. 异步函数状态机转换

### 2.1 async fn 到状态机的转换

**转换规则**：

```rust
async fn foo() -> T { body }
```

转换为状态机：

```rust
enum FooStateMachine {
    Start,
    State1 { /* 捕获的变量 */ },
    State2 { /* 捕获的变量 */ },
    Done,
}

impl Future for FooStateMachine {
    type Output = T;
    fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<T> {
        loop {
            match *self {
                Start => { /* 执行到第一个await */ }
                State1 { ... } => { /* 执行到第二个await */ }
                // ...
            }
        }
    }
}
```

### 2.2 状态机形式语义

**状态机配置**：$\langle s, \sigma, \kappa \rangle$

- $s \in \text{State}$：当前状态
- $\sigma$：变量环境（捕获的状态）
- $\kappa$：继续点（continuation）

**状态转换规则**：

$$
\frac{\text{state}(s) = \text{await}(e, s_{\text{next}}) \quad \text{poll}(e) = \text{Pending}}{\langle s, \sigma, \kappa \rangle \to \langle s_{\text{suspend}}, \sigma, \kappa \rangle} \quad \text{[ASYNC-AWAIT-PENDING]}
$$

$$
\frac{\text{state}(s) = \text{await}(e, s_{\text{next}}) \quad \text{poll}(e) = \text{Ready}(v)}{\langle s, \sigma, \kappa \rangle \to \langle s_{\text{next}}, \sigma[x \mapsto v], \kappa \rangle} \quad \text{[ASYNC-AWAIT-READY]}
$$

---

## 3. 跨Await点借用分析

### 3.1 问题陈述

**关键问题**：当异步函数挂起（await）时，局部变量的借用是否仍然有效？

```rust
async fn example() {
    let data = vec![1, 2, 3];
    let ref = &data[0];  // 借用

    some_async_op().await;  // 挂起点

    println!("{}", ref);  // 挂起后使用借用？
}
```

### 3.2 生命周期边界规则

**形式化规则**：

对于在await点之前创建的借用 `r = &x`：

$$
\text{lifetime}(r) \subseteq \text{until\_next\_await}
$$

即借用的生命周期不能超过下一个await点，除非：

1. 被借用的值在状态机中（被捕获）
2. 借用本身也被捕获

### 3.3 状态机捕获分析

**捕获规则**：

```rust
async fn foo() {
    let x = String::new();
    let r = &x;  // 错误！
    bar().await;
    use(r);
}
```

**错误原因**：

- `r` 引用 `x`，但 `x` 在栈上
- 当挂起时，栈帧被保存到状态机
- 但 `r` 指向的是原栈位置，不是状态机中的副本

**正确模式**：

```rust
async fn foo() {
    let x = String::new();
    bar().await;
    let r = &x;  // 在await之后借用
    use(r);
}
```

### 3.4 自引用与Pin

**形式化定理（异步自引用）**：

异步状态机可能包含自引用结构：

$$
\exists \text{state\_machine}. \text{self\_referential}(\text{state\_machine})
$$

**Pin的必要性**：

```rust
async fn self_referential_example() {
    let mut x = [1, 2, 3];
    let ptr = &mut x[0] as *mut i32;  // 指向局部数组

    yield_now().await;  // 挂起

    unsafe { *ptr = 42; }  // 挂起后解引用
}  // x在这里drop
```

**形式化解释**：

- 状态机包含字段 `x: [i32; 3]` 和 `ptr: *mut i32`
- `ptr` 指向 `x` 的内部
- 移动状态机 → `ptr` 悬垂
- `Pin<Box<dyn Future>>` 防止移动

---

## 4. Send与Sync对异步的影响

### 4.1 异步Send边界

**定理（Future Send条件）**：

$$
\text{Future}: \text{Send} \Leftrightarrow \forall \text{捕获变量 } v. v: \text{Send}
$$

**跨线程Spawn要求**：

```rust
tokio::spawn(async { ... });  // 要求 Future: Send
```

**反例**：

```rust
let rc = Rc::new(42);
tokio::spawn(async move {
    println!("{}", *rc);  // 错误！Rc<!Send>
});
```

### 4.2 跨.await点持有Send/Sync

**关键规则**：

```rust
async fn hold_across_await() {
    let mutex = Mutex::new(42);
    let guard = mutex.lock().await;  // 获取锁

    some_async_op().await;  // 跨越await持有guard！

    drop(guard);  // 在其他线程可能执行时释放
}
```

**形式化分析**：

- `MutexGuard` 在挂起时仍被持有
- 当Future在另一线程恢复时，`drop(guard)` 在另一线程执行
- 这要求 `MutexGuard: Send` 才能安全

---

## 5. 异步借用检查器扩展

### 5.1 生成器状态分析

**生成器状态转换**：

```
状态 0: 初始
  └─► 执行到第一个await
  └─► 状态 1: 保存变量，挂起
        └─► 恢复执行
        └─► 执行到第二个await
        └─► 状态 2: 保存变量，挂起
              └─► ...
```

### 5.2 借用检查扩展规则

**规则 AWAIT-BORROW**：

$$
\frac{\Gamma \vdash \text{await}(e) : T \quad \text{live\_vars}(\Gamma) = \{x_1, \ldots, x_n\}}{\forall r \in \text{borrows}(\Gamma). \text{lifetime}(r) \subseteq \text{current\_suspend\_point}}
$$

**约束**：所有活跃借用的生命周期必须在await点结束。

---

## 6. 异步形式化示例

### 6.1 状态机展开示例

```rust
async fn example(x: i32) -> i32 {
    let y = x + 1;
    let z = async { y * 2 }.await;
    z + 1
}
```

**展开后的状态机**：

```rust
enum ExampleState {
    Start(i32),           // 初始状态，捕获参数x
    State1 { y: i32 },    // 执行let y = x + 1后
    State2 { z: i32 },    // await完成后，捕获z
    Done,
}

impl Future for ExampleState {
    type Output = i32;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<i32> {
        match *self {
            Start(x) => {
                let y = x + 1;
                *self = State1 { y };
                self.poll(cx)  // 继续执行
            }
            State1 { y } => {
                // 创建子Future
                let fut = async { y * 2 };
                // poll子Future...
                match fut.poll(cx) {
                    Ready(z) => {
                        *self = State2 { z };
                        self.poll(cx)
                    }
                    Pending => Poll::Pending,
                }
            }
            State2 { z } => {
                let result = z + 1;
                *self = Done;
                Ready(result)
            }
            Done => panic!("poll after completion"),
        }
    }
}
```

### 6.2 借用冲突示例分析

```rust
async fn conflict_example() {
    let mut data = vec![1, 2, 3];
    let r1 = &mut data[0];
    let r2 = &mut data[1];  // 编译错误！

    some_op().await;

    println!("{}, {}", r1, r2);
}
```

**错误原因形式化**：

- `r1 = &mut data[0]` 创建可变借用 $\text{borrow}(\text{data}, \text{mut}, t_1)$
- `r2 = &mut data[1]` 尝试创建第二个可变借用
- 虽然索引不同，但借用检查器保守地认为可能冲突
- 在.await点后，可能恢复于不同线程，需要 `Send` 保证

---

## 7. 异步与并发的交互

### 7.1 async/await与多线程

**形式化模型**：

```
单线程执行器:
  Future轮询在一个线程上顺序执行
  无数据竞争（单线程）

多线程执行器 (如tokio::spawn_multi_threaded):
  Future可以在不同线程上轮询
  需要 Future: Send
  需要捕获变量: Send
```

### 7.2 异步同步原语

**Mutex在异步中的语义**：

```rust
pub struct Mutex<T> {
    inner: std::sync::Mutex<T>,
}

impl<T> Mutex<T> {
    pub async fn lock(&self) -> MutexGuard<'_, T> {
        // 异步等待锁可用
        // 等待期间让出控制权
    }
}
```

**与传统Mutex的区别**：

- 异步Mutex：等待时yield，不阻塞线程
- 传统Mutex：等待时阻塞线程

---

## 参考文献

1. Rust Async Working Group. (2024). Asynchronous Programming in Rust.
2. Tokio Project. (2024). Tokio Runtime and Async I/O.
3. Swift, J. (2020). Understanding Rust Futures by implementing an async executor.
4. Rust Compiler Team. (2024). Generator Internals.

---

*本文档为《Rust所有权与可判定性》项目的异步形式语义补充*
