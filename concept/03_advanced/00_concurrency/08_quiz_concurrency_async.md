> **内容分级**: [专家级]

# 测验：并发与异步（L3 试点扩展）
>
> **EN**: Concurrency
> **Summary**: Concurrency — An interactive quiz checking L3 concurrency (Send/Sync, Mutex/Arc, channels) and async (Future, Pin, await).
> **受众**: [专家]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` 权威页。
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链
> **后置概念**: N/A
---

> **来源**: · [Herlihy & Shavit — The Art of Multiprocessor Programming](https://dl.acm.org/doi/10.5555/2385452) · [Batty et al. — The Semantics of Multicore C](https://doi.org/10.1145/2049706.2049711) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [The Rust Programming Language — Ch16 Fearless Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html) ·
> [The Rust Programming Language — Ch17 Async/Await](https://doc.rust-lang.org/book/ch17-00-async-await.html) ·
> [Rust Atomics and Locks](https://marabos.nl/atomics/)
>
> **前置概念**:
> [Concurrency](01_concurrency.md) ·
> [Async/Await](../01_async/01_async.md) ·
> [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) ·
> [Iterator Patterns](../../02_intermediate/07_iterators_and_closures/01_iterator_patterns.md)
>
> **对应练习**:
> [`exercises/src/concurrency/`](../../exercises/src/concurrency) ·
> [`exercises/src/async_programming/`](../../exercises/src/async_programming)

---

> **Bloom 层级**: L4-L5
> **难度图例**: 🟢 基础（概念直接考察）｜ 🟡 进阶（需理解深层原理）｜ 🔴 专家（多概念综合 / 边界情况）
> **题型构成**: 代码阅读题（能否编译 / 输出分析，本测验特色）+ 规范题型【单选】【多选】【判断】（按 mdbook-quiz 指南四级题型规范（`docs/02_learning/07_mdbook_quiz_guide.md`） 的 .md 落地形态组织，不引入 TOML 插件）
> **定位**: L3 嵌入式互动测验——验证并发模型（Send/Sync、Mutex/Arc、channel）与异步（Async）编程（Future、Pin、await）核心概念的掌握程度。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、并发基础：Send 与 Sync

「并发基础：Send 与 Sync」部分按 Q1. 以下代码能否编译？解释 `Send` 和 `Sync` 的语义、Q2. 以下代码的输出是什么？存在什么问题？与Q3. 以下代码的输出是什么？解释 `mpsc` channel 的语义的顺序逐层展开。

### Q1. 🟡 以下代码能否编译？解释 `Send` 和 `Sync` 的语义

```rust,compile_fail
use std::rc::Rc;
use std::thread;

fn main() {
    let data = Rc::new(42);
    let handle = thread::spawn(move || {
        println!("{}", *data);
    });
    handle.join().unwrap();
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`Rc<i32> cannot be sent between threads safely`

**解析**：`Rc<T>` 是**单线程引用（Reference）计数**，未实现 `Send` trait，不能跨线程移动。

**解决方案**——使用 `Arc<T>`（Atomic Reference Counted）：

```rust
use std::sync::Arc;
use std::thread;

fn main() {
    let data = Arc::new(42);
    let data2 = Arc::clone(&data);
    let handle = thread::spawn(move || {
        println!("{}", *data2);
    });
    handle.join().unwrap();
}
```

**`Send` vs `Sync`**：

| Trait | 语义 | 实现条件 |
|:---|:---|:---|
| `Send` | 类型可以**跨线程转移所有权（Ownership）** | `T` 的所有权可以安全转移到另一个线程 |
| `Sync` | 类型可以**跨线程共享引用（Reference）**（`&T` 是 `Send`） | `T` 的内部状态访问是线程安全的 |

**组合**：

| 类型 | `Send` | `Sync` | 说明 |
|:---|:---:|:---:|:---|
| `Rc<T>` | ❌ | ❌ | 非原子引用（Reference）计数 |
| `Arc<T>` | ✅（若 `T: Send + Sync`） | ✅（若 `T: Send + Sync`） | 原子引用（Reference）计数 |
| `Mutex<T>` | ✅（若 `T: Send`） | ✅（若 `T: Send`） | 互斥锁保护 |
| `Cell<T>` | ✅ | ❌ | 内部可变性，非同步 |
| `RefCell<T>` | ✅ | ❌ | 运行时（Runtime）借用（Borrowing）检查，非同步 |

**知识点**：`Send` 和 `Sync` 是 Rust 并发安全（Concurrency Safety）的编译期保证。编译器自动为大多数类型推导实现，但 `unsafe impl` 可用于自定义类型。[→ 并发模型详解](01_concurrency.md)

</details>

---

### Q2. 🟡 以下代码的输出是什么？存在什么问题？

```rust
use std::thread;

fn main() {
    let mut handles = vec![];
    let mut counter = 0;

    for _ in 0..10 {
        let handle = thread::spawn(move || {
            counter += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Counter: {counter}");
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`cannot borrow`counter`as mutable more than once at a time`

**解析**：闭包（Closures）通过 `move` 捕获了 `counter`，但 `counter` 被多个闭包同时 `move`，违反了所有权（Ownership）规则。

**核心问题**：多个线程需要**共享可变状态**。

**解决方案**——`Arc<Mutex<T>>`：

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }

    for handle in handles {
        handle.join().unwrap();
    }

    println!("Counter: {}", *counter.lock().unwrap());
}
```

**知识点**：`Arc` 提供共享所有权（Ownership），`Mutex` 提供互斥访问。组合是 Rust 中多线程共享可变状态的标准模式。[→ 并发模式详解](03_concurrency_patterns.md)

</details>

---

### Q3. 🟡 以下代码的输出是什么？解释 `mpsc` channel 的语义

```rust
use std::sync::mpsc;
use std::thread;

fn main() {
    let (tx, rx) = mpsc::channel();

    thread::spawn(move || {
        tx.send(1).unwrap();
        tx.send(2).unwrap();
        tx.send(3).unwrap();
    });

    for received in rx {
        println!("Got: {received}");
    }
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

```
Got: 1
Got: 2
Got: 3
```

**解析**：`mpsc` = **Multi-Producer Single-Consumer**（多生产者单消费者）。

- `tx`（transmitter）可克隆，多个线程可发送
- `rx`（receiver）不能克隆，只有一个消费者
- `rx` 作为迭代器（Iterator）使用时，当所有 `tx` 被 drop，迭代自动结束

**对比**：

| Channel 类型 | 生产者 | 消费者 | 容量 | 用途 |
|:---|:---:|:---:|:---:|:---|
| `mpsc::channel()` | 多 | 单 | 无界 | 一般消息传递 |
| `mpsc::sync_channel(n)` | 多 | 单 | 有界（n） | 背压控制 |
| `crossbeam::channel` | 多 | 多 | 有界/无界 | 更强大的生态替代 |

**知识点**：Channel 是 Rust 中"消息传递"并发模型的核心工具，与"共享状态"模型互补。[→ 并发模型详解](01_concurrency.md)

</details>

---

## 二、异步编程

本节从 Q4. 以下代码的输出是什么？解释 `.await` 的作用、Q5. 以下代码能否编译？解释 `Pin` 的作用与Q6. 以下代码存在什么问题？如何修复？切入，剖析「异步编程」的核心内容。

### Q4. 🟢 以下代码的输出是什么？解释 `.await` 的作用

```rust
async fn say_hello() {
    println!("Hello");
}

#[tokio::main]
async fn main() {
    let future = say_hello();
    println!("Before await");
    future.await;
    println!("After await");
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

```
Before await
Hello
After await
```

**解析**：

- `async fn` 不立即执行，而是返回一个 **Future**
- `let future = say_hello();` 只创建 Future，**不执行函数体**
- `.await` 才是执行点：驱动 Future 到完成

**关键点**：

```rust,ignore
let future = say_hello(); // 创建 Future，零成本
// ... 此时可以进行其他工作 ...
future.await;             // 执行异步操作，可能让出线程
```

**Future 状态机**：编译器将 `async fn` 转换为状态机，`.await` 处为状态切换点。

**知识点**：Rust 的 async/await 是**零成本抽象（Zero-Cost Abstraction）**——没有运行时（Runtime）分配，状态机在栈上展开。→ Async/Await 详解

</details>

---

### Q5. 🔴 以下代码能否编译？解释 `Pin` 的作用

```rust
use std::pin::Pin;
use std::future::Future;
use std::task::{Context, Poll};

struct MyFuture {
    data: String,
}

impl Future for MyFuture {
    type Output = String;
    fn poll(self: Pin<&mut Self>, _cx: &mut Context<'_>) -> Poll<Self::Output> {
        Poll::Ready(self.data.clone())
    }
}

fn main() {
    let fut = MyFuture { data: String::from("hello") };
    // fut.await; // 假设在 async 上下文中
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译（但 `main` 中 `.await` 需要 `async` 上下文）

**解析**：`Pin<&mut Self>` 是 Rust 异步（Async）的核心保证。

**为什么需要 `Pin`**：

`async fn` 编译后的状态机可能包含**自引用（Reference）**（例如一个字段是指向另一个字段的引用）：

```rust,ignore
async fn example() {
    let data = [1, 2, 3];
    let ptr = &data[0]; // ptr 指向 data 内部
    some_async().await;  // 可能在此处被移动！
    println!("{}", *ptr); // 若 data 被移动，ptr 悬垂！
}
```

`Pin` 承诺：被固定的值**在内存中不会移动**，从而保证自引用（Reference）的安全性。

**规则**：

| 操作 | `Pin<&mut T>` | `T: Unpin` |
|:---|:---|:---|
| 获取 `&mut T` | ❌（除非 `T: Unpin`） | ✅ |
| 大多数类型 | 自动实现 `Unpin` | — |
| 自引用（Reference）类型（async 状态机） | `!Unpin` | 必须 `Pin` |

**知识点**：`Pin` 不是日常需要直接使用的类型，但理解其"承诺不移动"的语义对理解 async 安全性至关重要。[→ Pin/Unpin 详解](../01_async/08_pin_unpin.md)

</details>

---

### Q6. 🔴 以下代码存在什么问题？如何修复？

```rust
use tokio;

#[tokio::main]
async fn main() {
    let v = vec![1, 2, 3];
    let handle = tokio::spawn(async move {
        println!("{}", v[0]);
    });
    println!("{}", v[1]);
    handle.await.unwrap();
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`use of moved value: v`

**解析**：`async move` 闭包（Closures）通过 `move` 捕获了 `v` 的所有权（Ownership），`main` 中的 `v` 不再可用。

**解决方案**——使用 `Arc` 共享数据：

```rust
use std::sync::Arc;
use tokio;

#[tokio::main]
async fn main() {
    let v = Arc::new(vec![1, 2, 3]);
    let v2 = Arc::clone(&v);
    let handle = tokio::spawn(async move {
        println!("{}", v2[0]);
    });
    println!("{}", v[1]);
    handle.await.unwrap();
}
```

**对比线程与任务**：

| 特性 | `std::thread::spawn` | `tokio::spawn` |
|:---|:---|:---|
| 执行单元 | OS 线程 | 异步（Async）任务（协作式调度） |
| 闭包（Closures）要求 | `FnOnce + Send + 'static` | `Future + Send + 'static` |
| 内存开销 | ~1-2 MB 栈 | ~几 KB |
| 适用场景 | CPU 密集型 | IO 密集型 |

**知识点**：`tokio::spawn` 要求 Future 是 `'static`，因此不能借用（Borrowing）局部变量，必须转移所有权（Ownership）或使用 `Arc`。→ Async 模式详解

</details>

---

## 三、综合应用

理解「综合应用」需要把握 Q7. 以下代码的输出是什么？解释 `join!` 与顺序 await…、Q8. 以下代码能否编译？解释 `'static` 在并发中的含义、Q9. 以下代码的输出是什么？解释 `RwLock` 与 `Mutex…与Q10. 以下代码存在什么问题？这是 Rust 并发的经典陷阱，本节依次展开。

### Q7. 🟡 以下代码的输出是什么？解释 `join!` 与顺序 await 的区别

```rust
use tokio::time::{sleep, Duration};

async fn task1() -> i32 {
    sleep(Duration::from_millis(100)).await;
    println!("task1 done");
    1
}

async fn task2() -> i32 {
    sleep(Duration::from_millis(50)).await;
    println!("task2 done");
    2
}

#[tokio::main]
async fn main() {
    let r1 = task1().await;
    let r2 = task2().await;
    println!("Result: {}", r1 + r2);
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

```
task1 done
task2 done
Result: 3
```

**解析**：**顺序 await**——`task1().await` 完全完成后才启动 `task2()`，总耗时 ~150ms。

**并发执行**——使用 `tokio::join!`：

```rust
#[tokio::main]
async fn main() {
    let (r1, r2) = tokio::join!(task1(), task2());
    println!("Result: {}", r1 + r2);
}
```

输出变为：

```
task2 done
task1 done
Result: 3
```

总耗时 ~100ms（两者并发执行）。

**对比**：

| 方式 | 执行模式 | 适用场景 |
|:---|:---|:---|
| `a.await; b.await;` | 顺序 | 有依赖关系 |
| `tokio::join!(a, b)` | 并发，等待全部完成 | 独立任务，需全部结果 |
| `tokio::select!` | 并发，等待任一完成 | 竞争条件，超时处理 |
| `futures::future::join` | 并发（非 Tokio 专属） | 通用生态 |

**知识点**：`await` 本身不创建并发，只是暂停当前任务。真正的并发需要 `join!`、`select!` 或 `spawn`。[→ Async 模式详解](../01_async/01_async.md)

</details>

---

### Q8. 🟡 以下代码能否编译？解释 `'static` 在并发中的含义

```rust,compile_fail
use std::thread;

fn main() {
    let s = String::from("hello");
    let handle = thread::spawn(move || {
        println!("{}", s);
    });
    drop(s); // 尝试提前释放
    handle.join().unwrap();
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`use of moved value: s`

**解析**：`thread::spawn(move || ...)` 已经将 `s` 的所有权（Ownership）**移动**到新线程，`main` 中不能再使用 `s`（包括 `drop`）。

**`'static` 约束的深层含义**：

`thread::spawn` 要求闭包（Closures）满足 `'static`，即闭包捕获的数据必须：

- 拥有所有权（Ownership）（`move`），或
- 是 `'static` 生命周期（Lifetimes）（如字符串字面量 `"hello"`）

**对比**：

```rust,ignore
// ✅ 可以：字符串字面量是 'static
let s = "hello";
thread::spawn(move || { println!("{}", s); });

// ✅ 可以：Arc 共享所有权
let s = Arc::new(String::from("hello"));
let s2 = Arc::clone(&s);
thread::spawn(move || { println!("{}", s2); });

// ❌ 不可以：借用局部变量
let s = String::from("hello");
thread::spawn(|| { println!("{}", &s); });
```

**知识点**：`'static` 不等于"程序全局存活"，而是"不借用（Borrowing）任何非 `'static` 数据"。理解这一点是掌握 Rust 并发闭包（Closures）的关键。→ 生命周期（Lifetimes）详解

</details>

---

### Q9. 🟡 以下代码的输出是什么？解释 `RwLock` 与 `Mutex` 的区别

```rust
use std::sync::RwLock;

fn main() {
    let lock = RwLock::new(5);

    {
        let r1 = lock.read().unwrap();
        let r2 = lock.read().unwrap();
        println!("Read: {} {}", *r1, *r2);
    }

    {
        let mut w = lock.write().unwrap();
        *w += 1;
    }

    println!("Final: {}", *lock.read().unwrap());
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：

```
Read: 5 5
Final: 6
```

**解析**：`RwLock<T>`（读写锁）允许多个读锁或一个写锁：

| 锁类型 | 并发数 | 互斥对象 |
|:---|:---:|:---|
| `Mutex` | 1（任意访问） | 所有访问者 |
| `RwLock::read()` | 多（并发读） | 写锁 |
| `RwLock::write()` | 1（独占写） | 所有其他锁 |

**注意**：`RwLock` 的读锁可以**递归获取**（同一线程多次 `read()`），但写锁通常不能（可能死锁，取决于实现）。

**选择建议**：

| 场景 | 推荐 |
|:---|:---|
| 读多写少 | `RwLock` |
| 读写均衡或写多 | `Mutex`（更简单，某些实现更快） |
| 高并发读 | `crossbeam` 的 lock-free 结构 |

**知识点**：`RwLock` 适合读多写少的场景，但实现复杂度和平台差异较大。`Mutex` 是更保守、更通用的选择。[→ 并发模式详解](03_concurrency_patterns.md)

</details>

---

### Q10. 🔴 以下代码存在什么问题？这是 Rust 并发的经典陷阱

```rust,compile_fail
use std::sync::Mutex;

fn main() {
    let counter = Mutex::new(0);

    for _ in 0..10 {
        std::thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
    }

    println!("Result: {}", *counter.lock().unwrap());
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`counter` moved into closure in previous iteration of loop`

**解析**：`counter` 在第一次迭代时被 `move` 进闭包（Closures），后续迭代无法再次使用。

**修复方案**——使用 `Arc<Mutex<T>>`：

```rust
use std::sync::{Arc, Mutex};

fn main() {
    let counter = Arc::new(Mutex::new(0));
    let mut handles = vec![];

    for _ in 0..10 {
        let counter = Arc::clone(&counter);
        let handle = std::thread::spawn(move || {
            let mut num = counter.lock().unwrap();
            *num += 1;
        });
        handles.push(handle);
    }

    for h in handles {
        h.join().unwrap();
    }

    println!("Result: {}", *counter.lock().unwrap());
}
```

**另一个陷阱**——若不 `join`，可能打印时子线程尚未完成：

```rust,ignore
// 错误：可能输出 "Result: 0" 到 "Result: 10" 之间的任意值
println!("Result: {}", *counter.lock().unwrap());
```

**知识点**：`Arc<Mutex<T>>` 是 Rust 多线程共享可变状态的**三板斧**——原子引用（Reference）计数 + 互斥锁 + 显式 join 同步。[→ 并发模式详解](03_concurrency_patterns.md)

</details>

---

## 四、规范题型补充：单选 · 多选 · 判断

> 本节按四级题型规范补充单选、多选与判断题，知识点与
> [Concurrency](01_concurrency.md)、[Async/Await](../01_async/01_async.md) 权威页一致；
> 干扰项针对常见误解设计。

### Q11. 🟡【单选】marker trait `Send` 的准确含义是？

- A. 类型的引用可以被多个线程同时持有
- B. 类型的**所有权**可以安全地从一个线程转移到另一个线程
- C. 类型实现了 `Clone`
- D. 类型是 `'static` 的

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：`Send` = 可跨线程**转移所有权**（如 move 进 `thread::spawn`）。A 描述的是 `Sync`（`&T` 可跨线程共享）——`T: Sync ⟺ &T: Send`，两者混淆是最常见错误。C、D 与线程安全无关：是否可复制、是否含非静态引用是另外两个独立维度（`'static` 只是 `thread::spawn` 的常见约束，非 `Send` 的定义）。

</details>

---

### Q12. 🟡【单选】`Arc<Mutex<T>>` 与 `Rc<RefCell<T>>` 的本质区别是？

- A. 前者用于单线程，后者用于多线程
- B. 前者线程安全（原子引用计数 + 阻塞锁），后者仅限单线程（非原子计数 + 运行时借用检查）
- C. 两者性能完全相同
- D. 后者更安全，应总是优先使用

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：两对组合是同一模式（共享所有权 + 内部可变性）在"单线程 / 多线程"两个世界的对应物。`Rc`/`RefCell` 零原子操作、无锁，更快但 `!Send`；`Arc`/`Mutex` 付出原子指令与锁开销换取跨线程能力。选型规则：不跨线程就用 `Rc<RefCell<T>>`（D 错——跨线程用它是编译错误而非"更不安全"）。

</details>

---

### Q13. 🔴【多选】关于 `async`/`.await`，下列说法正确的有？（选出所有正确项）

- A. `async fn` 返回 `impl Future`，是惰性的：不被 poll 就一行也不执行
- B. `.await` 会阻塞当前 OS 线程直到 future 完成
- C. Future 需要执行器（executor）驱动 poll 才能推进
- D. `join!` 在同一任务内并发轮询多个 future

<details>
<summary>✅ 答案与解析</summary>

**答案：A、C、D**

**解析**：Rust future 是**惰性状态机**：`async` 只构造状态机，执行器反复 `poll` 推进，遇到挂起点返回 `Pending`（A、C）。B 是最要害的误解：`.await` 挂起时**让出**当前任务，执行器把线程让给其他就绪任务——这正是 async 高并发的来源；真正阻塞线程的是 `std::thread::sleep` 这类同步调用（所以 async 代码中要用 `tokio::time::sleep`）。D 正确：`join!` 并发驱动分支，任一挂起不阻碍其他分支。

</details>

---

### Q14. 🟢【判断】Rust 通过所有权系统与 `Send`/`Sync` 标记，在**编译期**静态保证无数据竞争——这就是 "fearless concurrency" 的含义。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：数据竞争 = 并发 + 共享 + 至少一方写 + 无同步。Rust 的"别名-可变分离"在单线程内已排除"同时读写"，跨线程时 `Send`/`Sync` 边界保证只有线程安全的共享方式能编译通过。注意精确表述：编译期保证的是**无数据竞争（UB 层面）**，不排除逻辑层面的竞态条件（race condition）或死锁——后者属于正确性问题，不是内存安全问题。

</details>

---

### Q15. 🔴【判断】`Pin` 的核心作用是防止自引用结构体在移动后内部指针失效；它保证的是"数据不会被移动"，而不是"数据不会被修改"。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：`async` 状态机可能包含指向自身的引用（跨 `.await` 的借用），一旦移动，这些内部指针就悬空——`Pin<Ptr>` 通过"不提供 `&mut T` 安全访问路径"把值钉在内存位置。关键区分：`Pin` 约束的是**位置稳定性**而非**可变性**——被 pin 的数据照样可以被修改（甚至在 `Unpin` 类型上 pin 完全没有效果）。这也是 `Pin` 与 `&mut`（独占但允许移动/替换）语义错位的根源。

</details>

---

## 五、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 10/10 | 🏆 并发/异步（Async）已内化 | 进阶至 [Lock-Free](06_lock_free.md) 或 [Stream Processing](../06_low_level_patterns/05_stream_processing_semantics.md) |
| 7–9/10 | ✅ 核心概念掌握 | 强化 [并发练习](../../exercises/src/concurrency) 和 [异步（Async）练习](../../exercises/src/async_programming) |
| 4–6/10 | 🔄 需巩固基础 | 重读 [Concurrency](01_concurrency.md) · [Async](../01_async/01_async.md) |
| 0–3/10 | 📚 建议重新开始 | 从 [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) 确认 Send/Sync 基础，再读并发章节 |

---

> **对应 Crate**: [`c05_threads`](../../crates/c05_threads) · [`c06_async`](../../crates/c06_async)
> **对应练习**: [`exercises/src/concurrency/`](../../exercises/src/concurrency) · [`exercises/src/async_programming/`](../../exercises/src/async_programming)

---

> **权威来源**: [The Rust Programming Language — Ch16](https://doc.rust-lang.org/book/ch16-00-concurrency.html) · [The Rust Programming Language — Ch17](https://doc.rust-lang.org/book/ch17-00-async-await.html) · [Rust Atomics and Locks](https://marabos.nl/atomics/)

## 嵌入式测验（Embedded Quiz）

本节从测验 1：本文件是 测验：并发与异步（L3 试点扩展） 的专项测验集。…、测验 2：在 测验：并发与异步（L3 试点扩展） 的测验中，若遇到不确…与测验 3：专项测验与概念文件末尾的嵌入式测验有什么区别？（理解层）切入，剖析「嵌入式测验（Embedded Quiz）」的核心内容。

### 测验 1：🟢 本文件是 测验：并发与异步（L3 试点扩展） 的专项测验集。这类测验文件的主要作用是什么？（理解层）

**题目**: 本文件是 测验：并发与异步（L3 试点扩展） 的专项测验集。这类测验文件的主要作用是什么？

<details>
<summary>✅ 答案与解析</summary>

集中提供大量针对特定主题的练习题，帮助学习者系统检验和巩固对该主题的掌握程度，补充概念文件中的嵌入式测验。
</details>

---

### 测验 2：🟢 在 测验：并发与异步（L3 试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？（理解层）

**题目**: 在 测验：并发与异步（L3 试点扩展） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？

<details>
<summary>✅ 答案与解析</summary>

先尝试独立作答，然后对照答案解析理解错误原因，最后回到对应的概念文件重新阅读相关章节，形成"测验-反馈-复习"的闭环。
</details>

---

### 测验 3：🟢 专项测验与概念文件末尾的嵌入式测验有什么区别？（理解层）

**题目**: 专项测验与概念文件末尾的嵌入式测验有什么区别？

<details>
<summary>✅ 答案与解析</summary>

专项测验题量更大、覆盖更全面，通常按难度分层；嵌入式测验更精简，直接关联刚阅读的概念内容，用于即时检验理解。
</details>
