# Rust形式化方法面试题集锦

> **创建日期**: 2026-02-24
> **目标**: 面试准备、自我检测、知识点巩固
> **级别**: L1/L2 (给人看的)

---

## 使用指南

**难度分级**:

- ⭐ 基础 - 初级开发者
- ⭐⭐ 进阶 - 中级开发者
- ⭐⭐⭐ 高级 - 高级/核心开发者
- ⭐⭐⭐⭐ 专家 - 研究者/架构师

---

## 一、所有权与借用 (20题)

### ⭐ 基础题

**Q1: 什么是所有权？三规则是什么？**

<details>
<summary>答案</summary>

所有权是Rust内存管理的核心机制：

1. 每个值有且只有一个所有者
2. 所有者离开作用域，值被丢弃
3. 所有权可以转移(Move)或借用(Borrow)

</details>

---

**Q2: Move和Copy有什么区别？**

<details>
<summary>答案</summary>

- **Move**: 转移所有权，原变量不再有效
- **Copy**: 复制值，原变量仍然有效

实现Copy的条件：只包含标量值或其他Copy类型。

</details>

---

**Q3: 什么是借用规则？**

<details>
<summary>答案</summary>

1. 要么一个可变引用(&mut)，要么多个不可变引用(&)
2. 引用必须始终有效（不能悬垂）

</details>

---

**Q4: 为什么这段代码编译错误？如何修复？**

```rust
let x = String::from("hello");
let y = x;
println!("{}", x);
```

<details>
<summary>答案</summary>

**错误原因**: String不实现Copy，赋值时Move所有权，x不再有效。

**修复方案**:

```rust
// 方案1: clone
let y = x.clone();

// 方案2: 借用
let y = &x;
```

</details>

---

### ⭐⭐ 进阶题

**Q5: 解释`Rc`和`Arc`的区别，为什么`Rc`不是Send？**

<details>
<summary>答案</summary>

| 特性 | Rc | Arc |
| :--- | :--- | :--- |
| 线程安全 | 否 | 是 |
| 引用计数 | 非原子 | 原子 |

`Rc`不是Send因为引用计数更新非线程安全，多线程同时修改会导致数据竞争。

</details>

---

**Q6: `RefCell`和`Mutex`有什么区别？**

<details>
<summary>答案</summary>

- `RefCell`: 单线程运行时借用检查
- `Mutex`: 多线程互斥锁，线程安全

相同点：都提供内部可变性。

</details>

---

**Q7: 什么是内部可变性模式？举例说明。**

<details>
<summary>答案</summary>

允许在不可变引用下修改数据：

```rust
use std::cell::Cell;
let cell = Cell::new(5);
let x = &cell;
x.set(10);  // 内部修改
```

常用类型：`Cell`, `RefCell`, `Mutex`, `RwLock`

</details>

---

**Q8: 解释这段代码为什么错误：**

```rust
let mut x = 5;
let r1 = &x;
let r2 = &mut x;
println!("{}", r1);
```

<details>
<summary>答案</summary>

**错误**: 不能同时存在不可变借用和可变借用。

`r1`仍然存在（被println使用），所以不能创建`r2`。

**修复**: 缩小r1的作用域，在创建r2前结束r1。

</details>

---

### ⭐⭐⭐ 高级题

**Q9: 什么是非词法生命周期(NLL)？它解决了什么问题？**

<details>
<summary>答案</summary>

NLL基于值的使用位置而非词法作用域判断生命周期。

**解决的问题**:

```rust
let mut x = 5;
let y = &x;
println!("{}", y);  // y最后一次使用
// 这里y已经结束，即使还在作用域内
let z = &mut x;  // 在NLL之前编译错误
```

</details>

---

**Q10: `PhantomData`有什么用？**

<details>
<summary>答案</summary>

零大小类型，用于告诉编译器使用了某个类型，影响生命周期。

```rust
struct Slice<'a, T: 'a> {
    ptr: *const T,
    _marker: PhantomData<&'a T>,
}
```

</details>

---

**Q11: 什么是Pin？为什么需要它？**

<details>
<summary>答案</summary>

`Pin`保证值不会被移动，用于自引用结构。

async/await需要Pin因为Future是状态机，可能自引用。

</details>

---

**Q12: 解释`mem::replace`和`mem::swap`的区别。**

<details>
<summary>答案</summary>

- `swap`: 交换两个可变引用的值
- `replace`: 替换值并返回旧值

```rust
mem::swap(&mut a, &mut b);  // a和b交换
let old = mem::replace(&mut a, new);  // a=new，返回旧值
```

</details>

---

### ⭐⭐⭐⭐ 专家题

**Q13: 如何理解"所有权系统防止内存泄漏"这个说法？**

<details>
<summary>答案</summary>

严格来说不完全正确：

- 所有权系统主要防止**内存不安全**（use-after-free, double-free）
- 内存泄漏仍可能发生（`Rc`循环引用、`mem::forget`）

但所有权+RAII确实有助于减少泄漏。

</details>

---

**Q14: `Box::leak`有什么用途？**

<details>
<summary>答案</summary>

将堆内存泄漏为`'static`引用：

```rust
let x: &'static str = Box::leak(Box::new(String::from("hello")));
```

用途：

- 全局状态
- 与C FFI交互
- 运行时单例

</details>

---

**Q15: 如何实现一个线程安全的引用计数智能指针？**

<details>
<summary>答案</summary>

使用`AtomicUsize`作为引用计数：

```rust
struct Arc<T> {
    ptr: NonNull<ArcInner<T>>,
}

struct ArcInner<T> {
    count: AtomicUsize,
    data: T,
}
```

clone: `count.fetch_add(1, Relaxed)`
drop: `if count.fetch_sub(1, Release) == 1 { 释放 }`

</details>

---

## 二、类型系统 (15题)

### ⭐ 基础题

**Q16: 什么是`Sized` trait？**

<details>
<summary>答案</summary>

标记编译时已知大小的类型。泛型参数默认`T: Sized`，DST（动态大小类型）如`str`、`[T]`、`dyn Trait`不是Sized。

</details>

---

**Q17: `impl Trait`和`dyn Trait`有什么区别？**

<details>
<summary>答案</summary>

| 特性 | impl Trait | dyn Trait |
| :--- | :--- | :--- |
| 分发 | 静态 | 动态 |
| 开销 | 无 | 虚表查找 |
| 返回类型 | 支持 | 需要Box |

</details>

---

**Q18: 什么是关联类型(Associated Type)？**

<details>
<summary>答案</summary>

Trait中定义的占位类型，由实现者指定：

```rust
trait Iterator {
    type Item;
    fn next(&mut self) -> Option<Self::Item>;
}
```

每个实现只能有一个Item类型。

</details>

---

### ⭐⭐ 进阶题

**Q19: 什么是型变(Variance)？协变、逆变、不变有什么区别？**

<details>
<summary>答案</summary>

| 型变 | 含义 | 示例 |
| :--- | :--- | :--- |
| 协变(+) | 保持方向 | `Box<&'static str> <: Box<&'a str>` |
| 逆变(-) | 反转方向 | `fn(&'a str) <: fn(&'static str)` |
| 不变(=) | 必须相同 | `&mut T`, `Cell<T>` |

</details>

---

**Q20: 生命周期省略的三条规则是什么？**

<details>
<summary>答案</summary>

1. 每个引用参数有自己的生命周期
2. 只有一个输入生命周期 → 赋给输出
3. `&self`存在 → `self`的生命周期赋给输出

</details>

---

**Q21: 解释`for<'a>`语法。**

<details>
<summary>答案</summary>

高阶trait bound (HRTB)，表示"对于所有生命周期"。

```rust
F: for<'a> Fn(&'a str) -> &'a str
```

</details>

---

### ⭐⭐⭐ 高级题

**Q22: 什么是泛型关联类型(GAT)？**

<details>
<summary>答案</summary>

允许关联类型有泛型参数：

```rust
trait Container {
    type Item<'a>;
    fn get(&self, index: usize) -> Option<Self::Item<'_>>;
}
```

</details>

---

**Q23: 什么是特化(Specialization)？**

<details>
<summary>答案</summary>

为特定类型提供泛型的特殊实现：

```rust
impl<T> Trait for T { default fn method() {} }
impl Trait for i32 { fn method() {} }  // 特化
```

目前不稳定，需要feature flag。

</details>

---

**Q24: 解释空指针优化(Null Pointer Optimization)。**

<details>
<summary>答案</summary>

`Option<&T>`和`&T`大小相同，用0表示`None`。

```rust
assert_eq!(size_of::<Option<&i32>>(), size_of::<&i32>());
```

</details>

---

### ⭐⭐⭐⭐ 专家题

**Q25: 如何实现一个自定义DST？**

<details>
<summary>答案</summary>

DST需要大小信息存储在胖指针中：

```rust
struct MySlice {
    data: [u8],  // DST
}

// 使用胖指针
let ptr: *const MySlice;  // 包含长度信息
```

通常与`#[repr(C)]`和指针操作配合。

</details>

---

## 三、并发与异步 (15题)

### ⭐ 基础题

**Q26: Send和Sync有什么区别？**

<details>
<summary>答案</summary>

- **Send**: 可跨线程转移所有权
- **Sync**: 可跨线程共享（通过`&T`）

等价定义：`T: Sync ⇔ &T: Send`

</details>

---

**Q27: `Mutex`和`RwLock`怎么选？**

<details>
<summary>答案</summary>

- 读多写少 → `RwLock`
- 通用场景 → `Mutex`（默认推荐）

`RwLock`可能有写者饥饿问题。

</details>

---

**Q28: `thread::spawn`和`tokio::spawn`区别？**

<details>
<summary>答案</summary>

| 特性 | thread::spawn | tokio::spawn |
| :--- | :--- | :--- |
| 创建 | OS线程 | 异步任务 |
| 成本 | ~MB | ~KB |
| 数量 | 几百 | 数百万 |

</details>

---

### ⭐⭐ 进阶题

**Q29: 什么是死锁？如何避免？**

<details>
<summary>答案</summary>

死锁：两个线程互相等待对方释放锁。

避免策略：

1. 锁顺序一致
2. 使用`try_lock`
3. 避免嵌套锁
4. 使用作用域锁

</details>

---

**Q30: async/await原理是什么？**

<details>
<summary>答案</summary>

编译器将async函数转换为状态机：

```rust
async fn foo() { bar().await; }

// 转换为：
enum FooFuture {
    Start,
    WaitingBar,
    Done,
}
```

执行器轮询Future，在`.await`处可能让出。

</details>

---

**Q31: 为什么`Cell`不是Sync？**

<details>
<summary>答案</summary>

`Cell`提供内部可变性但没有同步机制，多线程同时修改会导致数据竞争。

使用`Mutex`进行线程安全的内部可变性。

</details>

---

### ⭐⭐⭐ 高级题

**Q32: 什么是`Unpin`？**

<details>
<summary>答案</summary>

标记可以安全移动的类型。大多数类型自动实现`Unpin`。

非`Unpin`：async fn生成的Future（自引用）。

</details>

---

**Q33: 如何避免跨await持锁导致的死锁？**

<details>
<summary>答案</summary>

`.await`前释放锁：

```rust
// ❌ 危险
let guard = mutex.lock().unwrap();
some_async().await;

// ✅ 安全
{
    let guard = mutex.lock().unwrap();
    // 使用guard
}  // 释放
some_async().await;

// 或使用tokio::sync::Mutex
let guard = tokio_mutex.lock().await;
```

</details>

---

**Q34: `select!`宏是什么？**

<details>
<summary>答案</summary>

等待多个Future，哪个先完成就执行哪个：

```rust
tokio::select! {
    _ = task1 => println!("task1"),
    _ = task2 => println!("task2"),
}
```

</details>

---

### ⭐⭐⭐⭐ 专家题

**Q35: 实现一个简单的异步运行时。**

<details>
<summary>答案</summary>

核心组件：

1. Task队列
2. Executor轮询
3. Reactor处理IO事件
4. Waker唤醒Task

```rust
struct Runtime {
    task_queue: VecDeque<Task>,
}

impl Runtime {
    fn run(&self) {
        while let Some(task) = self.task_queue.pop_front() {
            if task.poll() == Pending {
                // 重新入队或等待唤醒
            }
        }
    }
}
```

</details>

---

## 四、形式化方法 (10题)

### ⭐⭐ 进阶题

**Q36: 什么是L1/L2/L3证明？**

<details>
<summary>答案</summary>

- **L1**: 证明思路（给人看的）
- **L2**: 完整数学证明
- **L3**: 机器证明（Coq/Lean）

</details>

---

**Q37: T-OW2定理是什么？**

<details>
<summary>答案</summary>

**所有权唯一性定理**: 每个值在任意时刻只有一个所有者。

直觉：防止双重释放。

</details>

---

**Q38: T-BR1定理是什么？**

<details>
<summary>答案</summary>

**数据竞争自由定理**: 借用检查通过 ⇒ 无数据竞争。

直觉：编译时保证并发安全。

</details>

---

### ⭐⭐⭐ 高级题

**Q39: 解释类型安全中的"进展性"和"保持性"。**

<details>
<summary>答案</summary>

- **进展性**: 良类型表达式可以继续求值或已是值
- **保持性**: 求值保持类型

类型安全 = 进展性 + 保持性

</details>

---

**Q40: 分离逻辑是什么？**

<details>
<summary>答案</summary>

用于推理共享可变状态的逻辑框架。

核心概念：

- 资源断言：`l ↦ v`（位置l存储值v）
- 分离合取：`P * Q`（P和Q拥有不相交资源）
- 框架规则：`{P} C {Q} ⊢ {P*R} C {Q*R}`

</details>

---

## 五、分布式与工作流 (10题)

### ⭐⭐ 进阶题

**Q41: Saga模式解决什么问题？**

<details>
<summary>答案</summary>

长事务问题。将大事务分解为多个本地事务，每个有补偿操作。

</details>

---

**Q42: 编排式vs编制式Saga区别？**

<details>
<summary>答案</summary>

| 特性 | 编排式 | 编制式 |
| :--- | :--- | :--- |
| 控制 | 集中协调器 | 事件驱动 |
| 可见性 | 高 | 低 |
| 灵活性 | 低 | 高 |

</details>

---

**Q43: CQRS适合什么场景？**

<details>
<summary>答案</summary>

- 读多写少
- 复杂查询
- 需要事件溯源

</details>

---

### ⭐⭐⭐ 高级题

**Q44: 熔断器模式如何工作？**

<details>
<summary>答案</summary>

状态机：

- Closed: 正常
- Open: 错误率过高，快速失败
- Half-Open: 试探恢复

</details>

---

**Q45: 如何选择工作流引擎？**

<details>
<summary>答案</summary>

- 需要持久化 → Temporal/Cadence
- 简单流程 → 自研状态机
- 人工任务 → Camunda

</details>

---

## 六、系统设计题 (5题)

### ⭐⭐⭐⭐ 专家题

**Q46: 设计一个线程安全的LRU缓存。**

<details>
<summary>答案</summary>

```rust
use std::collections::HashMap;
use std::sync::Mutex;

struct LruCache<K, V> {
    map: Mutex<HashMap<K, Node<V>>>,
    capacity: usize,
}

// 使用Mutex保护HashMap
// 内部维护访问顺序（链表）
```

关键点：

- `Mutex`保护共享状态
- 处理容量超限
- 更新访问顺序

</details>

---

**Q47: 设计一个Saga协调器。**

<details>
<summary>答案</summary>

```rust
struct Saga {
    steps: Vec<Step>,
    compensations: Vec<Compensation>,
}

impl Saga {
    async fn execute(&self) -> Result<(), SagaError> {
        let mut completed = 0;
        for (i, step) in self.steps.iter().enumerate() {
            match step.execute().await {
                Ok(_) => completed += 1,
                Err(e) => {
                    // 执行补偿
                    for j in (0..completed).rev() {
                        self.compensations[j].execute().await?;
                    }
                    return Err(e);
                }
            }
        }
        Ok(())
    }
}
```

</details>

---

**Q48: 设计一个异步HTTP客户端连接池。**

<details>
<summary>答案</summary>

```rust
struct ConnectionPool {
    connections: Mutex<Vec<Connection>>,
    max_size: usize,
}

impl ConnectionPool {
    async fn get(&self) -> Connection {
        // 尝试从池中获取
        // 池空则创建新连接
        // 超过max_size则等待
    }

    async fn put(&self, conn: Connection) {
        // 归还连接
        // 健康检查
        // 放入池中或关闭
    }
}
```

</details>

---

**Q49: 如何实现一个自定义Future？**

<details>
<summary>答案</summary>

```rust
struct MyFuture {
    state: State,
}

impl Future for MyFuture {
    type Output = i32;

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match self.state {
            State::Start => {
                // 注册唤醒
                self.state = State::Waiting;
                Poll::Pending
            }
            State::Waiting => {
                // 检查完成
                if ready {
                    Poll::Ready(42)
                } else {
                    Poll::Pending
                }
            }
        }
    }
}
```

</details>

---

**Q50: 设计一个事件溯源系统。**

<details>
<summary>答案</summary>

核心组件：

1. **Event Store**: 存储事件
2. **Aggregate**: 领域模型
3. **Projection**: 读模型
4. **Command Handler**: 处理命令

```rust
// 事件
trait Event {}

// 聚合
trait Aggregate {
    fn apply(&mut self, event: &dyn Event);
    fn handle(&self, command: Command) -> Vec<Box<dyn Event>>;
}

// 事件存储
trait EventStore {
    fn append(&self, events: Vec<Box<dyn Event>>);
    fn get(&self, id: &str) -> Vec<Box<dyn Event>>;
}
```

</details>

---

## 附录：自我评估

### 初学者 (答对15-25题)

- 掌握所有权、借用基础
- 能写简单Rust程序
- 建议继续学习并发

### 进阶者 (答对25-35题)

- 理解类型系统
- 能处理生命周期
- 建议学习形式化方法

### 高级 (答对35-45题)

- 掌握并发异步
- 理解高级类型特性
- 建议参与开源

### 专家 (答对45-50题)

- 深入理解原理
- 能设计复杂系统
- 建议贡献研究

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-24
**状态**: ✅ 已完成 - 面试题集锦 (50题)
