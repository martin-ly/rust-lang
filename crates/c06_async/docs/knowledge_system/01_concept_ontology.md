# 异步编程概念本体 (Concept Ontology)

> **文档类型**: 📘 形式化定义 | 🎓 概念体系 | 🔬 本体论  
> **目标**: 提供异步编程核心概念的精确、形式化、无歧义定义  
> **方法**: 类型论 + 范畴论 + 操作语义

**最后更新**: 2025-10-19  
**Rust版本**: 1.75+ (核心概念), 1.90+ (最新特性)

---

## 📋 本体结构

### 概念层次体系

```text
根概念: AsyncProgramming
├── 核心抽象层 (L1)
│   ├── Future        # 异步计算抽象
│   ├── Task          # 执行单元
│   ├── Runtime       # 运行时环境
│   └── Executor      # 执行器
│
├── 类型系统层 (L2)
│   ├── Pin           # 内存位置固定
│   ├── Send          # 跨线程传输
│   ├── Sync          # 跨线程共享
│   └── 'static       # 静态生命周期
│
├── 语法层 (L3)
│   ├── async fn      # 异步函数
│   ├── .await        # 等待点
│   ├── async block   # 异步块
│   └── Stream        # 异步迭代器
│
├── 运行时层 (L4)
│   ├── Reactor       # I/O事件循环
│   ├── Scheduler     # 任务调度器
│   ├── Waker         # 唤醒机制
│   └── Context       # 执行上下文
│
└── 模式层 (L5)
    ├── Select        # 多路选择
    ├── Join          # 并发等待
    ├── Spawn         # 任务生成
    └── Channel       # 异步通信
```

---

## 🎯 L1: 核心抽象层

### 概念: Future

#### 形式化定义

**类型理论定义**:

```text
∀ T. Future<T> : Type → Type
Future<T> ≅ (Pin<&mut Self>, &mut Context<'_>) → Poll<T>

其中:
  Poll<T> = Ready(T) | Pending
  Context<'_> = { waker: &'_ Waker, ... }
```

**Rust定义**:

```rust
pub trait Future {
    type Output;
    
    fn poll(
        self: Pin<&mut Self>, 
        cx: &mut Context<'_>
    ) -> Poll<Self::Output>;
}
```

**操作语义**:

```text
⟦Future⟧ = μF. λ(π, κ). 
  case π of
    | Initial → compute_next_state(π') → (Pending, π')
    | Ready(v) → (Ready(v), ·)
    | Suspended → check_ready(κ) → ...
```

#### 属性向量

| 属性维度 | 值 | 说明 |
|---------|-----|------|
| **类型安全** | Safe | 完全类型安全，编译期检查 |
| **内存模型** | Heap/Stack | 取决于具体实现 |
| **生命周期** | Arbitrary | 可以是任意生命周期 |
| **Send** | Conditional | 取决于Output和内部状态 |
| **Sync** | Conditional | 一般不是Sync |
| **惰性求值** | True | 不调用poll不执行 |
| **组合性** | High | 通过组合子高度可组合 |
| **零成本抽象** | True | 编译为状态机，无运行时开销 |

#### 关系集合

**is-a 关系**:

- Future is-a Composable Computation
- Future is-a State Machine

**has-a 关系**:

- Future has-a Output Type
- Future has-a Internal State
- Future has-a Poll Method

**depends-on 关系**:

- Future depends-on Pin (内存安全)
- Future depends-on Context (唤醒机制)
- Future depends-on Poll (返回类型)

**implements 关系**:

```rust
impl<T> Future for BoxFuture<'_, T>
impl<F: Future> Future for Pin<Box<F>>
impl Future for Ready<T>
impl Future for Pending<T>
```

#### 数学性质

1. **惰性性 (Laziness)**:

   ```text
   ∀ f: Future<T>. ¬executed(f) ⟺ ¬polled(f)
   ```

2. **确定性进展 (Deterministic Progress)**:

   ```text
   ∀ f: Future<T>. 
     poll(f) = Pending → ∃ waker. will_wake(f)
   ```

3. **最终终止性 (Eventual Termination)**:

   ```text
   ∀ f: Future<T>. 
     (∀n. poll^n(f) = Pending) → ∃m > n. poll^m(f) = Ready(v)
   ```

   (假设资源充足且无死锁)

---

### 概念: Task

#### 形式化定义1

**类型定义**:

```text
Task<T> = (Future<T>, TaskMetadata, TaskState)

其中:
  TaskMetadata = { id: TaskId, priority: Priority, ... }
  TaskState = New | Scheduled | Running | Completed | Cancelled
```

**状态转移**:

```text
State Transition Graph:
  New → Scheduled → Running ⇄ Scheduled
      ↓                ↓
  Cancelled      Completed
```

#### 属性向量1

| 属性 | 值 | 说明 |
|------|-----|------|
| **执行模型** | Cooperative | 协作式调度 |
| **抢占性** | Non-preemptive | 只在.await点让出 |
| **优先级** | Optional | 部分运行时支持 |
| **取消性** | Cooperative | 需要检查取消标志 |
| **局部性** | Task-local | 支持任务局部存储 |

#### 关系集合1

**is-a**:

- Task is-a Schedulable Unit
- Task is-a Future Wrapper

**has-a**:

- Task has-a Future
- Task has-a State
- Task has-a Waker
- Task has-a JoinHandle

**interacts-with**:

- Task interacts-with Executor (被调度)
- Task interacts-with Scheduler (状态更新)

---

### 概念: Runtime

#### 形式化定义2

**类型定义**:

```text
Runtime = (Executor, Reactor, Scheduler, ResourcePool)

其中:
  Executor: Task → Result<T, E>
  Reactor: EventSource → EventLoop
  Scheduler: Queue<Task> × Policy → Task
  ResourcePool: { threads, memory, handles, ... }
```

**运行时不变式**:

```text
Invariants:
  1. ∀ task ∈ ready_queue. is_pollable(task)
  2. ∀ task ∈ wait_queue. has_waker(task)
  3. single_threaded ⟹ !need(Send + Sync)
  4. multi_threaded ⟹ require(Send)
```

#### 属性向量2

| 属性 | Tokio | async-std | Smol |
|------|-------|-----------|------|
| **线程模型** | 多线程 | 多线程 | 单/多 |
| **调度器** | 工作窃取 | 工作窃取 | 简单队列 |
| **I/O模型** | mio/epoll | 平台原生 | polling |
| **定时器** | 时间轮 | 堆 | 堆 |
| **代码行数** | ~50K | ~20K | ~1.5K |
| **生态系统** | 最大 | 中等 | 小 |

#### 关系集合2

**is-a**:

- Runtime is-a Execution Environment
- Runtime is-a Resource Manager

**has-a**:

- Runtime has-a Executor
- Runtime has-a Reactor
- Runtime has-a Scheduler
- Runtime has-a Thread Pool

**provides**:

- Runtime provides Task Spawning
- Runtime provides I/O Abstraction
- Runtime provides Timer Service

---

### 概念: Executor

#### 形式化定义3

**类型定义**:

```text
Executor = {
  spawn: Future<T> → JoinHandle<T>,
  block_on: Future<T> → T,
  run: () → !
}

执行语义:
  execute(executor, future) = 
    loop {
      match future.poll(cx) {
        Ready(v) => return v,
        Pending => wait_for_wake()
      }
    }
```

#### 属性向量3

| 属性 | 单线程 | 多线程 | 说明 |
|------|--------|--------|------|
| **并发度** | 1 | N | 同时运行任务数 |
| **公平性** | 高 | 中 | 任务调度公平性 |
| **延迟** | 低 | 中 | 任务切换延迟 |
| **吞吐量** | 低 | 高 | 总体任务处理能力 |
| **复杂度** | 低 | 高 | 实现复杂度 |

#### 关系集合3

**is-a**:

- Executor is-a Task Scheduler

**has-a**:

- Executor has-a Task Queue
- Executor has-a Worker Threads (多线程)

**collaborates-with**:

- Executor collaborates-with Reactor (I/O事件)

---

## 🎯 L2: 类型系统层

### 概念: `Pin<T>`

#### 形式化定义4

**类型定义**:

```text
Pin<P> = { ptr: P | ∀ t1, t2. ptr@t1 = ptr@t2 }
  即: Pin保证指针指向的内存地址不变

Unpin: Type → Prop
  Unpin(T) ⟺ ∀ x: T. Pin<x> ≅ x
  即: Unpin类型不需要固定
```

**Rust定义**:

```rust
pub struct Pin<P> {
    pointer: P,
}

// 安全约束
impl<P: Deref<Target: Unpin>> Pin<P> {
    pub fn new(pointer: P) -> Pin<P>
}

impl<P: Deref> Pin<P> {
    pub unsafe fn new_unchecked(pointer: P) -> Pin<P>
}
```

#### 属性向量4

| 属性 | 值 | 说明 |
|------|-----|------|
| **内存固定** | Required | 保证内存位置不变 |
| **自引用** | Enabled | 允许安全的自引用 |
| **移动语义** | Restricted | 限制移动操作 |
| **Drop保证** | Strong | 保证正确析构 |

#### 数学性质4

1. **位置不变性 (Location Invariance)**:

   ```text
   ∀ p: Pin<P>, t1, t2.
     addr(deref(p)@t1) = addr(deref(p)@t2)
   ```

2. **Unpin传递性**:

   ```text
   ∀ T: Unpin, U: Unpin.
     (T, U): Unpin
     [T; N]: Unpin
     Box<T>: Unpin
   ```

3. **Pin投影**:

   ```text
   struct S { a: A, b: B }
   Pin<&mut S> ⊢ Pin<&mut A>  if !Unpin(S)
   ```

---

### 概念: Send + Sync

#### 形式化定义5

**类型类定义**:

```text
trait Send: 'static { }
  语义: T: Send ⟺ 可以安全地在线程间传递所有权

trait Sync: 'static { }
  语义: T: Sync ⟺ &T: Send
        即: 可以安全地在线程间共享不可变引用
```

**组合规则**:

```text
T: Send, U: Send ⊢ (T, U): Send
T: Send, U: Send ⊢ Either<T, U>: Send
T: Send ⊢ Vec<T>: Send
T: Sync ⊢ Arc<T>: Send + Sync
T: Send ⊢ Mutex<T>: Send + Sync
```

#### 属性矩阵

| 类型 | Send | Sync | 说明 |
|------|------|------|------|
| `i32` | ✅ | ✅ | 原始类型 |
| `String` | ✅ | ✅ | 独占所有权 |
| `Rc<T>` | ❌ | ❌ | 非原子引用计数 |
| `Arc<T>` | ✅ | ✅ | 原子引用计数 |
| `Cell<T>` | ✅ | ❌ | 内部可变性，非线程安全 |
| `RefCell<T>` | ✅ | ❌ | 运行时借用检查 |
| `Mutex<T>` | ✅ | ✅ | 锁保护 |
| `RwLock<T>` | ✅ | ✅ | 读写锁 |
| `MutexGuard<'_, T>` | ❌ | ✅ | 锁守卫 |

#### 关系集合5

**implies**:

- T: Sync ⟹ &T: Send
- T: Send, U: Send ⟹ (T, U): Send

**enables**:

- T: Send enables spawn(async move { ... })
- T: Send + Sync enables `Arc<T>`

---

## 🎯 L3: 语法层

### 概念: async fn

#### 形式化定义6

**语法脱糖 (Desugaring)**:

```rust
// 语法糖
async fn foo(x: T) -> U { body }

// 脱糖为
fn foo(x: T) -> impl Future<Output = U> {
    async move { body }
}

// 进一步展开为状态机
enum FooFuture {
    State0 { x: T },
    State1 { intermediate: V },
    State2 { result: U },
}

impl Future for FooFuture {
    type Output = U;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<U> {
        // 状态机逻辑
    }
}
```

**类型规则**:

```text
Γ ⊢ body: T
─────────────────────────────
Γ ⊢ async { body }: impl Future<Output = T>

Γ ⊢ f: T → U    Γ ⊢ x: T
──────────────────────────────
Γ ⊢ async fn f(x: T) -> U: T → impl Future<Output = U>
```

#### 属性向量6

| 属性 | 值 | 说明 |
|------|-----|------|
| **返回类型** | impl Future | 匿名Future类型 |
| **状态机** | 编译器生成 | 自动生成 |
| **捕获** | Move语义 | 默认move捕获 |
| **生命周期** | 复杂 | 需要仔细处理 |

---

### 概念: .await

#### 形式化定义7

**操作语义**:

```text
⟦expr.await⟧ = 
  let future = expr;
  loop {
    match Pin::new(&mut future).poll(cx) {
      Poll::Ready(v) => break v,
      Poll::Pending => {
        // 保存当前状态
        // 返回Pending到上层
        // 注册waker
        return Poll::Pending
      }
    }
  }
```

**类型规则**:

```text
Γ ⊢ expr: impl Future<Output = T>
──────────────────────────────────
Γ ⊢ expr.await: T

前提: 必须在async上下文中
```

#### 属性向量7

| 属性 | 值 | 说明 |
|------|-----|------|
| **让出点** | True | 协作式让出执行权 |
| **类型安全** | Safe | 编译期检查 |
| **零成本** | True | 编译为状态转换 |
| **可取消** | By Task | 任务级别可取消 |

---

### 概念: Stream

#### 形式化定义8

**类型定义**:

```rust
pub trait Stream {
    type Item;
    
    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
    ) -> Poll<Option<Self::Item>>;
}
```

**类比关系**:

```text
Iterator  : Future  :: Stream : AsyncIterator
─────────────────────────────────────────────
next()    : poll()  :: poll_next() : async next()
```

**数学定义**:

```text
Stream<T> ≅ () → Future<Option<T>>

Stream是一个无限（或有限）的Future序列:
[Future<Option<T₀>>, Future<Option<T₁>>, ..., Future<None>]
```

#### 属性向量8

| 属性 | Iterator | Stream | 说明 |
|------|----------|--------|------|
| **执行模型** | 同步 | 异步 | 阻塞vs非阻塞 |
| **背压** | Pull | Pull | 消费者驱动 |
| **组合性** | 高 | 高 | 丰富的组合子 |
| **零成本** | 是 | 是 | 编译期优化 |

---

## 🎯 L4: 运行时层

### 概念: Waker

#### 形式化定义9

**类型定义**:

```rust
pub struct Waker {
    waker: RawWaker,
}

pub struct RawWaker {
    data: *const (),
    vtable: &'static RawWakerVTable,
}

pub struct RawWakerVTable {
    clone: unsafe fn(*const ()) -> RawWaker,
    wake: unsafe fn(*const ()),
    wake_by_ref: unsafe fn(*const ()),
    drop: unsafe fn(*const ()),
}
```

**语义规范**:

```text
wake(waker) 语义:
  1. 通知调度器任务已就绪
  2. 将任务放入就绪队列
  3. 可能唤醒等待的线程

安全约束:
  1. wake必须是线程安全的
  2. 可以从任何线程调用
  3. 调用后Future应该可以取得进展
```

#### 属性向量9

| 属性 | 值 | 说明 |
|------|-----|------|
| **线程安全** | Required | Send + Sync |
| **克隆成本** | 低 | 引用计数 |
| **唤醒延迟** | 微秒级 | 取决于实现 |

---

### 概念: Reactor

#### 形式化定义10

**类型定义**:

```text
Reactor = {
  register: (Source, Token, Interest) → Result<()>,
  deregister: Token → Result<()>,
  poll: Timeout → Vec<Event>,
}

其中:
  Source = TcpStream | UdpSocket | Timer | Signal | ...
  Interest = Read | Write | Both
  Event = (Token, Ready)
  Ready = Readable | Writable | Error
```

**事件循环语义**:

```text
reactor_loop:
  loop {
    events = poll(timeout);
    for event in events {
      waker = lookup_waker(event.token);
      waker.wake();
    }
  }
```

#### 属性向量10

| 属性 | epoll | kqueue | IOCP | 说明 |
|------|-------|--------|------|------|
| **平台** | Linux | BSD/Mac | Windows | 操作系统 |
| **模型** | Readiness | Readiness | Completion | 通知模型 |
| **性能** | 高 | 高 | 高 | O(已就绪) |

---

## 🎯 L5: 模式层

### 概念: Select

#### 形式化定义11

**类型签名**:

```rust
select! {
    result1 = future1 => handle1(result1),
    result2 = future2 => handle2(result2),
    ...
}
```

**语义**:

```text
select([f₁, f₂, ..., fₙ]) = 
  poll_all([f₁, f₂, ..., fₙ]):
    if ∃ i. poll(fᵢ) = Ready(vᵢ):
      return (i, vᵢ)  // 返回第一个就绪的
    else:
      return Pending
```

**公平性**:

```text
随机公平: 每次从随机位置开始轮询
轮询公平: 记住上次位置，从下一个开始
优先级: 按顺序轮询，前面优先
```

---

### 概念: Join

#### 形式化定义12

**类型签名**:

```rust
join!(fut1, fut2, ..., futN) -> (T1, T2, ..., TN)
```

**语义**:

```text
join([f₁, f₂, ..., fₙ]) = 
  poll_all([f₁, f₂, ..., fₙ]):
    results = []
    for fᵢ in [f₁, ..., fₙ]:
      match poll(fᵢ):
        Ready(v) => results[i] = Some(v)
        Pending => continue
    
    if all(results.is_some()):
      return Ready(tuple(results))
    else:
      return Pending
```

**并发性**:

```text
join: 所有Future在同一任务中并发轮询
spawn + join: 所有Future在不同任务中并发执行
```

---

## 📊 概念关系图

```text
                    AsyncProgramming
                           |
           ┌───────────────┼───────────────┐
           ↓               ↓               ↓
        Future           Runtime         Syntax
           |               |               |
     ┌─────┼─────┐    ┌────┼────┐    ┌────┼────┐
     ↓     ↓     ↓    ↓    ↓    ↓    ↓    ↓    ↓
   Poll  Output Pin Exec React Sched async await Stream
                 |     |     |
            ┌────┘     |     └────┐
            ↓          ↓          ↓
          Send       Waker     Context
            ↑          ↑
            └──────────┘
              Thread Safety
```

---

## 🔗 概念依赖关系

### 依赖层次

```text
L0 (基础): Type, Lifetime, Ownership
    ↓
L1 (核心): Future, Poll, Pin
    ↓
L2 (语法): async, await, async fn
    ↓
L3 (运行时): Executor, Reactor, Waker
    ↓
L4 (模式): join, select, spawn
    ↓
L5 (应用): Web, CLI, Service
```

### 必需依赖 (Required Dependencies)

```text
Future ⇒ {Poll, Pin, Output}
async fn ⇒ {Future}
.await ⇒ {Future, Context}
Task ⇒ {Future, Waker}
Executor ⇒ {Task, Waker}
Runtime ⇒ {Executor, Reactor}
```

### 可选依赖 (Optional Dependencies)

```text
Future ⊙ Send (多线程运行时需要)
Future ⊙ 'static (spawn通常需要)
Future ⊙ Unpin (某些API需要)
```

---

## 📝 使用指南

### 如何查找概念

1. **按层次查找**: L1核心 → L2类型 → L3语法 → L4运行时 → L5模式
2. **按关系查找**: 概念 → 关系集合 → 相关概念
3. **按属性查找**: 概念 → 属性向量 → 满足条件的概念

### 如何理解概念

1. **读形式化定义** - 精确理解概念本质
2. **看属性向量** - 了解概念特征
3. **查关系集合** - 理解概念在体系中的位置
4. **验证数学性质** - 理解概念的理论基础

### 概念查询示例

**Q: Future为什么需要Pin？**

A: 查找路径

1. Future → depends-on → Pin
2. Pin → 定义 → 内存位置固定
3. Future → 实现 → 状态机
4. 状态机 → 可能包含 → 自引用
5. 自引用 → 需要 → Pin保证安全

---

## 🔄 版本历史

- **v1.0** (2025-10-19): 初始版本，定义核心概念本体

---

**维护状态**: ✅ 活跃  
**形式化级别**: ⭐⭐⭐⭐ (高度形式化)

🎓 **概念本体为异步编程提供坚实的理论基础！**
