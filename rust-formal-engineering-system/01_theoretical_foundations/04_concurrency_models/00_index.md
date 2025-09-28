# 并发模型（Concurrency Models）索引

## 目的

- 梳理 Rust 并发编程的理论基础与实现模型。
- 对比不同并发模型的适用场景与性能特征。
- 建立并发安全的形式化理论基础。

## 核心概念

### 并发模型分类

- **共享内存模型**：通过共享内存和同步原语进行通信
- **消息传递模型**：通过消息通道进行通信，避免共享状态
- **Actor 模型**：每个 Actor 拥有独立状态，通过消息通信
- **CSP 模型**：通信顺序进程，强调同步通信

### 线程模型

- **OS 线程**：内核级线程，重量级，适合 CPU 密集型任务
- **绿色线程**：用户级线程，轻量级，适合 I/O 密集型任务
- **异步任务**：基于 Future 的协程模型，零成本抽象

### 同步原语

- **互斥锁（Mutex）**：排他性访问共享资源
- **读写锁（RwLock）**：允许多读或单写
- **条件变量（Condvar）**：线程间条件同步
- **信号量（Semaphore）**：限制并发访问数量

### 内存模型

- **原子操作**：不可分割的操作，保证原子性
- **内存序**：指定内存操作的重排序约束
- **数据竞争**：多线程同时访问共享数据且至少一个为写
- **内存一致性**：多线程环境下的内存可见性保证

## 理论基础

### 并发安全的形式化

Rust 的并发模型基于以下形式化保证：

1. **数据竞争自由**：

   ```text
   ∀r1, r2. ¬(write(r1) ∧ access(r2) ∧ alias(r1, r2))
   ```

2. **内存一致性**：

   ```text
   ∀thread t, memory_order mo. consistent(t, mo)
   ```

3. **结构化并发**：

   ```text
   ∀task t, parent p. lifetime(t) ⊆ lifetime(p)
   ```

### 所有权与并发

- **移动语义**：所有权转移确保数据只能被一个线程拥有
- **借用规则**：编译时检查防止并发访问冲突
- **RAII**：资源自动管理，避免资源泄漏

## 与 Rust 的关联

### 类型系统支持

- **`Send` trait**：标记类型可以安全地跨线程转移所有权
- **`Sync` trait**：标记类型可以安全地跨线程共享引用
- **`Send + Sync`**：既可以被转移也可以被共享
- **`!Send`/`!Sync`**：明确标记不能跨线程的类型

### 异步编程模型

- **Future trait**：表示异步计算的值
- **async/await**：语法糖，简化异步代码编写
- **Executor**：异步任务调度器
- **Waker**：异步任务唤醒机制

### 零成本抽象

- **编译时检查**：并发安全在编译时保证，运行时无开销
- **单态化**：泛型代码编译时特化，避免虚函数调用
- **内存布局**：零成本抽象不改变内存布局

## 术语（Terminology）

- 并发（Concurrency）、并行（Parallelism）
- 数据竞争（Data Race）、竞态条件（Race Condition）
- 原子操作（Atomic Operation）、内存序（Memory Ordering）
- 结构化并发（Structured Concurrency）

## 形式化与证明（Formalization）

- 数据竞争自由：`∀r1, r2. ¬(write(r1) ∧ access(r2) ∧ alias(r1, r2))`
- 内存一致性：基于 C++11 内存模型
- 死锁检测：通过所有权系统避免循环等待

## 实践与样例（Practice）

- 线程与同步：参见 [crates/c05_threads](../../../crates/c05_threads/)
- 异步编程：[crates/c06_async](../../../crates/c06_async/)
- 分布式系统：[crates/c20_distributed](../../../crates/c20_distributed/)

## 相关索引

- 内存安全：[`../02_memory_safety/00_index.md`](../02_memory_safety/00_index.md)
- 所有权与借用：[`../03_ownership_borrowing/00_index.md`](../03_ownership_borrowing/00_index.md)
- 编程范式（并发）：[`../../02_programming_paradigms/05_concurrent/00_index.md`](../../02_programming_paradigms/05_concurrent/00_index.md)

## 导航

- 返回理论基础：[`../00_index.md`](../00_index.md)
- 编程范式：[`../../02_programming_paradigms/00_index.md`](../../02_programming_paradigms/00_index.md)
- 质量保障：[`../../10_quality_assurance/00_index.md`](../../10_quality_assurance/00_index.md)
- 返回项目根：[`../../README.md`](../../README.md)
