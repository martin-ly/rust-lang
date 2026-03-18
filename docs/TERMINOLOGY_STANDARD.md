# Rust 术语标准化文档

> **文档版本**: 1.0.0
> **创建日期**: 2026-03-17
> **最后更新**: 2026-03-17
> **Rust 版本**: 1.94.0+ (Edition 2024)
> **对齐标准**: Ferrocene Language Specification (FLS)
> **状态**: ✅ 已完成

---

## 📋 目录

- [Rust 术语标准化文档](#rust-术语标准化文档)
  - [📋 目录](#-目录)
  - [简介](#简介)
    - [术语表使用说明](#术语表使用说明)
  - [所有权相关术语](#所有权相关术语)
  - [类型系统术语](#类型系统术语)
  - [并发相关术语](#并发相关术语)
  - [异步相关术语](#异步相关术语)
  - [宏系统术语](#宏系统术语)
  - [FFI/Unsafe 术语](#ffiunsafe-术语)
  - [生命周期术语](#生命周期术语)
  - [版本演进术语](#版本演进术语)
  - [参考资源](#参考资源)
    - [官方文档引用格式说明](#官方文档引用格式说明)
    - [相关文档](#相关文档)
    - [Ferrocene FLS 标准对照](#ferrocene-fls-标准对照)
  - [更新历史](#更新历史)

---

## 简介

本文档旨在为 Rust 学习项目提供标准化的术语对照体系，确保中英文术语使用的一致性和准确性。所有术语定义均对齐 **Ferrocene Language Specification (FLS)** 标准，并引用官方文档（The Book、Reference、RFC）作为权威来源。

### 术语表使用说明

- **中文术语**: 推荐使用的中文译名
- **英文术语**: 官方英文术语（FLS 标准）
- **定义**: 简洁准确的术语定义
- **官方来源**: 权威出处引用，格式为 `文档名 章节`

---

## 所有权相关术语

| 中文术语 | 英文术语 | 定义 | 官方来源 |
|---------|---------|------|---------|
| 所有权 | Ownership | 每个值在任一时刻有且只有一个所有者，所有者离开作用域时值被释放 | The Book Ch 4.1 |
| 借用 | Borrowing | 通过引用临时访问值而不获取所有权，分为不可变借用和可变借用 | The Book Ch 4.2 |
| 不可变借用 | Immutable Borrow / Shared Reference | 允许只读访问的引用类型 `&T`，可同时存在多个 | The Book Ch 4.2 |
| 可变借用 | Mutable Borrow / Exclusive Reference | 允许读写访问的引用类型 `&mut T`，同一作用域内只能存在一个 | The Book Ch 4.2 |
| 移动 | Move | 将值的所有权从一个变量转移到另一个变量，原变量失效 | The Book Ch 4.1 |
| 复制 | Copy | 按位复制的隐式克隆，原变量保持有效；仅适用于实现 `Copy` trait 的类型 | The Book Ch 4.1 |
| 克隆 | Clone | 显式深度复制，通过 `Clone` trait 实现，可自定义复制逻辑 | The Book Ch 4.1 |
| 借用检查器 | Borrow Checker | 编译器组件，静态分析代码确保借用规则被遵守，防止数据竞争和悬垂引用 | Reference Ch 8.2 |
| 所有权规则 | Ownership Rules | (1) 每个值有唯一所有者；(2) 值随所有者离开作用域而释放；(3) 所有权可转移 | The Book Ch 4.1 |
| 借用规则 | Borrowing Rules | (1) 任一时刻只能有一个可变引用或任意数量的不可变引用；(2) 引用必须始终有效 | The Book Ch 4.2 |
| 作用域 | Scope | 变量有效的程序文本区域，通常由大括号 `{}` 界定 | The Book Ch 4.1 |
| 释放 | Drop | 值离开作用域时自动调用 `Drop::drop` 方法回收资源 | The Book Ch 15.3 |
| RAII | Resource Acquisition Is Initialization | 资源获取即初始化，资源生命周期与对象绑定，通过析构器自动释放 | Reference Ch 11.3 |
| 资源 | Resource | 程序使用的内存、文件句柄、网络连接等需要管理的实体 | The Book Ch 15.3 |
| 所有权转移 | Ownership Transfer | 值的所有权从一个绑定移动到另一个绑定的过程 | Reference Ch 8.2 |
| 词法作用域 | Lexical Scope | 基于源代码文本结构的变量作用域范围 | Reference Ch 8.2 |
| 非词法生命周期 | Non-Lexical Lifetimes (NLL) | 基于实际使用情况而非词法作用域的生命周期计算，允许更早释放借用 | RFC 2094 |
| 重新借用 | Reborrow | 从已有引用创建新引用的过程，如从 `&mut T` 重新借出 `&T` | Reference Ch 8.2 |

---

## 类型系统术语

| 中文术语 | 英文术语 | 定义 | 官方来源 |
|---------|---------|------|---------|
| 类型系统 | Type System | 对程序中值的分类和约束系统，确保类型安全 | The Book Ch 3.2 |
| 静态类型 | Static Typing | 编译期确定所有变量类型的类型系统特性 | The Book Ch 3.2 |
| 类型推导 | Type Inference | 编译器根据上下文自动推导变量类型的能力 | The Book Ch 3.2 |
| 标量类型 | Scalar Types | 单一值的类型，包括整数、浮点数、布尔值和字符 | The Book Ch 3.2 |
| 复合类型 | Compound Types | 可包含多个值的类型，包括元组和数组 | The Book Ch 3.2 |
| 元组 | Tuple | 固定长度、元素类型可异构的有序集合类型 `(T1, T2, ...)` | The Book Ch 3.2 |
| 数组 | Array | 固定长度、元素类型同构的连续内存集合类型 `[T; N]` | The Book Ch 3.2 |
| 切片 | Slice | 动态长度的连续序列视图类型 `&[T]` 或 `&mut [T]` | The Book Ch 4.3 |
| 结构体 | Struct | 命名字段的复合数据类型，类似其他语言的记录或对象 | The Book Ch 5.1 |
| 枚举 | Enum | 可拥有多个变体（variants）的代数数据类型 | The Book Ch 6 |
| 变体 | Variant | 枚举类型的可能取值之一，可包含关联数据 | The Book Ch 6 |
| 模式匹配 | Pattern Matching | 使用 `match` 等结构解构值并执行对应分支的机制 | The Book Ch 6.2 |
| 泛型 | Generics | 参数化类型，允许编写适用于多种类型的代码 | The Book Ch 10 |
| 特征 | Trait | 定义共享行为的抽象接口，可被类型实现 | The Book Ch 10.2 |
| 实现 | Implementation / Impl | 为类型定义方法或实现特征的具体代码块 | The Book Ch 5.3 |
| 关联类型 | Associated Type | 在 trait 定义中声明、在实现时指定的占位符类型 | The Book Ch 19.2 |
| 泛型参数 | Generic Parameter | 类型、生命周期或常量的形式参数，用于泛型定义 | Reference Ch 6.1 |
| 类型参数 | Type Parameter | 泛型定义中的形式类型参数，如 `T` in `Vec<T>` | The Book Ch 10.1 |
| 常量泛型 | Const Generics | 使用常量值作为泛型参数，如 `[T; N]` 中的 `N` | RFC 2000 |
| 约束 | Bound / Constraint | 对泛型参数的限制条件，如 `T: Display` | The Book Ch 10.2 |
| 特征对象 | Trait Object | 运行时多态，使用 `dyn Trait` 实现的动态分发 | The Book Ch 17.2 |
| 静态分发 | Static Dispatch | 编译期确定具体实现的函数调用，通过单态化实现 | Reference Ch 8.9 |
| 动态分发 | Dynamic Dispatch | 运行时确定具体实现的函数调用，通过虚表实现 | Reference Ch 8.9 |
| 单态化 | Monomorphization | 将泛型代码转换为具体类型代码的编译过程 | Reference Ch 8.9 |
| 零成本抽象 | Zero-Cost Abstractions | 运行时无开销的高级抽象，开销在编译期消除 | The Book Ch 13.1 |
| 型变 | Variance | 类型构造器对其参数的子类型关系保持方式（协变/逆变/不变） | Reference Ch 4.6 |
| 协变 | Covariance | 子类型关系保持方向一致（若 `A <: B` 则 `F<A> <: F<B>`） | Reference Ch 4.6 |
| 逆变 | Contravariance | 子类型关系方向反转（若 `A <: B` 则 `F<B> <: F<A>`） | Reference Ch 4.6 |
| 不变 | Invariance | 无子类型关系（`F<A>` 与 `F<B>` 无关） | Reference Ch 4.6 |
| never 类型 | Never Type (`!`) | 表示永不返回的函数的返回类型，可强制转换为任何类型 | Reference Ch 4.8 |
| 单元类型 | Unit Type (`()`) | 空元组类型，表示无有意义返回值 | The Book Ch 3.2 |
| 新类型模式 | Newtype Pattern | 使用元组结构体包装现有类型以提供类型安全和抽象 | The Book Ch 19.3 |
| 类型别名 | Type Alias | 为现有类型创建同义词，使用 `type` 关键字 | The Book Ch 19.4 |

---

## 并发相关术语

| 中文术语 | 英文术语 | 定义 | 官方来源 |
|---------|---------|------|---------|
| 并发 | Concurrency | 多个任务在重叠时间段内执行，可能交替进行 | The Book Ch 16 |
| 并行 | Parallelism | 多个任务真正同时执行，需要多核处理器 | The Book Ch 16 |
| 线程 | Thread | 操作系统调度的基本执行单元，Rust 通过 `std::thread` 支持 | The Book Ch 16.1 |
| 进程 | Process | 独立运行的程序实例，拥有独立的内存空间 | The Book Ch 16.1 |
| 数据竞争 | Data Race | 多个线程同时访问同一内存，至少一个是写操作且无同步 | The Book Ch 16.1 |
| 竞态条件 | Race Condition | 程序行为依赖于线程执行顺序的非确定性问题 | The Book Ch 16.1 |
| 死锁 | Deadlock | 多个线程互相等待对方释放资源而无法继续执行的状态 | The Book Ch 16.2 |
| 同步 | Synchronization | 协调多线程访问共享资源的机制 | The Book Ch 16.2 |
| 互斥锁 | Mutex | 互斥（Mutual Exclusion）同步原语，保证同时只有一个线程访问数据 | The Book Ch 16.2 |
| 读写锁 | RwLock | 允许多读单写的同步原语，读共享写独占 | The Book Ch 16.2 |
| 原子操作 | Atomic Operation | 不可中断的基本操作，通过 `std::sync::atomic` 提供 | The Book Ch 16.3 |
| 内存序 | Memory Ordering | 控制原子操作间可见性的规则（Relaxed/Acquire/Release/AcqRel/SeqCst） | Reference Ch 22.9 |
| 顺序一致性 | Sequential Consistency | 最强的内存序，保证所有线程看到一致的操作顺序 | Reference Ch 22.9 |
| 获取-释放 | Acquire-Release | 成对的内存序，建立 happens-before 关系 | Reference Ch 22.9 |
| 条件变量 | Condition Variable | 允许线程等待特定条件满足的同步原语 | The Book Ch 16.2 |
| 信号量 | Semaphore | 控制同时访问某资源的线程数量的计数同步原语 | The Book Ch 16.2 |
| 屏障 | Barrier | 使多个线程在某点等待直到所有线程到达的同步原语 | The Book Ch 16.2 |
| 线程安全 | Thread Safety | 类型可安全地在多线程间共享而不引起数据竞争的性质 | The Book Ch 16.4 |
| Send | Send Trait | 标记可安全转移到其他线程的类型的 trait | The Book Ch 16.4 |
| Sync | Sync Trait | 标记可安全被多线程共享引用（`&T` 是 `Send`）的类型的 trait | The Book Ch 16.4 |
| 内部可变性 | Interior Mutability | 允许在不可变引用后修改数据的设计模式（RefCell/Mutex） | The Book Ch 15.5 |
| 外部可变性 | Exterior Mutability | 通过 `&mut` 显式声明的可变性 | Reference Ch 8.4 |
| 消息传递 | Message Passing | 线程间通过通道（channel）发送数据而非共享内存的并发模式 | The Book Ch 16.2 |
| 通道 | Channel | 线程间通信机制，发送者和接收者通过消息传递数据 | The Book Ch 16.2 |
| 共享状态 | Shared State | 多线程访问同一内存的并发模式，需要同步机制 | The Book Ch 16.2 |
| 线程本地存储 | Thread-Local Storage | 每个线程拥有独立实例的数据存储机制 | Reference Ch 10.3 |
| 工作窃取 | Work Stealing | 线程从其他线程任务队列窃取任务的负载均衡策略 | The Book Ch 16.3 |
| 无锁编程 | Lock-Free Programming | 不使用互斥锁，依赖原子操作实现的并发 | Reference Ch 22.9 |

---

## 异步相关术语

| 中文术语 | 英文术语 | 定义 | 官方来源 |
|---------|---------|------|---------|
| 异步 | Asynchronous / Async | 允许任务在等待 I/O 时让出执行权，不阻塞线程的编程模型 | The Book Ch 17 |
| async/await | Async/Await | 异步编程的语法糖，`async` 定义异步代码块，`await` 等待异步操作完成 | The Book Ch 17.1 |
| Future | Future | 表示尚未完成的异步计算，实现了 `std::future::Future` trait | The Book Ch 17.1 |
| 轮询 | Polling | 通过调用 `poll` 方法检查 Future 是否完成的机制 | Reference Ch 37.1 |
| 上下文 | Context | 传递给 `poll` 方法的异步执行上下文，包含 waker | Reference Ch 37.1 |
| Waker | Waker | 通知执行器 Future 可以再次轮询的机制 | Reference Ch 37.1 |
| 执行器 | Executor | 管理和调度 Future 执行运行时的组件 | The Book Ch 17.3 |
| 运行时 | Runtime | 提供异步执行环境的库（如 Tokio、async-std） | The Book Ch 17.3 |
| 反应器 | Reactor | 监听 I/O 事件并唤醒对应 waker 的运行时组件 | Reference Ch 37.1 |
| 任务 | Task | 异步运行时调度的执行单元，通常是顶层的 Future | The Book Ch 17.3 |
| 阻塞操作 | Blocking Operation | 会阻塞当前线程直到完成的操作，不应在异步上下文中执行 | The Book Ch 17.3 |
| 阻塞线程池 | Blocking Thread Pool | 运行时提供的专用线程池，用于执行阻塞操作 | The Book Ch 17.3 |
| 状态机 | State Machine | `async fn` 编译后转换成的状态机结构 | Reference Ch 37.1 |
| Pin | Pin | 固定值在内存中位置的类型，用于自引用结构和异步 Future | The Book Ch 17.4 |
| Unpin | Unpin | 标记类型可安全移动的 trait，大多数类型自动实现 | The Book Ch 17.4 |
| 固定 | Pinning | 保证值在内存中不被移动的机制 | The Book Ch 17.4 |
| 流 | Stream | 异步版本的迭代器，产生一系列异步值 | Reference Ch 37.1 |
| Sink | Sink | 可异步接收值的抽象，Stream 的反向操作 | Reference Ch 37.1 |
| 异步迭代器 | Async Iterator | 异步生成值序列的类型（`async fn next(&mut self) -> Option<T>`） | RFC 79 |
| 并发执行 | Concurrent Execution | 同时执行多个 Future 并等待其完成（`join!`/`select!`） | The Book Ch 17.3 |
| 竞争选择 | Race / Select | 在多个异步操作中等待最先完成的那个 | The Book Ch 17.3 |
| 超时 | Timeout | 为异步操作设置最大等待时间的机制 | The Book Ch 17.3 |
| 背压 | Backpressure | 当消费者慢于生产者时控制数据流率的机制 | The Book Ch 17.3 |
| 协作式调度 | Cooperative Scheduling | 任务主动让出执行权的调度方式 | The Book Ch 17 |
| 生成器 | Generator | 可暂停和恢复执行的函数，是 async/await 的实现基础 | RFC 2033 |
| Yield | Yield | 生成器中暂停执行并返回值的操作 | RFC 2033 |

---

## 宏系统术语

| 中文术语 | 英文术语 | 定义 | 官方来源 |
|---------|---------|------|---------|
| 宏 | Macro | 在编译期进行代码生成和转换的元编程机制 | The Book Ch 19.5 |
| 声明宏 | Declarative Macro / `macro_rules!` | 基于模式匹配的宏定义方式，类似规则匹配替换 | The Book Ch 19.5 |
| 过程宏 | Procedural Macro | 在编译期执行 Rust 代码进行代码生成的宏类型 | The Book Ch 19.5 |
| 派生宏 | Derive Macro | 过程宏的一种，通过 `#[derive(Trait)]` 自动实现 trait | The Book Ch 19.5 |
| 属性宏 | Attribute Macro | 过程宏的一种，定义自定义属性 `#[attribute]` 修饰项 | The Book Ch 19.5 |
| 函数式宏 | Function-like Macro | 过程宏的一种，类似函数调用的宏 `macro!()` | The Book Ch 19.5 |
| Token | Token | 源代码的最小语法单元，宏操作的基本单位 | Reference Ch 3 |
| Token 树 | Token Tree (TT) | 配对的括号及其内部 tokens 组成的树形结构 | Reference Ch 3 |
| 元变量 | Metavariable | 宏规则中用于捕获和引用模式的变量，如 `$name:ty` | Reference Ch 6.2 |
| 重复 | Repetition | 宏中匹配和展开重复模式的机制（`*` 和 `+`） | Reference Ch 6.2 |
| 片段指定符 | Fragment Specifier | 指定元变量类型的标记（`expr`、`ty`、`ident` 等） | Reference Ch 6.2 |
| 卫生性 | Hygiene | 宏生成的标识符不会与外部代码意外冲突的性质 | Reference Ch 6.2 |
| 宏展开 | Macro Expansion | 编译期将宏调用替换为生成代码的过程 | Reference Ch 6 |
| 编译期计算 | Compile-Time Evaluation | 宏在编译阶段执行代码生成 | The Book Ch 19.5 |
| TokenStream | TokenStream | 过程宏接收和返回的 token 序列类型 | Reference Ch 6.3 |
| 语法扩展 | Syntax Extension | 通过宏扩展语言语法的机制 | Reference Ch 6 |
| 宏导出 | Macro Export | 使用 `#[macro_export]` 使宏可从 crate 外部访问 | The Book Ch 19.5 |
| 宏导入 | Macro Import | 通过 `#[macro_use]` 或路径导入宏 | The Book Ch 19.5 |
| 守卫条件 | Guard Condition | 宏规则中额外的 `if` 条件过滤匹配 | Reference Ch 6.2 |

---

## FFI/Unsafe 术语

| 中文术语 | 英文术语 | 定义 | 官方来源 |
|---------|---------|------|---------|
| Unsafe Rust | Unsafe Rust | 允许执行不安全操作的 Rust 代码块，需要 `unsafe` 关键字 | The Book Ch 19.1 |
| 安全抽象 | Safe Abstraction | 在 unsafe 实现上提供安全接口的封装层 | The Book Ch 19.1 |
| 原始指针 | Raw Pointer | 不受借用检查器约束的裸指针（`*const T` 和 `*mut T`） | The Book Ch 19.1 |
| 不安全函数 | Unsafe Function | 声明为 `unsafe fn` 的函数，调用者需保证调用安全 | The Book Ch 19.1 |
| 不安全块 | Unsafe Block | 声明为 `unsafe { ... }` 的代码块，内部可执行不安全操作 | The Book Ch 19.1 |
| FFI | Foreign Function Interface | 与其他语言（主要是 C）交互的接口机制 | The Book Ch 19.1 |
| 外部函数 | Extern Function | 使用 `extern` 声明的来自其他语言或提供给其他语言的函数 | The Book Ch 19.1 |
| 外部块 | Extern Block | 使用 `extern "C" { ... }` 声明外部库函数的块 | The Book Ch 19.1 |
| ABI | Application Binary Interface | 定义函数调用约定、数据布局等二进制接口规范 | Reference Ch 8.10 |
| 调用约定 | Calling Convention | 函数调用的低级约定（如 `"C"`、`"system"`） | Reference Ch 8.10 |
| 未初始化内存 | Uninitialized Memory | 未写入有效值的内存区域，读取它是未定义行为 | The Book Ch 19.1 |
| MaybeUninit | MaybeUninit | 安全处理可能未初始化内存的类型 | The Book Ch 19.1 |
| 未定义行为 | Undefined Behavior (UB) | 违反 Rust 安全假设的行为，后果不可预测 | The Book Ch 19.1 |
| 悬垂指针 | Dangling Pointer | 指向已释放或未分配内存的指针 | The Book Ch 19.1 |
| 空指针 | Null Pointer | 不指向任何有效内存地址的指针（值为 0） | The Book Ch 19.1 |
| 内存对齐 | Memory Alignment | 数据在内存中的地址必须是其类型的对齐值的倍数 | Reference Ch 10.2 |
| 填充 | Padding | 编译器在结构体字段间插入的空白字节，用于对齐 | Reference Ch 10.2 |
| 布局 | Layout | 类型的内存布局（大小和对齐）信息 | Reference Ch 10.2 |
| 类型双关 | Type Punning | 将一种类型的位重新解释为另一种类型 | The Book Ch 19.1 |
| 联合体 | Union | 共享同一块内存的多种类型，类似 C 的 union | Reference Ch 7.8 |
| 透明包装 | Transparent Wrapper | 使用 `#[repr(transparent)]` 保证与内部类型相同布局 | Reference Ch 10.1 |
| 内联汇编 | Inline Assembly | 在 Rust 代码中直接嵌入汇编指令（`asm!` 宏） | Reference Ch 10.4 |
| 易变读取 | Volatile Read/Write | 不被编译器优化的特殊内存读写操作 | Reference Ch 10.4 |
| 静态变量 | Static Variable | 程序整个生命周期存在的全局变量，可声明为可变 | The Book Ch 19.1 |
| 可变静态 | Mutable Static | 使用 `static mut` 声明的可变全局变量，访问需要 unsafe | The Book Ch 19.1 |

---

## 生命周期术语

| 中文术语 | 英文术语 | 定义 | 官方来源 |
|---------|---------|------|---------|
| 生命周期 | Lifetime | 引用有效的程序执行时段，确保引用不悬垂 | The Book Ch 10.3 |
| 生命周期参数 | Lifetime Parameter | 泛型生命周期，如 `'a`，用于标注引用有效范围 | The Book Ch 10.3 |
| 生命周期省略 | Lifetime Elision | 编译器根据约定自动推导生命周期标注的规则 | The Book Ch 10.3 |
| 生命周期标注 | Lifetime Annotation | 显式声明引用生命周期的语法，如 `&'a T` | The Book Ch 10.3 |
| 生命周期边界 | Lifetime Bound | 对生命周期参数的限制，如 `'a: 'b`（'a 至少和 'b 一样长） | Reference Ch 6.1.4 |
| 静态生命周期 | Static Lifetime (`'static`) | 整个程序执行期间有效的生命周期 | The Book Ch 10.3 |
| 生命周期子类型 | Lifetime Subtyping | 生命周期间的包含关系，如 `'long: 'short` | Reference Ch 4.6 |
| 早期绑定 | Early Bound | 在定义点就确定具体生命周期的泛型参数 | Reference Ch 6.1 |
| 晚期绑定 | Late Bound | 在调用点根据上下文确定具体生命周期的泛型参数 | Reference Ch 6.1 |
| 生命周期约束 | Lifetime Constraint | 泛型定义中对生命周期的限制条件 | Reference Ch 6.1.4 |
| 高阶 trait 边界 | Higher-Ranked Trait Bounds (HRTB) | 对任意生命周期的 trait 约束，如 `for<'a>` | Reference Ch 6.2.4 |
| 借用集 | Borrow Set | 编译器分析中某点的所有活跃借用集合 | Reference Ch 8.2 |
| 存活集 | Live Set | 编译器分析中某点的所有存活变量集合 | Reference Ch 8.2 |
| 限制区域 | Restriction | 生命周期分析中值不可被借用的代码区域 | Reference Ch 8.2 |
| Polonius | Polonius | 基于逻辑的区域推理的新一代借用检查算法 | RFC 2094 |
| 区域推理 | Region Inference | 编译器自动推导引用生命周期的算法过程 | Reference Ch 8.2 |
| 悬垂引用 | Dangling Reference | 指向已释放内存的引用，生命周期系统防止此问题 | The Book Ch 10.3 |
| 协变生命周期 | Covariant Lifetime | 较长生命周期可替代较短生命周期的性质 | Reference Ch 4.6 |
| 逆变生命周期 | Contravariant Lifetime | 较短生命周期可替代较长生命周期的性质（罕见） | Reference Ch 4.6 |
| 出入作用域 | Enter/Exit Scope | 变量进入或离开作用域的生命周期分析概念 | Reference Ch 8.2 |

---

## 版本演进术语

| 中文术语 | 英文术语 | 定义 | 官方来源 |
|---------|---------|------|---------|
| Edition | Edition | Rust 语言的大版本，允许不兼容语法演进（2015/2018/2021/2024） | The Book Ch Appendix |
| 版本迁移 | Edition Migration | 将代码从旧 Edition 迁移到新 Edition 的过程 | The Book Ch Appendix |
| 弃用 | Deprecation | 标记某些功能将在未来版本移除的机制（`#[deprecated]`） | Reference Ch 7.8 |
| 不稳定特性 | Unstable Feature | 仅可在 nightly 编译器使用的实验性功能 | Reference Ch 3.1 |
| 特性门 | Feature Gate | 使用 `#![feature(...)]` 启用不稳定特性的机制 | Reference Ch 3.1 |
| Nightly | Nightly | 每日构建的 Rust 开发版本，包含实验性功能 | The Book Ch Appendix |
| Beta | Beta | Rust 的预发布测试版本 | The Book Ch Appendix |
| Stable | Stable | Rust 的正式稳定版本，每 6 周发布 | The Book Ch Appendix |
| LTS | Long-Term Support | 长期支持版本，提供更长时间的维护和更新 | RFC 1522 |
| Ferrocene | Ferrocene | Rust 的安全关键应用认证版本，符合工业标准 | Ferrocene Spec |
| FLS | Ferrocene Language Specification | Ferrocene 的语言规范文档 | Ferrocene Docs |
| 语义版本 | Semantic Versioning | 版本号格式 `MAJOR.MINOR.PATCH`，Rust 使用 `MINOR` 发布新功能 | The Book Ch Appendix |
| 破坏性变更 | Breaking Change | 可能导致现有代码失效的语法或行为变更 | RFC 1105 |
|  crater 运行 | Crater Run | 使用 crater 工具测试变更对整个生态影响的过程 | Rust Forge |
| MCP | Major Change Proposal | Rust 编译器重大变更提案流程 | Rust Forge |
| RFC | Request for Comments | Rust 语言设计和变更的标准提案流程 | RFC Repo |
| FCP | Final Comment Period | RFC 进入最终评论期，即将接受或拒绝 | RFC Process |
| 稳定性承诺 | Stability Promise | Rust 对稳定版 API 不引入破坏性变更的承诺 | The Book Ch Appendix |
| 版本检查 | Version Check | `rust-version` 字段指定最低支持的 Rust 版本 | Cargo Book |
| Rust 2024 | Rust 2024 Edition | 最新 Edition（2024年发布），包含 `gen` 关键字等新特性 | Rust Blog |

---

## 参考资源

### 官方文档引用格式说明

本文档中的官方来源引用采用以下格式：

| 引用格式 | 说明 | URL |
|---------|------|-----|
| The Book Ch X.Y | The Rust Programming Language 官方教程 | <https://doc.rust-lang.org/book/> |
| Reference Ch X.Y | Rust Reference 语言参考 | <https://doc.rust-lang.org/reference/> |
| RFC XXXX | Rust RFC 提案 | <https://rust-lang.github.io/rfcs/> |
| Ferrocene Spec | Ferrocene 语言规范 | <https://spec.ferrocene.dev/> |
| Cargo Book | Cargo 文档 | <https://doc.rust-lang.org/cargo/> |
| Rust Blog | 官方博客 | <https://blog.rust-lang.org/> |
| Rust Forge | 贡献者文档 | <https://forge.rust-lang.org/> |

### 相关文档

- [研究笔记术语表](./research_notes/GLOSSARY.md) - 形式化方法和研究相关术语
- [所有权速查卡](./02_reference/quick_reference/ownership_cheatsheet.md) - 所有权系统快速参考
- [类型系统速查卡](./02_reference/quick_reference/type_system.md) - 类型系统快速参考
- [错误码映射](./02_reference/ERROR_CODE_MAPPING.md) - 编译器错误码详解

### Ferrocene FLS 标准对照

本术语表与 Ferrocene Language Specification (FLS) 对齐的关键点：

1. **所有权与借用**: 采用 FLS Chapter 8 的借用检查器术语定义
2. **类型系统**: 遵循 FLS Chapter 4 的类型分类和型变规则
3. **生命周期**: 基于 FLS Chapter 6 的泛型生命周期规范
4. **Unsafe Rust**: 参考 FLS Chapter 11 的不安全操作定义
5. **并发模型**: 与 FLS Chapter 16 的线程安全 trait 定义一致

---

## 更新历史

| 版本 | 日期 | 更新内容 | 作者 |
|-----|------|---------|------|
| 1.0.0 | 2026-03-17 | 初始版本，包含 8 大类术语，对齐 FLS 标准 | Rust 学习项目 |

---

> **维护说明**: 本文档随 Rust 版本更新而维护。如有术语变更或新增，请提交 Issue 或 PR 更新本文档。
