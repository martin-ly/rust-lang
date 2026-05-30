> **Bloom 层级**: 记忆 → 理解
> **定位**: 本项目的最小国际化基础设施（决策 3-C）
> **目标**: 为 100 个高频 Rust 术语提供标准化的英文原文对照，确保学习者能顺利对接 crates.io、RFC、GitHub Issue 等英文生态。
> **前置概念**: [所有权](../01_foundation/01_ownership.md) · [借用](../01_foundation/02_borrowing.md) · [类型系统](../01_foundation/04_type_system.md)
> **后置概念**: [生命周期](../01_foundation/03_lifetimes.md) · [特质](../02_intermediate/01_traits.md) · [泛型](../02_intermediate/02_generics.md)
> **标准来源**: [The Rust Programming Language (TRPL)](https://doc.rust-lang.org/book/) · [Rust Reference](https://doc.rust-lang.org/reference/) · [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)

# Rust 核心术语英中对照表

---

## L1 基础层术语 (Foundation)

| 中文术语 | English Term | 层级 | 定义 | 官方来源 |
|:---|:---|:---:|:---|:---|
| 所有权 | Ownership | L1 | Rust 的核心内存管理机制：每个值有且只有一个所有者，所有者离开作用域时值被丢弃 | [TRPL Ch4](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) |
| 借用 | Borrowing | L1 | 通过引用临时访问值而不获取所有权，分为不可变借用 (`&T`) 和可变借用 (`&mut T`) | [TRPL Ch4.2](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html) |
| 生命周期 | Lifetime | L1 | 引用的有效范围，Rust 编译器通过生命周期分析确保引用始终有效 | [TRPL Ch10.3](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html) |
| 移动 | Move | L1 | 将值的所有权从一个变量转移到另一个变量，原变量此后不可使用 | [TRPL Ch4.1](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html) |
| 复制 | Copy | L1 | 按位复制值的语义（适用于标量类型栈上数据），复制后原变量仍可使用 | [TRPL Ch4.1](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html) |
| 克隆 | Clone | L1 | 显式深拷贝的 trait，用于在堆上分配新内存并复制数据 | [std::clone::Clone](https://doc.rust-lang.org/std/clone/trait.Clone.html) |
| 引用 | Reference | L1 | 指向值的非空指针（`&T` 或 `&mut T`），编译器保证其有效性 | [TRPL Ch4.2](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html) |
| 解引用 | Dereference | L1 | 通过 `*` 运算符访问引用指向的值 | [TRPL Ch15.1](https://doc.rust-lang.org/book/ch15-01-box.html) |
| 作用域 | Scope | L1 | 变量有效的代码区域，通常由 `{}` 界定 | [TRPL Ch4.1](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html) |
| 释放/丢弃 | Drop | L1 | 值离开作用域时自动调用的析构逻辑，由 `Drop` trait 定义 | [std::ops::Drop](https://doc.rust-lang.org/std/ops/trait.Drop.html) |
| 悬空指针 | Dangling Pointer | L1 | 指向已释放内存的引用，Rust 编译器在编译期阻止此类错误 | [TRPL Ch4.2](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html) |
| 别名规则 | Aliasing Rules | L1 | 同一时间内，一个值要么有一个可变引用，要么有多个不可变引用，二者不可兼得 | [Rust Reference](https://doc.rust-lang.org/reference/items/traits.html) |
| 栈 | Stack | L1 | 后进先出的内存区域，用于存储固定大小的局部变量 | [TRPL Ch4.1](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html) |
| 堆 | Heap | L1 | 动态分配内存的区域，通过 `Box::new`、`Vec::new` 等分配 | [TRPL Ch4.1](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html) |
| 切片 | Slice / `str` / `[T]` | L1 | 对连续序列的动态大小视图，如字符串切片 `&str` 和数组切片 `&[T]` | [TRPL Ch4.3](https://doc.rust-lang.org/book/ch04-03-slices.html) |
| 范围 | Range | L1 | 表示整数区间的类型（`a..b`、`a..=b` 等），用于迭代和索引 | [std::ops::Range](https://doc.rust-lang.org/std/ops/struct.Range.html) |
| `Vec` | Vec | L1 | 动态数组，堆上分配的可变长度连续序列 | [std::vec::Vec](https://doc.rust-lang.org/std/vec/struct.Vec.html) |
| `HashMap` | HashMap | L1 | 基于哈希表的无序键值对容器 | [std::collections::HashMap](https://doc.rust-lang.org/std/collections/struct.HashMap.html) |
| `VecDeque` | VecDeque | L1 | 双端队列，支持 O(1) 两端插入和删除 | [std::collections::VecDeque](https://doc.rust-lang.org/std/collections/struct.VecDeque.html) |
| `Debug` | Debug | L1 | 用于格式化输出的 trait，通过 `{:?}` 提供开发者友好的表示 | [std::fmt::Debug](https://doc.rust-lang.org/std/fmt/trait.Debug.html) |
| `Display` | Display | L1 | 用于格式化输出的 trait，通过 `{}` 提供用户友好的表示 | [std::fmt::Display](https://doc.rust-lang.org/std/fmt/trait.Display.html) |
| `PartialEq` | PartialEq | L1 | 定义部分等价关系的 trait（允许 NaN ≠ NaN） | [std::cmp::PartialEq](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html) |
| `Hash` | Hash | L1 | 定义哈希值的 trait，与 `HashMap` 等哈希集合配合使用 | [std::hash::Hash](https://doc.rust-lang.org/std/hash/trait.Hash.html) |
| 模式匹配 | Pattern Matching | L1 | 通过 `match`、`if let` 等解构值并绑定变量的机制 | [TRPL Ch6.2](https://doc.rust-lang.org/book/ch06-02-match.html) |
| 枚举 | Enum / Enumeration | L1 | 代数数据类型，可携带数据的标签联合体（tagged union） | [TRPL Ch6](https://doc.rust-lang.org/book/ch06-00-enums.html) |
| 结构体 | Struct | L1 | 命名字段的复合数据类型 | [TRPL Ch5](https://doc.rust-lang.org/book/ch05-00-structs.html) |
| 元组 | Tuple | L1 | 匿名、固定长度、有序的元素组合 | [TRPL Ch3.2](https://doc.rust-lang.org/book/ch03-02-data-types.html) |
| 泛型 | Generics | L1 | 参数化类型的机制，允许代码复用不同类型 | [TRPL Ch10](https://doc.rust-lang.org/book/ch10-00-generics.html) |
| 特质 | Trait | L1 | 定义共享行为的接口，类似其他语言的接口或类型类 | [TRPL Ch10.2](https://doc.rust-lang.org/book/ch10-02-traits.html) |

## L2 进阶层术语 (Intermediate)

| 中文术语 | English Term | 层级 | 定义 | 官方来源 |
|:---|:---|:---:|:---|:---|
| 特质边界 | Trait Bounds | L2 | 对泛型参数的约束，要求类型实现特定 trait | [TRPL Ch10.2](https://doc.rust-lang.org/book/ch10-02-traits.html) |
| 生命周期省略 | Lifetime Elision | L2 | 编译器自动推断简单函数签名中的生命周期，减少冗余标注 | [TRPL Ch10.3](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html) |
| 生命周期子类型 | Lifetime Subtyping | L2 | `'a: 'b` 表示 `'a` 的生命周期至少与 `'b` 一样长 | [Rust Reference](https://doc.rust-lang.org/reference/subtyping.html) |
| 智能指针 | Smart Pointer | L2 | 拥有元数据或额外功能的指针类型（`Box<T>`、`Rc<T>`、`Arc<T>` 等） | [TRPL Ch15](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html) |
| 内部可变性 | Interior Mutability | L2 | 通过 `Cell<T>`、`RefCell<T>` 在不可变引用后修改数据的设计模式 | [TRPL Ch15.5](https://doc.rust-lang.org/book/ch15-05-interior-mutability.html) |
| 单态化 | Monomorphization | L2 | 编译器为每个泛型实例生成独立代码的过程，实现零成本抽象 | [TRPL Ch10.1](https://doc.rust-lang.org/book/ch10-01-syntax.html) |
| 高阶 trait 边界 | HRTB (Higher-Ranked Trait Bounds) | L2 | `for<'a>` 语法，对任意生命周期约束的泛型边界 | [Rust Reference](https://doc.rust-lang.org/reference/trait-bounds.html#higher-ranked-trait-bounds) |
| 关联类型 | Associated Type | L2 | 在 trait 定义中声明、在实现时确定的具体类型 | [TRPL Ch19.2](https://doc.rust-lang.org/book/ch19-03-advanced-traits.html) |
| 默认实现 | Default Implementation | L2 | trait 中为方法提供默认体，实现者可选择覆盖 | [TRPL Ch10.2](https://doc.rust-lang.org/book/ch10-02-traits.html) |
| 孤儿规则 | Orphan Rule | L2 | 禁止为外部类型实现外部 trait，确保类型系统一致性 | [RFC 1023](https://github.com/rust-lang/rfcs/pull/1023) |
| 新类型模式 | Newtype Pattern | L2 | 通过元组结构体包装现有类型以获得不同 trait 实现 | [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/type-safety.html#c-newtype) |
| 类型状态模式 | Typestate Pattern | L2 | 利用类型系统编码状态机，在编译期阻止非法状态转换 | [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/type-safety.html) |
| 闭包 | Closure | L2 | 匿名函数，可捕获其环境中的变量 | [TRPL Ch13.1](https://doc.rust-lang.org/book/ch13-01-closures.html) |
| 迭代器 | Iterator | L2 | 实现 `Iterator` trait 的对象，提供惰性序列访问 | [TRPL Ch13.2](https://doc.rust-lang.org/book/ch13-02-iterators.html) |
| 适配器方法 | Adapter Methods | L2 | 转换迭代器的链式方法（`map`、`filter`、`fold` 等） | [std::iter::Iterator](https://doc.rust-lang.org/std/iter/trait.Iterator.html) |
| 消耗器方法 | Consumer Methods | L2 | 触发迭代器求值并返回结果的方法（`collect`、`sum`、`for_each` 等） | [std::iter::Iterator](https://doc.rust-lang.org/std/iter/trait.Iterator.html) |
| 错误传播 | Error Propagation | L2 | 通过 `?` 运算符自动将错误返回给调用者 | [TRPL Ch9.2](https://doc.rust-lang.org/book/ch09-02-recoverable-errors-with-result.html) |
| `Result` 类型 | Result | L2 | `Result<T, E>` 枚举，表示可能失败的操作，显式处理错误 | [std::result::Result](https://doc.rust-lang.org/std/result/enum.Result.html) |
| `Option` 类型 | Option | L2 | `Option<T>` 枚举，表示可能不存在的值，替代空指针 | [std::option::Option](https://doc.rust-lang.org/std/option/enum.Option.html) |
| `?` 运算符 | Try Operator / Question Mark | L2 | 自动展开 `Result` 或 `Option`，错误时提前返回 | [TRPL Ch9.2](https://doc.rust-lang.org/book/ch09-02-recoverable-errors-with-result.html) |
| `TryFrom` / `TryInto` | TryFrom / TryInto | L2 | 可失败的类型转换 trait，返回 `Result` 而非直接 panic | [std::convert::TryFrom](https://doc.rust-lang.org/std/convert/trait.TryFrom.html) |
| `AsRef` / `AsMut` | AsRef / AsMut | L2 | 廉价的引用转换 trait，用于泛型函数接受多种引用类型 | [std::convert::AsRef](https://doc.rust-lang.org/std/convert/trait.AsRef.html) |
| `Cow` | Clone-on-Write | L2 | 写时克隆的智能指针，避免不必要的堆分配 | [std::borrow::Cow](https://doc.rust-lang.org/std/borrow/enum.Cow.html) |

## L3 高级层术语 (Advanced)

| 中文术语 | English Term | 层级 | 定义 | 官方来源 |
|:---|:---|:---:|:---|:---|
| 并发 | Concurrency | L3 | 多个任务交替执行，通过线程、async 等机制实现 | [TRPL Ch16](https://doc.rust-lang.org/book/ch16-00-concurrency.html) |
| 并行 | Parallelism | L3 | 多个任务真正同时执行（多核 CPU） | [TRPL Ch16](https://doc.rust-lang.org/book/ch16-00-concurrency.html) |
| `Send` 特质 | Send | L3 | 标记可安全跨线程传递所有权的类型 | [TRPL Ch16.4](https://doc.rust-lang.org/book/ch16-04-extensible-concurrency-sync-and-send.html) |
| `Sync` 特质 | Sync | L3 | 标记可安全跨线程共享引用的类型（`&T` 是 `Send`） | [TRPL Ch16.4](https://doc.rust-lang.org/book/ch16-04-extensible-concurrency-sync-and-send.html) |
| 异步/异步编程 | Async / Asynchronous Programming | L3 | 基于 `Future` 和 async/await 的非阻塞并发模型 | [TRPL Ch17](https://doc.rust-lang.org/book/ch17-00-async-await.html) |
| `Future` | Future | L3 | 代表将来某个时刻完成的异步计算，轮询驱动 | [std::future::Future](https://doc.rust-lang.org/std/future/trait.Future.html) |
| `Pin` | Pin | L3 | 保证值在内存中不被移动的包装类型，用于自引用结构 | [std::pin::Pin](https://doc.rust-lang.org/std/pin/struct.Pin.html) |
| `Waker` | Waker | L3 | 通知异步运行时任务可以继续执行的句柄 | [std::task::Waker](https://doc.rust-lang.org/std/task/struct.Waker.html) |
| 运行时 | Runtime | L3 | 提供异步任务调度、I/O、定时器等服务的执行环境（如 Tokio） | [Async Book](https://rust-lang.github.io/async-book/01_getting_started/04_async_await_primer.html) |
| 不安全 Rust | Unsafe Rust | L3 | 使用 `unsafe` 关键字绕过编译器安全检查的代码区域 | [TRPL Ch20.1](https://doc.rust-lang.org/book/ch20-01-unsafe-rust.html) |
| 裸指针 | Raw Pointer | L3 | `*const T` / `*mut T`，无生命周期/所有权保证，需 `unsafe` 解引用 | [TRPL Ch20.1](https://doc.rust-lang.org/book/ch20-01-unsafe-rust.html) |
| 外部函数接口 | FFI (Foreign Function Interface) | L3 | 与 C/C++ 等其他语言代码互操作的机制 | [TRPL Ch20.1](https://doc.rust-lang.org/book/ch20-01-unsafe-rust.html) |
| 声明宏 | Declarative Macro / macro_rules! | L3 | 基于模式匹配的代码生成宏 | [TRPL Ch20.5](https://doc.rust-lang.org/book/ch20-05-macros.html) |
| 过程宏 | Procedural Macro | L3 | 在编译期操作 token 流的 Rust 代码（派生宏、属性宏、函数宏） | [TRPL Ch20.5](https://doc.rust-lang.org/book/ch20-05-macros.html) |
| 属性 | Attribute | L3 | 以 `#[...]` 修饰的元数据，控制编译器行为 | [Rust Reference](https://doc.rust-lang.org/reference/attributes.html) |
| 过程宏卫生性 | Macro Hygiene | L3 | 宏生成的标识符不会与外部代码冲突的保证 | [Rust Reference](https://doc.rust-lang.org/reference/macros-by-example.html#hygiene) |
| 原子操作 | Atomic Operation | L3 | 不可中断的底层内存操作（`AtomicUsize`、`Ordering` 等） | [std::sync::atomic](https://doc.rust-lang.org/std/sync/atomic/index.html) |
| 内存排序 | Memory Ordering | L3 | 控制原子操作可见性的语义（`Relaxed`、`Acquire`、`Release`、`SeqCst`） | [std::sync::atomic::Ordering](https://doc.rust-lang.org/std/sync/atomic/enum.Ordering.html) |
| 无锁数据结构 | Lock-free Data Structure | L3 | 不使用互斥锁，仅靠原子操作实现线程安全的数据结构 | [Rustonomicon](https://doc.rust-lang.org/nomicon/atomics.html) |
| `Unpin` | Unpin | L3 | 标记可在内存中安全移动的类型；大多数类型自动实现 | [std::marker::Unpin](https://doc.rust-lang.org/std/marker/trait.Unpin.html) |
| `MaybeUninit` | MaybeUninit | L3 | 可能未初始化的内存包装器，用于 `unsafe` 中的延迟初始化 | [std::mem::MaybeUninit](https://doc.rust-lang.org/std/mem/union.MaybeUninit.html) |
| `ManuallyDrop` | ManuallyDrop | L3 | 阻止编译器自动调用 `Drop` 的包装器，用于精细控制析构时机 | [std::mem::ManuallyDrop](https://doc.rust-lang.org/std/mem/struct.ManuallyDrop.html) |
| `Poll` | Poll | L3 | 异步任务的状态枚举：`Pending`（未完成）或 `Ready(T)`（已完成） | [std::task::Poll](https://doc.rust-lang.org/std/task/enum.Poll.html) |
| `Mutex` | Mutex | L3 | 互斥锁，保证同一时间只有一个线程访问受保护数据 | [std::sync::Mutex](https://doc.rust-lang.org/std/sync/struct.Mutex.html) |
| `RwLock` | RwLock | L3 | 读写锁，允许多个读者或单个写者并发访问 | [std::sync::RwLock](https://doc.rust-lang.org/std/sync/struct.RwLock.html) |
| 通道 | Channel | L3 | 线程间或 async 任务间的消息传递机制（`mpsc`、`oneshot`、`broadcast`） | [std::sync::mpsc](https://doc.rust-lang.org/std/sync/mpsc/index.html) |
| 派生宏 | Derive Macro | L3 | 自动为结构体/枚举生成 trait 实现的过程宏（`#[derive(...)]`） | [TRPL Ch20.5](https://doc.rust-lang.org/book/ch20-05-macros.html) |
| 属性宏 | Attribute Macro | L3 | 修饰整个项（函数、模块等）的过程宏，可重写其 AST | [TRPL Ch20.5](https://doc.rust-lang.org/book/ch20-05-macros.html) |

## L4 形式化层术语 (Formal Methods)

| 中文术语 | English Term | 层级 | 定义 | 官方来源 |
|:---|:---|:---:|:---|:---|
| 线性逻辑 | Linear Logic | L4 | 资源敏感的逻辑系统，假设被消费而非重复使用 | [Girard 1987](https://girard.perso.math.cnrs.fr/linear.pdf) |
| 分离逻辑 | Separation Logic | L4 | 扩展 Hoare 逻辑以推理共享可变状态的逻辑框架 | [Reynolds 2002](https://www.cs.cmu.edu/~jcr/seplogic.pdf) |
| Iris | Iris | L4 | 高阶并发分离逻辑框架，RustBelt 的基础 | [RustBelt](https://plv.mpi-sws.org/rustbelt/) |
| RustBelt | RustBelt | L4 | 在 Iris 中形式化验证 Rust 不安全代码正确性的项目 | [POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) |
| 树借用 | Tree Borrows | L4 | Miri 使用的别名模型，替代 Stacked Borrows | [PLDI 2025](https://doi.org/10.1145/3735592) |
| 堆叠借用 | Stacked Borrows | L4 | Miri 的旧别名模型，已被 Tree Borrows 取代 | [Miri Docs](https://github.com/rust-lang/miri) |
| 操作语义 | Operational Semantics | L4 | 通过抽象机器定义程序执行步骤的语义方法 | [Winskel 1993](https://mitpress.mit.edu/9780262731034) |
| 指称语义 | Denotational Semantics | L4 | 将程序映射到数学对象的语义方法 | [Winskel 1993](https://mitpress.mit.edu/9780262731034) |
| Hoare 三元组 | Hoare Triple | L4 | `{P} C {Q}`，前置条件 P 下执行 C 保证后置条件 Q | [Hoare 1969](https://doi.org/10.1145/363235.363259) |
| 类型论 | Type Theory | L4 | 将类型作为数学对象研究的理论，编程语言的逻辑基础 | [Pierce 2002 — TAPL](https://www.cis.upenn.edu/~bcpierce/tapl/) |
| Lambda 演算 | Lambda Calculus | L4 | 基于函数抽象和应用的计算模型 | [Church 1936](https://doi.org/10.2307/2268485) |
| 范畴论 | Category Theory | L4 | 研究数学结构和映射的抽象理论，函数式编程的理论基础 | [Awodey 2010](https://global.oup.com/academic/product/category-theory-9780199237180) |
| 函子 | Functor | L4 | 范畴之间的结构保持映射；在 Rust 中对应 `map` 操作 | [Category Theory](https://global.oup.com/academic/product/category-theory-9780199237180) |
| 单子 | Monad | L4 | 支持 `return` 和 `bind` 运算的自函子范畴；`Option`、`Result`、`Future` 均为单子 | [Haskell Wiki](https://wiki.haskell.org/Monad) |
| 细化类型 | Refinement Type | L4 | 附加谓词约束的类型，如 `{x: i32 | x > 0}` | [Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell-blog/) |
| 模型检测 | Model Checking | L4 | 自动验证有限状态系统是否满足规范的方法 | [Kani Docs](https://model-checking.github.io/kani/) |
| 演绎验证 | Deductive Verification | L4 | 通过逻辑推理证明程序正确性的方法 | [Verus Docs](https://verus-lang.github.io/verus/) |
| 安全标签 | Safety Tags | L4 | 为 unsafe API 标准化的机器可读安全契约标签 (RFC #3842) | [RFC #3842](https://github.com/rust-lang/rfcs/pull/3842) |
| 效果系统 | Effects System | L4 | 在类型系统中跟踪计算效果（如异步、异常、状态）的扩展 | [Rust Project Goals](https://rust-lang.github.io/rust-project-goals/2026/effects.html) |

## L5-L7 生态/未来层术语 (Ecosystem & Future)

| 中文术语 | English Term | 层级 | 定义 | 官方来源 |
|:---|:---|:---:|:---|:---|
| Crate | Crate | L6 | Rust 的编译单元和包管理单位，通过 Cargo 分发 | [Cargo Book](https://doc.rust-lang.org/cargo/) |
| 工作区 | Workspace | L6 | 共享 `Cargo.lock` 和输出目录的一组相关 crates | [Cargo Book](https://doc.rust-lang.org/cargo/reference/workspaces.html) |
| 特性 | Feature | L6 | Cargo 的条件编译和可选依赖机制 | [Cargo Book](https://doc.rust-lang.org/cargo/reference/features.html) |
| 版本 | Edition | L6 | Rust 的语言级兼容性版本（2015/2018/2021/2024） | [Edition Guide](https://doc.rust-lang.org/edition-guide/) |
| 过程宏 crate | Proc-macro Crate | L6 | 编译器在编译期执行的特殊 crate 类型 | [TRPL Ch20.5](https://doc.rust-lang.org/book/ch20-05-macros.html) |
| WebAssembly / WASM | WebAssembly | L6 | 可移植的二进制指令格式，Rust 可编译为 WASM 目标 | [Rust and WebAssembly](https://rustwasm.github.io/book/) |
| WASI | WASI (WebAssembly System Interface) | L6 | WASM 的系统接口标准，分为 Preview 1 (`wasip1`) 和 Preview 2 (`wasip2`) | [WASI Spec](https://github.com/WebAssembly/WASI) |
| 嵌入式 | Embedded | L6 | 无操作系统或 RTOS 环境下的 Rust 开发（`no_std`） | [Embedded Book](https://doc.rust-lang.org/stable/embedded-book/) |
| `no_std` | no_std | L6 | 不链接标准库，仅使用 `core` 和 `alloc` 的运行环境 | [Rust Reference](https://doc.rust-lang.org/reference/crates-and-source-files.html#prelude) |
| 异步闭包 | Async Closure | L7 | `async \|x\| { ... }`，捕获环境并在异步上下文中执行 | [Rust 1.85](https://blog.rust-lang.org/2025/02/20/Rust-1.85.0.html) |
| 生成器 | Gen Block / Generator | L7 | `gen { yield value; }`，同步生成器语法（Rust 2024 预留关键字） | [RFC 3513](https://github.com/rust-lang/rfcs/pull/3513) |
| 常量 trait | Const Trait | L7 | 在 `const fn` 中调用 trait 方法的机制（向稳定化推进） | [Project Goals](https://rust-lang.github.io/rust-project-goals/2025h1/const-trait.html) |
| 异步 Drop | Async Drop | L7 | 支持异步资源释放的析构机制（设计中） | [Compiler Team MCP #727](https://github.com/rust-lang/compiler-team/issues/727) |
| 精确捕获 | Precise Capturing | L7 | `use<..>` 语法，显式控制 `impl Trait` 的生命周期捕获 | [Rust 1.82](https://blog.rust-lang.org/2024/10/17/Rust-1.82.0.html) |
| 精确边界 | RPITIT / RTN | L7 | Return Position Impl Trait In Traits / Return Type Notation | [RFC 2289](https://github.com/rust-lang/rfcs/pull/2289) |

---

## 使用说明

1. **代码注释**: 所有 crates/ 中的 `lib.rs` 和公共 API 应使用英文文档注释（`///`），内部实现可使用中文注释。
2. **概念文件**: concept/ 中的 Markdown 文件保持中文主体，但首次出现关键术语时应标注英文原文，如：**所有权 (Ownership)**。
3. **RFC 和 Issue**: 查阅 Rust 官方资源时，使用英文术语搜索（如 "lifetime elision" 而非 "生命周期省略"）。
4. **扩展贡献**: 如需添加新术语，请遵循"中文术语 | English Term | 层级 | 定义 | 官方来源"的格式，并提供可验证的 URL。

---

> **文档版本**: 1.0
> **对应 Rust 版本**: 1.96.0 (Edition 2024)
> **最后更新**: 2026-05-29
> **状态**: ✅ 术语表创建完成，覆盖 101/100 目标术语
