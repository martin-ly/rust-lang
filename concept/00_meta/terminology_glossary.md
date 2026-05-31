> **说明**：本表为最小国际化 efforts（决策 3-C），聚焦高频术语标准化。所有英文术语与 [TRPL](https://doc.rust-lang.org/book/) 及 [Rust Reference](https://doc.rust-lang.org/reference/) 保持一致，确保学习者能顺利对接 crates.io、RFC、GitHub Issue 等英文生态。
> 
> **标准来源**: TRPL · Rust Reference · std API Docs · Rustnomicon · Async Book · Cargo Book · Edition Guide  
> **对应 Rust 版本**: 1.96.0 (Edition 2024)  
> **状态**: 术语表覆盖 100 个高频术语，L1 → L5+ 分层

# Rust 核心术语英中对照表

---

## 层级说明

本表按认知复杂度将术语分为五个层级，对应 Bloom 分类法从记忆到分析的不同阶段：

- **L1 基础**：入门必读概念，出现在 TRPL 前 10 章，任何 Rust 学习者第一周就会遇到。
- **L2 进阶**：日常编码高频使用，涉及 trait 系统、智能指针、并发原语与错误处理。
- **L3 高级**：涉及 unsafe、异步运行时、宏系统、内存模型与类型系统深层机制。
- **L4 形式化**：程序验证、分离逻辑、类型论及 Rust 官方形式化项目（RustBelt、Miri 等）。
- **L5+ 生态/专家**：生产环境主流 crate、嵌入式、WebAssembly 及跨语言互操作生态。

---

## L1 基础（Foundation）

- **所有权** (Ownership) [L1] — 值在任意时刻有且只有一个所有者 — [TRPL](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)

- **借用** (Borrowing) [L1] — 通过引用临时访问数据而不获取所有权 — [TRPL](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html)

- **生命周期** (Lifetimes) [L1] — 引用必须始终有效的编译期作用域分析 — [TRPL](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)

- **变量绑定** (Variable Binding) [L1] — 将值与变量名关联并可附带可变性 — [TRPL](https://doc.rust-lang.org/book/ch03-01-variables-and-mutability.html)

- **可变性** (Mutability) [L1] — 允许通过 `mut` 关键字修改变量或引用 — [TRPL](https://doc.rust-lang.org/book/ch03-01-variables-and-mutability.html)

- **引用** (Reference) [L1] — 指向值的非空借用指针 `&T` 或 `&mut T` — [TRPL](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html)

- **字符串** (String) [L1] — 堆分配的可变 UTF-8 字符串类型 — [TRPL](https://doc.rust-lang.org/book/ch08-02-strings.html)

- **字符串切片** (String Slice / `str`) [L1] — 不可变的 UTF-8 字符串视图 `&str` — [TRPL](https://doc.rust-lang.org/book/ch04-03-slices.html)

- **切片** (Slice) [L1] — 对连续序列的动态大小视图 `&[T]` — [TRPL](https://doc.rust-lang.org/book/ch04-03-slices.html)

- **结构体** (Struct) [L1] — 命名字段的复合数据类型 — [TRPL](https://doc.rust-lang.org/book/ch05-00-structs.html)

- **枚举** (Enum / Enumeration) [L1] — 可携带数据的标签联合类型 — [TRPL](https://doc.rust-lang.org/book/ch06-00-enums.html)

- **模式匹配** (Pattern Matching) [L1] — 解构值并根据结构执行分支 — [TRPL](https://doc.rust-lang.org/book/ch06-02-match.html)

- **if let** (If Let) [L1] — 对单一模式进行条件解构的语法糖 — [TRPL](https://doc.rust-lang.org/book/ch06-03-if-let.html)

- **match** (Match) [L1] — 穷尽式多分支模式匹配控制流表达式 — [TRPL](https://doc.rust-lang.org/book/ch06-02-match.html)

- **函数** (Function) [L1] — 具名参数化代码块，可接收参数并返回值 — [TRPL](https://doc.rust-lang.org/book/ch03-03-how-functions-work.html)

- **闭包** (Closures) [L1] — 可捕获其环境变量的匿名函数 — [TRPL](https://doc.rust-lang.org/book/ch13-01-closures.html)

- **迭代器** (Iterator) [L1] — 按顺序惰性产生元素的 trait — [TRPL](https://doc.rust-lang.org/book/ch13-02-iterators.html)

- **模块** (Module) [L1] — 通过 `mod` 组织的代码命名空间单元 — [TRPL](https://doc.rust-lang.org/book/ch07-02-defining-modules-to-control-scope-and-privacy.html)

- **包** (Package) [L1] — 包含一个或多个 crate 的 Cargo 项目 — [TRPL](https://doc.rust-lang.org/book/ch07-01-packages-and-crates.html)

- **crate** (Crate) [L1] — Rust 的编译单元和包管理基本单位 — [TRPL](https://doc.rust-lang.org/book/ch07-01-packages-and-crates.html)

- **Cargo** (Cargo) [L1] — Rust 官方的包管理与构建工具 — [Cargo Book](https://doc.rust-lang.org/cargo/)

- **panic** (Panic) [L1] — 不可恢复错误导致的线程栈展开与终止 — [TRPL](https://doc.rust-lang.org/book/ch09-01-unrecoverable-errors-with-panic.html)

- **Result** (Result) [L1] — 显式处理可恢复错误的 `Ok(T)` 或 `Err(E)` — [TRPL](https://doc.rust-lang.org/book/ch09-02-recoverable-errors-with-result.html)

- **Option** (Option) [L1] — 显式处理可选值的 `Some(T)` 或 `None` — [TRPL](https://doc.rust-lang.org/book/ch09-02-recoverable-errors-with-result.html)

- **Vec** (Vec) [L1] — 堆上动态增长的连续数组类型 — [TRPL](https://doc.rust-lang.org/book/ch08-01-vectors.html)

- **HashMap** (HashMap) [L1] — 基于哈希表的无序键值对容器 — [TRPL](https://doc.rust-lang.org/book/ch08-03-hash-maps.html)


## L2 进阶（Intermediate）

- **泛型** (Generics) [L2] — 参数化类型与函数以实现代码复用 — [TRPL](https://doc.rust-lang.org/book/ch10-00-generics.html)

- **特征** (Traits) [L2] — 定义共享行为的接口与类型约束机制 — [TRPL](https://doc.rust-lang.org/book/ch10-02-traits.html)

- **生命周期参数** (Lifetime Parameters) [L2] — 显式标注引用作用域的泛型参数 — [TRPL](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)

- **关联类型** (Associated Types) [L2] — 在 trait 中声明由实现者确定的具体类型 — [TRPL](https://doc.rust-lang.org/book/ch19-03-advanced-traits.html)

- **智能指针** (Smart Pointers) [L2] — 拥有元数据与额外行为的堆分配容器 — [TRPL](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)

- **Box** (Box) [L2] — 在堆上分配值的所有权单所有权指针 — [TRPL](https://doc.rust-lang.org/book/ch15-01-box.html)

- **Rc** (Reference Counted) [L2] — 单线程引用计数的多所有权智能指针 — [TRPL](https://doc.rust-lang.org/book/ch15-04-rc.html)

- **Arc** (Atomic Reference Counted) [L2] — 原子引用计数的多线程共享所有权指针 — [std](https://doc.rust-lang.org/std/sync/struct.Arc.html)

- **RefCell** (RefCell) [L2] — 运行时借用检查的内部可变性容器 — [TRPL](https://doc.rust-lang.org/book/ch15-05-interior-mutability.html)

- **Cell** (Cell) [L2] — 通过移动实现内部可变性的单值容器 — [std](https://doc.rust-lang.org/std/cell/struct.Cell.html)

- **Mutex** (Mutual Exclusion) [L2] — 线程间互斥访问受保护数据的同步原语 — [TRPL](https://doc.rust-lang.org/book/ch16-03-shared-state.html)

- **RwLock** (Read-Write Lock) [L2] — 支持多读单写并发访问的同步原语 — [std](https://doc.rust-lang.org/std/sync/struct.RwLock.html)

- **原子类型** (Atomic Types) [L2] — 提供无锁原子内存操作的整数类型 — [std](https://doc.rust-lang.org/std/sync/atomic/index.html)

- **通道** (Channel) [L2] — 线程间或异步任务间的消息传递机制 — [TRPL](https://doc.rust-lang.org/book/ch16-02-message-passing.html)

- **线程** (Thread) [L2] — 操作系统级别的并发执行单元 — [TRPL](https://doc.rust-lang.org/book/ch16-01-threads.html)

- **Send** (Send) [L2] — 标记可安全跨线程转移所有权的 trait — [TRPL](https://doc.rust-lang.org/book/ch16-04-extensible-concurrency-sync-and-send.html)

- **Sync** (Sync) [L2] — 标记可安全跨线程共享引用的 trait — [TRPL](https://doc.rust-lang.org/book/ch16-04-extensible-concurrency-sync-and-send.html)

- **错误处理** (Error Handling) [L2] — 基于 Result 与 `?` 的显式错误传播机制 — [TRPL](https://doc.rust-lang.org/book/ch09-00-error-handling.html)

- **? 运算符** (Try Operator) [L2] — 自动展开 Result 并在错误时提前返回 — [TRPL](https://doc.rust-lang.org/book/ch09-02-recoverable-errors-with-result.html)

- **From / Into** (From / Into) [L2] — 类型间转换的标准 trait 接口 — [std](https://doc.rust-lang.org/std/convert/trait.From.html)

- **Deref** (Deref) [L2] — 自定义解引用行为以支持自动强转 — [std](https://doc.rust-lang.org/std/ops/trait.Deref.html)

- **Drop** (Drop) [L2] — 值离开作用域时自动执行的析构逻辑 — [std](https://doc.rust-lang.org/std/ops/trait.Drop.html)

- **Copy** (Copy) [L2] — 按位复制后原变量仍可使用的标记 trait — [std](https://doc.rust-lang.org/std/marker/trait.Copy.html)

- **Clone** (Clone) [L2] — 显式深拷贝的 trait，用于堆数据复制 — [std](https://doc.rust-lang.org/std/clone/trait.Clone.html)

- **Eq / PartialEq** (Eq / PartialEq) [L2] — 定义等价关系的比较 trait 组合 — [std](https://doc.rust-lang.org/std/cmp/trait.Eq.html)


## L3 高级（Advanced）

- **不安全 Rust** (Unsafe Rust) [L3] — 使用 `unsafe` 关键字绕过编译器安全检查 — [TRPL](https://doc.rust-lang.org/book/ch20-01-unsafe-rust.html)

- **裸指针** (Raw Pointer) [L3] — 无生命周期与所有权保证的原始指针 — [TRPL](https://doc.rust-lang.org/book/ch20-01-unsafe-rust.html)

- **FFI** (Foreign Function Interface) [L3] — 与 C/C++ 等外部代码互操作的接口 — [TRPL](https://doc.rust-lang.org/book/ch20-01-unsafe-rust.html)

- **内联汇编** (Inline Assembly) [L3] — 在 Rust 中直接嵌入底层汇编指令 — [Reference](https://doc.rust-lang.org/reference/inline-assembly.html)

- **声明宏** (Declarative Macros) [L3] — 基于模式匹配的 `macro_rules!` 代码生成 — [TRPL](https://doc.rust-lang.org/book/ch20-05-macros.html)

- **过程宏** (Procedural Macros) [L3] — 编译期操作 token 流的 Rust 代码 — [TRPL](https://doc.rust-lang.org/book/ch20-05-macros.html)

- **生命周期子类型** (Lifetime Subtyping) [L3] — `'a: 'b` 表示前者存活不短于后者 — [Reference](https://doc.rust-lang.org/reference/subtyping.html)

- **协变** (Covariance) [L3] — 泛型参数随子类型关系同向变化的特性 — [Nomicon](https://doc.rust-lang.org/nomicon/subtyping.html)

- **逆变** (Contravariance) [L3] — 泛型参数随子类型关系反向变化的特性 — [Nomicon](https://doc.rust-lang.org/nomicon/subtyping.html)

- **不变** (Invariance) [L3] — 泛型参数不随子类型关系变化的特性 — [Nomicon](https://doc.rust-lang.org/nomicon/subtyping.html)

- **HRTB** (Higher-Ranked Trait Bounds) [L3] — `for<'a>` 任意生命周期的泛型约束 — [Reference](https://doc.rust-lang.org/reference/trait-bounds.html#higher-ranked-trait-bounds)

- **GAT** (Generic Associated Types) [L3] — 泛型关联类型，trait 内的泛型类型构造 — [RFC 1590](https://rust-lang.github.io/rfcs/1590-generic-associated-types.html)

- **常量泛型** (Const Generics) [L3] — 以编译期常量作为参数的泛型机制 — [Reference](https://doc.rust-lang.org/reference/items/generics.html#const-generics)

- **特化** (Specialization) [L3] — 为更具体类型提供 trait 默认实现覆盖 — [RFC 1210](https://rust-lang.github.io/rfcs/1210-impl-specialization.html)

- **Pin** (Pin) [L3] — 保证值在内存中不被移动的固定包装器 — [std](https://doc.rust-lang.org/std/pin/struct.Pin.html)

- **Future** (Future) [L3] — 代表将来完成的异步计算，可被轮询驱动 — [std](https://doc.rust-lang.org/std/future/trait.Future.html)

- **async / await** (Async / Await) [L3] — 基于状态机的非阻塞异步编程语法 — [TRPL](https://doc.rust-lang.org/book/ch17-00-async-await.html)

- **Stream** (Stream) [L3] — 类似迭代器的异步元素序列 trait — [futures-rs](https://docs.rs/futures/latest/futures/stream/trait.Stream.html)

- **Waker** (Waker) [L3] — 通知异步运行时任务可以继续执行的句柄 — [std](https://doc.rust-lang.org/std/task/struct.Waker.html)

- **Context** (Context) [L3] — 携带 Waker 供异步轮询使用的上下文 — [std](https://doc.rust-lang.org/std/task/struct.Context.html)

- **内存顺序** (Memory Ordering) [L3] — 控制原子操作可见性的语义约束 — [std](https://doc.rust-lang.org/std/sync/atomic/enum.Ordering.html)

- **Relaxed** (Relaxed) [L3] — 最弱的原子内存顺序，仅保证原子性本身 — [std](https://doc.rust-lang.org/std/sync/atomic/enum.Ordering.html)

- **Release** (Release) [L3] — 写操作使用，保证此前写对获取侧可见 — [std](https://doc.rust-lang.org/std/sync/atomic/enum.Ordering.html)

- **Acquire** (Acquire) [L3] — 读操作使用，保证能看到释放侧先前写 — [std](https://doc.rust-lang.org/std/sync/atomic/enum.Ordering.html)

- **SeqCst** (Sequentially Consistent) [L3] — 最强顺序一致性，所有线程观察顺序一致 — [std](https://doc.rust-lang.org/std/sync/atomic/enum.Ordering.html)


## L4 形式化（Formal Methods）

- **分离逻辑** (Separation Logic) [L4] — 扩展 Hoare 逻辑以推理共享可变状态 — [Reynolds 2002](https://www.cs.cmu.edu/~jcr/seplogic.pdf)

- **线性逻辑** (Linear Logic) [L4] — 资源敏感、假设被消费而非重复的逻辑 — [Girard 1987](https://girard.perso.math.cnrs.fr/linear.pdf)

- **Hoare 逻辑** (Hoare Logic) [L4] — 基于前后置条件的形式化程序推理系统 — [Hoare 1969](https://doi.org/10.1145/363235.363259)

- **操作语义** (Operational Semantics) [L4] — 通过抽象机器步骤定义程序执行 — [Winskel 1993](https://mitpress.mit.edu/9780262731034)

- **指称语义** (Denotational Semantics) [L4] — 将程序映射到数学对象的语义方法 — [Winskel 1993](https://mitpress.mit.edu/9780262731034)

- **公理语义** (Axiomatic Semantics) [L4] — 基于逻辑公理推导程序正确性 — [Winskel 1993](https://mitpress.mit.edu/9780262731034)

- **类型论** (Type Theory) [L4] — 将类型作为数学对象研究的逻辑基础 — [TAPL](https://www.cis.upenn.edu/~bcpierce/tapl/)

- **子类型** (Subtyping) [L4] — 类型间替代关系的层级结构 — [Reference](https://doc.rust-lang.org/reference/subtyping.html)

- **类型推断** (Type Inference) [L4] — 编译器自动推导表达式类型的机制 — [Reference](https://doc.rust-lang.org/reference/type-inference.html)

- **RustBelt** (RustBelt) [L4] — 在 Iris 中形式化验证 Rust 不安全代码的项目 — [POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)

- **Iris** (Iris) [L4] — 高阶并发分离逻辑框架，RustBelt 的理论基础 — [RustBelt](https://plv.mpi-sws.org/rustbelt/)

- **Kani** (Kani) [L4] — Rust 代码的自动模型检测工具 — [Kani Docs](https://model-checking.github.io/kani/)

- **Verus** (Verus) [L4] — 支持 Rust 的演绎验证与证明助手 — [Verus Docs](https://verus-lang.github.io/verus/)

- **Miri** (Miri) [L4] — 检测未定义行为的 Rust 中间表示解释器 — [Miri](https://github.com/rust-lang/miri)

- **Tree Borrows** (Tree Borrows) [L4] — Miri 采用的内存别名模型 — [Miri](https://github.com/rust-lang/miri)


## L5+ 生态/专家（Ecosystem & Expert）

- **Tokio** (Tokio) [L5+] — 异步 Rust 的运行时与网络 IO 生态核心 — [Tokio](https://tokio.rs/)

- **Rayon** (Rayon) [L5+] — 数据并行计算的 work-stealing 线程池库 — [docs.rs](https://docs.rs/rayon/latest/rayon/)

- **Serde** (Serde) [L5+] — Rust 生态通用的序列化与反序列化框架 — [serde.rs](https://serde.rs/)

- **Protobuf** (Protocol Buffers) [L5+] — Google 的二进制数据交换格式与代码生成 — [protobuf.dev](https://protobuf.dev/)

- **gRPC** (gRPC) [L5+] — 基于 HTTP/2 的高性能远程过程调用框架 — [grpc.io](https://grpc.io/)

- **WebAssembly** (WebAssembly / WASM) [L5+] — 可移植二进制指令格式，Rust 可编译为目标 — [Rust and WASM](https://rustwasm.github.io/book/)

- **WASI** (WASI) [L5+] — WebAssembly 的系统接口标准规范 — [WASI Spec](https://github.com/WebAssembly/WASI)

- **嵌入式** (Embedded) [L5+] — 无操作系统或 RTOS 环境下的 Rust 开发 — [Embedded Book](https://doc.rust-lang.org/stable/embedded-book/)

- **实时系统** (Real-Time Systems) [L5+] — 有严格时间约束的确定性执行环境 — [Embedded Book](https://doc.rust-lang.org/stable/embedded-book/)

- **no_std** (no_std) [L5+] — 不链接标准库，仅使用 `core` 的运行环境 — [Reference](https://doc.rust-lang.org/reference/crates-and-source-files.html#prelude)


---

## 验证记录

以下术语经与 TRPL 及官方文档原文交叉核对，已排除常见误译：

| 中文术语 | 官方英文 | 常见误译 | 状态 |
|:---|:---|:---|:---:|
| 所有权 | **Ownership** | Possession | ✅ |
| 借用 | **Borrowing** | Lending | ✅ |
| 生命周期 | **Lifetimes** | Life Cycle | ✅ |
| 特征 | **Traits** | Characteristics | ✅ |
| 闭包 | **Closures** | Lambda | ✅ |
| 枚举 | **Enumerations / Enums** | — | ✅ |
| 模式匹配 | **Pattern Matching** | — | ✅ |
| 泛型 | **Generics** | — | ✅ |
| 智能指针 | **Smart Pointers** | — | ✅ |
| 不安全 Rust | **Unsafe Rust** | — | ✅ |

## 使用建议

1. **代码注释**：所有 `crates/` 中的 `lib.rs` 和公共 API 应使用英文文档注释（`///`），内部实现可使用中文注释；首次出现的关键术语请使用本表标准英文。
2. **概念文件**：`concept/` 与 `knowledge/` 中的 Markdown 保持中文主体，但首次出现关键术语时应标注英文原文，如：**所有权 (Ownership)**。
3. **RFC 与 Issue**：查阅 Rust 官方资源时，使用英文术语搜索（如 "lifetime elision" 而非 "生命周期省略"）。
4. **扩展贡献**：如需添加新术语，请遵循 `- **中文** (English) [层级] — 定义 — [来源](链接)` 的格式，并提供可验证的官方 URL。

---

> **文档版本**: 2.0  
> **术语总数**: 100  
> **与 TRPL 一致率**: 100%（所有 L1~L3 术语均与 TRPL / 官方 Reference 英文原文一致）  
> **最后更新**: 2026-05-31

---

## 术语快速索引（按拼音排序）

| 拼音 | 中文术语 | English Term | 层级 |
|:---|:---|:---|:---:|
| ? | ? 运算符 | Try Operator | L2 |
| A | Acquire | Acquire | L3 |
| A | Arc | Atomic Reference Counted | L2 |
| A | async / await | Async / Await | L3 |
| B | Box | Box | L2 |
| C | Cargo | Cargo | L1 |
| C | Cell | Cell | L2 |
| C | Clone | Clone | L2 |
| C | Context | Context | L3 |
| C | Copy | Copy | L2 |
| C | crate | Crate | L1 |
| D | Deref | Deref | L2 |
| D | Drop | Drop | L2 |
| E | Eq / PartialEq | Eq / PartialEq | L2 |
| F | FFI | Foreign Function Interface | L3 |
| F | From / Into | From / Into | L2 |
| F | Future | Future | L3 |
| G | GAT | Generic Associated Types | L3 |
| G | gRPC | gRPC | L5+ |
| H | HashMap | HashMap | L1 |
| H | Hoare 逻辑 | Hoare Logic | L4 |
| H | HRTB | Higher-Ranked Trait Bounds | L3 |
| I | if let | If Let | L1 |
| I | Iris | Iris | L4 |
| K | Kani | Kani | L4 |
| M | match | Match | L1 |
| M | Miri | Miri | L4 |
| M | Mutex | Mutual Exclusion | L2 |
| N | no_std | no_std | L5+ |
| O | Option | Option | L1 |
| P | panic | Panic | L1 |
| P | Pin | Pin | L3 |
| P | Protobuf | Protocol Buffers | L5+ |
| R | Rayon | Rayon | L5+ |
| R | Rc | Reference Counted | L2 |
| R | RefCell | RefCell | L2 |
| R | Relaxed | Relaxed | L3 |
| R | Release | Release | L3 |
| R | Result | Result | L1 |
| R | RustBelt | RustBelt | L4 |
| R | RwLock | Read-Write Lock | L2 |
| S | Send | Send | L2 |
| S | SeqCst | Sequentially Consistent | L3 |
| S | Serde | Serde | L5+ |
| S | Stream | Stream | L3 |
| S | Sync | Sync | L2 |
| T | Tokio | Tokio | L5+ |
| T | Tree Borrows | Tree Borrows | L4 |
| V | Vec | Vec | L1 |
| V | Verus | Verus | L4 |
| W | Waker | Waker | L3 |
| W | WASI | WASI | L5+ |
| W | WebAssembly | WebAssembly / WASM | L5+ |
| 不 | 不变 | Invariance | L3 |
| 不 | 不安全 Rust | Unsafe Rust | L3 |
| 借 | 借用 | Borrowing | L1 |
| 公 | 公理语义 | Axiomatic Semantics | L4 |
| 关 | 关联类型 | Associated Types | L2 |
| 内 | 内存顺序 | Memory Ordering | L3 |
| 内 | 内联汇编 | Inline Assembly | L3 |
| 函 | 函数 | Function | L1 |
| 分 | 分离逻辑 | Separation Logic | L4 |
| 切 | 切片 | Slice | L1 |
| 包 | 包 | Package | L1 |
| 协 | 协变 | Covariance | L3 |
| 原 | 原子类型 | Atomic Types | L2 |
| 变 | 变量绑定 | Variable Binding | L1 |
| 可 | 可变性 | Mutability | L1 |
| 声 | 声明宏 | Declarative Macros | L3 |
| 子 | 子类型 | Subtyping | L4 |
| 字 | 字符串 | String | L1 |
| 字 | 字符串切片 | String Slice / `str` | L1 |
| 实 | 实时系统 | Real-Time Systems | L5+ |
| 嵌 | 嵌入式 | Embedded | L5+ |
| 常 | 常量泛型 | Const Generics | L3 |
| 引 | 引用 | Reference | L1 |
| 所 | 所有权 | Ownership | L1 |
| 指 | 指称语义 | Denotational Semantics | L4 |
| 操 | 操作语义 | Operational Semantics | L4 |
| 智 | 智能指针 | Smart Pointers | L2 |
| 枚 | 枚举 | Enum / Enumeration | L1 |
| 模 | 模块 | Module | L1 |
| 模 | 模式匹配 | Pattern Matching | L1 |
| 泛 | 泛型 | Generics | L2 |
| 特 | 特化 | Specialization | L3 |
| 特 | 特征 | Traits | L2 |
| 生 | 生命周期 | Lifetimes | L1 |
| 生 | 生命周期参数 | Lifetime Parameters | L2 |
| 生 | 生命周期子类型 | Lifetime Subtyping | L3 |
| 类 | 类型推断 | Type Inference | L4 |
| 类 | 类型论 | Type Theory | L4 |
| 线 | 线性逻辑 | Linear Logic | L4 |
| 线 | 线程 | Thread | L2 |
| 结 | 结构体 | Struct | L1 |
| 裸 | 裸指针 | Raw Pointer | L3 |
| 过 | 过程宏 | Procedural Macros | L3 |
| 迭 | 迭代器 | Iterator | L1 |
| 逆 | 逆变 | Contravariance | L3 |
| 通 | 通道 | Channel | L2 |
| 错 | 错误处理 | Error Handling | L2 |
| 闭 | 闭包 | Closures | L1 |

---
