# Rust 概念速查卡片（Quick Reference）
>
> **EN**: Quick Reference
> **Summary**: Quick Reference. Core Rust concept.
>
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **受众**: [进阶]
> **Bloom 层级**: 记忆 → 应用
> **定位**：面试前/编码时的快速查阅手册。每个核心概念"一页纸"——定义 + 代码 + 错误码 + 关联概念。
> **使用方式**：按 Ctrl+F 搜索概念名，或按字母序浏览。
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>
> **来源**: [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference](https://doc.rust-lang.org/reference/)
---

## 📑 目录

- [Rust 概念速查卡片（Quick Reference）](#rust-概念速查卡片quick-reference)
  - [📑 目录](#-目录)
  - [一、核心概念速查（按字母序） 来源: 速查内容基于 Rust Reference / The Rust Programming Language / Rustonomicon / RFCs; 概念定义与 concept / 目录核心文件保持一致](#一核心概念速查按字母序-来源-速查内容基于-rust-reference--the-rust-programming-language--rustonomicon--rfcs-概念定义与-concept--目录核心文件保持一致)
    - [A](#a)
      - [`async` / `await`](#async--await)
      - [`Arc<T>`](#arct)
    - [B](#b)
      - [`Box<T>`](#boxt)
      - [Borrowing（借用）](#borrowing借用)
      - [Builder Pattern](#builder-pattern)
    - [C](#c)
      - [`const` / `const fn`](#const--const-fn)
      - [`Copy` Trait](#copy-trait)
      - [`crossbeam` / Channel](#crossbeam--channel)
    - [D](#d)
      - [`Drop` Trait](#drop-trait)
      - [`dyn Trait`](#dyn-trait)
    - [E](#e)
      - [`enum`（代数数据类型）](#enum代数数据类型)
      - [Error Handling（`Result<T, E>`）](#error-handlingresultt-e)
    - [F](#f)
      - [`Future` Trait](#future-trait)
      - [FFI（Foreign Function Interface）](#ffiforeign-function-interface)
    - [G](#g)
      - [`Generic<T>`](#generict)
      - [`Generic Associated Types (GATs)`](#generic-associated-types-gats)
    - [H](#h)
      - [`HashMap<K, V>`](#hashmapk-v)
      - [`HRTB`（Higher-Ranked Trait Bounds）](#hrtbhigher-ranked-trait-bounds)
    - [I](#i)
      - [`impl Trait`](#impl-trait)
      - [Interior Mutability（内部可变性）](#interior-mutability内部可变性)
    - [L](#l)
      - [Lifetimes（生命周期）](#lifetimes生命周期)
      - [`Lock` / `Mutex<T>`](#lock--mutext)
    - [M](#m)
      - [`macro_rules!`](#macro_rules)
      - [`Move` Semantics](#move-semantics)
    - [N](#n)
      - [Newtype Pattern](#newtype-pattern)
      - [`no_std`](#no_std)
    - [O](#o)
      - [`Option<T>`](#optiont)
      - [`Ownership`](#ownership)
    - [P](#p)
      - [`Pin<P<T>>`](#pinpt)
      - [`PhantomData<T>`](#phantomdatat)
    - [R](#r)
      - [`Rc<T>` / `Arc<T>`](#rct--arct)
      - [`Result<T, E>`](#resultt-e)
    - [S](#s)
      - [`Send` / `Sync`](#send--sync)
      - [`Sized` / `?Sized`](#sized--sized)
      - [`std::mem`](#stdmem)
    - [T](#t)
      - [`Trait`](#trait)
      - [Typestate Pattern](#typestate-pattern)
    - [U](#u)
      - [`Unsafe Rust`](#unsafe-rust)
    - [V](#v)
      - [`Vec<T>`](#vect)
    - [W](#w)
      - [`Waker`](#waker)
  - [二、编译错误码速查](#二编译错误码速查)
  - [三、模式选择决策树（速查版）](#三模式选择决策树速查版)
  - [四、跨语言对照速查](#四跨语言对照速查)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
    - [反命题与边界](#反命题与边界)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：本文档《Rust 概念速查卡片（Quick Reference）》在 Rust 知识体系中属于哪一层级的元数据？（理解层）](#测验-1本文档rust-概念速查卡片quick-reference在-rust-知识体系中属于哪一层级的元数据理解层)
    - [测验 2：《Rust 概念速查卡片（Quick Reference）》的主要用途是什么？（理解层）](#测验-2rust-概念速查卡片quick-reference的主要用途是什么理解层)
    - [测验 3：元数据层文档能否替代 L1-L7 的核心概念学习？（理解层）](#测验-3元数据层文档能否替代-l1-l7-的核心概念学习理解层)

## 一、核心概念速查（按字母序） 来源: 速查内容基于 Rust Reference / [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html) / [Rustonomicon](https://doc.rust-lang.org/nomicon/) / RFCs; 概念定义与 concept / 目录核心文件保持一致

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/) / 2025; Rust Reference / 2025; TRPL / 2024** 本速查表的所有概念定义均来源于 Rust 官方文档和学术论文。

### A

#### `async` / `await`

**定义**: 协作式多任务的语法糖，`async fn` 编译为 `enum Future` 状态机
**代码**:

```rust
async fn foo() -> i32 { 42 }
// 等价于: fn foo() -> impl Future<Output = i32>
```

**常见错误**: 在 `async` 块中使用阻塞 IO → 阻塞整个执行器线程
**关联**: Future · Pin · Waker · Tokio
**深入**: [`02_async.md`](../../03_advanced/01_async/02_async.md)

#### `Arc<T>`

**定义**: 原子引用计数智能指针，线程安全的共享所有权
**代码**: `let a = Arc::new(Mutex::new(0)); let b = Arc::clone(&a);`
**常见错误**: `Arc<RefCell<T>>` — RefCell 不是 Sync，不能跨线程共享
**关联**: Rc · Mutex · Send/Sync
**深入**: [`03_memory_management.md`](../../02_intermediate/02_memory_management/03_memory_management.md)

### B

#### `Box<T>`

**定义**: 堆分配的唯一所有权指针
**代码**: `let b = Box::new(5);`
**常见错误**: `Box<dyn Trait>` 是胖指针，大小不固定
**关联**: Own · Drop · 递归类型
**深入**: [`01_ownership.md`](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md)

#### Borrowing（借用）

**定义**: 所有权的临时授权，不改变资源最终归属
**规则**: 任意时刻，要么一个 `&mut T`，要么任意多个 `&T`
**代码**:

```rust,ignore
let r = &x; let r2 = &x;     // ✅ 共享借用
let r = &x; let r2 = &mut x; // ❌ E0502
```

**关联**: 生命周期 · 分离逻辑 · 分数权限
**深入**: [`02_borrowing.md`](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md)

#### Builder Pattern

**定义**: 用方法链逐步构造复杂对象，编译期保证必填字段
**代码**:

```rust,ignore
HttpRequestBuilder::new()
    .method("GET")
    .url("/")
    .build()  // 编译错误如果缺少必填字段
```

**关联**: 消费型方法链 · 类型状态
**深入**: [`02_patterns.md`](../../06_ecosystem/02_patterns.md)

[来源: [Rust Reference — Structs](https://doc.rust-lang.org/reference/items/structs.html) · [TRPL — Using Structs](https://doc.rust-lang.org/book/ch05-00-structs.html)]

### C

#### `const` / `const fn`

**定义**: 编译期常量 / 编译期可执行的函数
**代码**: `const N: usize = 10; const fn square(n: i32) -> i32 { n * n }`
**常见错误**: `const` 变量在多处使用会被内联复制，而非共享引用
**关联**: Const Generics · 编译期计算
**深入**: [`02_generics.md`](../../02_intermediate/01_generics/02_generics.md)

#### `Copy` Trait

**定义**: 标记类型可以按位复制，赋值后原变量仍可用
**代码**:

```rust
#[derive(Copy, Clone)]
struct Point { x: i32, y: i32 }
let p1 = Point { x: 1, y: 2 };
let p2 = p1;  // p1 仍可用（Copy）
```

**常见错误**: 为含 `String`/`Vec` 的类型实现 Copy → 编译错误 E0204
**关联**: Move · Clone · 仿射逻辑 weakening
**深入**: [`01_ownership.md`](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md)

#### `crossbeam` / Channel

**定义**: 跨线程通信通道（MPSC），所有权通过通道转移
**代码**: `let (tx, rx) = crossbeam::channel(); tx.send(data); let received = rx.recv();`
**关联**: Send · Sync · CSP
**深入**: [`01_concurrency.md`](../../03_advanced/00_concurrency/01_concurrency.md)

[来源: [Rust Reference — const and static](https://doc.rust-lang.org/reference/items/constant-items.html) · [TRPL — Constants](https://doc.rust-lang.org/book/ch03-01-variables-and-mutability.html#constants)]

### D

#### `Drop` Trait

**定义**: 资源释放的钩子，值离开作用域时自动调用
**代码**:

```rust,ignore
impl Drop for MyType {
    fn drop(&mut self) { println!("Dropping!"); }
}
```

**常见错误**: `mem::forget` 或循环引用（Rc）会阻止 Drop 执行
**关联**: RAII · 所有权 · 资源管理
**深入**: [`01_ownership.md`](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md)

#### `dyn Trait`

**定义**: Trait 对象，动态分发，运行时通过 vtable 调用方法
**代码**: `let items: Vec<Box<dyn Drawable>> = vec![Box::new(Circle), Box::new(Rect)];`
**常见错误**: `dyn Trait` 要求 Trait 是对象安全的（无泛型方法、无 Self: Sized bound）
**关联**: enum + match · 静态/动态分发 · vtable
**深入**: [`04_type_system.md`](../../01_foundation/02_type_system/04_type_system.md)

[来源: [Rust Reference — Drop](https://doc.rust-lang.org/reference/destructors.html) · [TRPL — Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)]

### E

#### `enum`（代数数据类型）

**定义**: 和类型（Sum Type），变体间互斥，编译期穷尽检查
**代码**:

```rust
enum Option<T> { None, Some(T) }
enum Result<T, E> { Ok(T), Err(E) }
```

**常见错误**: `match` 未穷尽 → 编译错误 E0004
**关联**: 模式匹配 · ADT · 和类型
**深入**: [`04_type_system.md`](../../01_foundation/02_type_system/04_type_system.md)

#### Error Handling（`Result<T, E>`）

**定义**: 显式错误传播，`?` 运算符自动展开/传播错误
**代码**:

```rust,ignore
fn read_file(path: &str) -> Result<String, io::Error> {
    let mut file = File::open(path)?;  // ? 传播错误
    let mut buf = String::new();
    file.read_to_string(&mut buf)?;
    Ok(buf)
}
```

**关联**: Option · panic · Try trait
**深入**: [`04_error_handling.md`](../../02_intermediate/03_error_handling/04_error_handling.md)

### F

#### `Future` Trait

**定义**: 异步计算的抽象，`poll` 方法驱动状态机推进
**代码**:

```rust,ignore
trait Future {
    type Output;
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output>;
}
```

**关联**: async/await · Pin · Waker · Executor
**深入**: [`02_async.md`](../../03_advanced/01_async/02_async.md)

#### FFI（Foreign Function Interface）

**定义**: 与其他语言（主要是 C）互操作的边界
**代码**:

```rust,ignore
extern "C" {
    fn sqrt(x: f64) -> f64;
}
```

**常见错误**: ABI 不匹配、内存布局差异、未初始化的悬垂指针
**关联**: unsafe · repr(C) · 内存布局
**深入**: [`03_unsafe.md`](../../03_advanced/02_unsafe/03_unsafe.md)

### G

#### `Generic<T>`

**定义**: 参数多态，编译期单态化为具体类型，零运行时开销
**代码**:

```rust
fn identity<T>(x: T) -> T { x }
// 单态化后生成: fn identity_i32(x: i32) -> i32 { x }
```

**常见错误**: 过度泛化导致编译时间爆炸、二进制膨胀
**关联**: Trait bounds · 单态化 · 参数性定理
**深入**: [`02_generics.md`](../../02_intermediate/01_generics/02_generics.md)

#### `Generic Associated Types (GATs)`

**定义**: 泛型关联类型，允许关联类型携带自己的泛型参数
**代码**:

```rust
trait LendingIterator {
    type Item<'a> where Self: 'a;
    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}
```

**关联**: 关联类型 · 生命周期泛型 · HKT 模拟
**深入**: [`02_generics.md`](../../02_intermediate/01_generics/02_generics.md)

### H

#### `HashMap<K, V>`

**定义**: 基于 Robin Hood 哈希的哈希表，默认使用 SipHash 防 HashDoS
**代码**: `let mut map = HashMap::new(); map.insert("key", 42);`
**常见错误**: 自定义类型作 Key 需实现 `Eq + Hash`；修改已插入 Key 的哈希值 → UB
**关联**: 集合类型 · 哈希 · BTreeMap
**深入**: [`04_type_system.md`](../../01_foundation/02_type_system/04_type_system.md)

#### `HRTB`（Higher-Ranked Trait Bounds）

**定义**: 高阶 Trait Bound，`for<'a>` 表示对所有生命周期成立
**代码**: `fn foo<F>(f: F) where F: for<'a> Fn(&'a str) -> &'a str;`
**关联**: 生命周期 · System F ∀ · 全称量化
**深入**: [`02_type_theory.md`](../../04_formal/00_type_theory/02_type_theory.md)

### I

#### `impl Trait`

**定义**: 抽象返回类型，调用者只知道实现了某 Trait，不知道具体类型
**代码**:

```rust
fn make_iter() -> impl Iterator<Item = i32> {
    vec![1, 2, 3].into_iter()
}
```

**常见错误**: `impl Trait` 在 Trait 定义中不稳定（需 RPITIT）；不能作为结构体字段类型
**关联**: dyn Trait · 存在类型 · 零成本抽象
**深入**: [`04_type_system.md`](../../01_foundation/02_type_system/04_type_system.md)

#### Interior Mutability（内部可变性）

**定义**: 在不可变引用背后修改数据，运行时检查借用规则
**选择矩阵**:

| 类型 | 线程安全 | 运行时检查 | 使用场景 |
|:---|:---|:---|:---|
| `Cell<T>` | ❌ | 无（按位替换）| `T: Copy`，简单值替换 |
| `RefCell<T>` | ❌ | 借用计数（panic）| 单线程，复杂借用模式 |
| `Mutex<T>` | ✅ | 锁 | 多线程互斥 |
| `RwLock<T>` | ✅ | 锁 | 多读单写 |
| `Atomic*` | ✅ | 硬件指令 | 整数/指针的原子操作 |

[来源: [Rust Reference — Interior Mutability](https://doc.rust-lang.org/reference/interior-mutability.html) · [TRPL — Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html)]

**深入**: [`03_memory_management.md`](../../02_intermediate/02_memory_management/03_memory_management.md)

### L

#### Lifetimes（生命周期）

**定义**: 引用的有效期限，编译期约束引用不悬垂
**代码**:

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

**常见错误**: 返回局部变量的引用 → E0597
**关联**: 借用 · 区域类型 · 子类型
**深入**: [`03_lifetimes.md`](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md)

#### `Lock` / `Mutex<T>`

**定义**: 互斥锁，保证同一时间只有一个线程访问数据
**代码**: `let data = Mutex::new(0); *data.lock().unwrap() += 1;`
**常见错误**: 死锁（嵌套锁顺序不一致）；`MutexGuard` 跨 await → 编译错误
**关联**: Send/Sync · 内部可变性 · 死锁
**深入**: [`01_concurrency.md`](../../03_advanced/00_concurrency/01_concurrency.md)

### M

#### `macro_rules!`

**定义**: 声明宏，基于模式匹配的语法扩展
**代码**:

```rust
macro_rules! vec {
    ($($x:expr),*) => {{
        let mut temp_vec = Vec::new();
        $(temp_vec.push($x);)*
        temp_vec
    }};
}
```

**常见错误**: 宏展开后的优先级问题（需用 `{}` 包裹）；递归宏深度溢出
**关联**: 过程宏 · 卫生宏 · 元编程
**深入**: [`04_macros.md`](../../03_advanced/03_proc_macros/04_macros.md)

#### `Move` Semantics

**定义**: 所有权转移，原变量失效，目标变量获得资源控制权
**代码**:

```rust
let s1 = String::from("hello");
let s2 = s1;  // s1 被 move，之后不可用
// println!("{}", s1); // E0382
```

**关联**: Copy · Drop · 线性逻辑
**深入**: [`01_ownership.md`](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md)

### N

#### Newtype Pattern

**定义**: 用元组结构体包装已有类型，实现零成本抽象的类型区分
**代码**:

```rust
struct Meters(u32);
struct Kilometers(u32);
// Meters 和 Kilometers 是不同的类型，不能混用
```

**关联**: 类型安全 · 零大小类型 · 封装
**深入**: [`02_patterns.md`](../../06_ecosystem/02_patterns.md)

#### `no_std`

**定义**: 不使用标准库，仅依赖 `core` 和 `alloc`，用于嵌入式/WASM
**代码**: `#![no_std]`
**常见错误**: `no_std` 环境下没有 `std::io`、`std::thread`；需使用 `alloc::vec::Vec`
**关联**: 嵌入式 · 裸机 · libcore
**深入**: [`04_application_domains.md`](../../06_ecosystem/04_application_domains.md)

### O

#### `Option<T>`

**定义**: 可能为空的值，`Some(T)` 或 `None`，强制调用者处理空值
**代码**:

```rust
let x: Option<i32> = Some(5);
let y = x.unwrap_or(0);  // 安全取值
```

**关联**: Result · ? 运算符 · Monad
**深入**: [`04_error_handling.md`](../../02_intermediate/03_error_handling/04_error_handling.md)

#### `Ownership`

**定义**: 每个值有且仅有一个 owner，owner 离开作用域时值被 drop
**核心规则**:

1. 每个值有唯一 owner
2. 值可以 move 到新的 owner
3. owner 离开作用域 → 值被 drop
**关联**: Move · Borrow · Drop · RAII
**深入**: [`01_ownership.md`](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md)

### P

#### `Pin<P<T>>`

**定义**: 保证 `T` 的内存地址不变，用于自引用结构
**代码**:

```rust,ignore
let mut future = Box::pin(my_async_fn());
let _ = future.as_mut().poll(cx);
```

**常见错误**: `Unpin` 类型上 Pin 无实际约束；手动创建 Pin 需 unsafe
**关联**: async · Future · 自引用 · !Unpin
**深入**: [`02_async.md`](../../03_advanced/01_async/02_async.md)

#### `PhantomData<T>`

**定义**: 零大小类型，用于向编译器标记逻辑上的类型关联
**代码**:

```rust,ignore
struct MyPtr<T> { ptr: *mut (), _marker: PhantomData<T> }
// 告诉编译器 MyPtr<T> 拥有 T 的 variance
```

**关联**: 方差 · 类型标记 · 零大小类型
**深入**: [`02_generics.md`](../../02_intermediate/01_generics/02_generics.md)

### R

#### `Rc<T>` / `Arc<T>`

**定义**: 引用计数共享所有权，`Arc` 是 `Rc` 的原子化线程安全版本
**选择**: 单线程 → `Rc<T>`；多线程 → `Arc<T>`
**常见错误**: `Rc` 循环引用 → 内存泄漏；`Arc` 性能开销来自原子操作
**关联**: 共享所有权 · 内部可变性 · 弱引用
**深入**: [`03_memory_management.md`](../../02_intermediate/02_memory_management/03_memory_management.md)

#### `Result<T, E>`

**定义**: 可能失败的操作结果，`Ok(T)` 或 `Err(E)`
**代码**:

```rust,ignore
fn may_fail() -> Result<i32, String> {
    if random() { Ok(42) } else { Err("failed".to_string()) }
}
let val = may_fail()?;  // ? 传播错误
```

**关联**: Option · ? 运算符 · panic
**深入**: [`04_error_handling.md`](../../02_intermediate/03_error_handling/04_error_handling.md)

### S

#### `Send` / `Sync`

**定义**: Auto Trait，标记类型的线程安全属性

- `T: Send` — T 可以安全地跨线程转移所有权
- `T: Sync` — `&T` 可以安全地跨线程共享（即 `&T: Send`）
**常见错误**: 手动 `unsafe impl Send for MyType` 需证明线程安全
**关联**: 并发 · 所有权 · 数据竞争
**深入**: [`01_concurrency.md`](../../03_advanced/00_concurrency/01_concurrency.md)

[来源: [Rust Reference — Auto Traits](https://doc.rust-lang.org/reference/special-types-and-traits.html) · [TRPL — Concurrency](https://doc.rust-lang.org/book/ch16-00-concurrency.html)]

#### `Sized` / `?Sized`

**定义**: `Sized` 标记编译期已知大小的类型；`?Sized` 允许动态大小类型（DST）
**代码**: `fn foo<T: ?Sized>(x: &T) { }` — 可接受 `&str`、`&[i32]`、`&dyn Trait`
**常见错误**: 泛型参数默认 `Sized`，需显式 `?Sized` 才能使用 trait object
**关联**: DST · 胖指针 · vtable
**深入**: [`02_generics.md`](../../02_intermediate/01_generics/02_generics.md)

#### `std::mem`

**定义**: 内存操作原语，包括 `replace`、`swap`、`take`、`drop`、`forget`
**常见错误**: `mem::forget` 跳过 Drop → 资源泄漏；`mem::transmute` 最危险，破坏类型系统
**关联**: unsafe · 内存布局 · ManuallyDrop
**深入**: [`03_unsafe.md`](../../03_advanced/02_unsafe/03_unsafe.md)

### T

#### `Trait`

**定义**: 行为抽象，类似 Java Interface / Haskell Typeclass，但基于组合而非继承
**代码**:

```rust,ignore
trait Drawable { fn draw(&self); }
impl Drawable for Circle { fn draw(&self) { ... } }
```

**关键限制**: Orphan Rule — 不能为外部类型实现外部 Trait
**关联**: 泛型 · dyn Trait · 关联类型 · 特化
**深入**: [`01_traits.md`](../../02_intermediate/00_traits/01_traits.md)

#### Typestate Pattern

**定义**: 用泛型将运行时状态编码为编译期类型，状态转换由类型系统保证
**代码**:

```rust,ignore
struct Door<State> { _marker: PhantomData<State> }
struct Closed; struct Open;
impl Door<Closed> { fn open(self) -> Door<Open> { ... } }
// 只有 Door<Closed> 能调用 open()
```

**关联**: PhantomData · 泛型 · 编译期状态机
**深入**: [`02_patterns.md`](../../06_ecosystem/02_patterns.md)

### U

#### `Unsafe Rust`

**定义**: 打开 5 个特定逃逸门：原始指针、unsafe 函数、extern 函数、静态变量、union
**代码**:

```rust,ignore
unsafe {
    let raw_ptr = &mut x as *mut i32;
    *raw_ptr = 42;  // 编译器不检查别名规则
}
```

**核心原则**: unsafe 块的安全性由程序员保证，但类型系统仍有效
**关联**: 原始指针 · Miri · FFI · Safety Contract
**深入**: [`03_unsafe.md`](../../03_advanced/02_unsafe/03_unsafe.md)

### V

#### `Vec<T>`

**定义**: 动态数组，堆分配，连续内存，O(1) 随机访问，O(1) 平摊尾部插入
**常见操作**:

```rust
let mut v = vec![1, 2, 3];
v.push(4);           // O(1) amortized
let x = v[0];        // O(1)
v.insert(1, 5);      // O(n)
```

**常见错误**: `v[i]` 越界 → panic；迭代时修改 → 编译错误 E0499
**关联**: Slice · 迭代器 · 集合类型
**深入**: [`04_type_system.md`](../../01_foundation/02_type_system/04_type_system.md)

### W

#### `Waker`

**定义**: 异步任务的唤醒机制，`Future` 挂起时注册 Waker，事件就绪时调用
**代码**:

```rust,ignore
fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    if !self.is_ready() {
        self.waker = Some(cx.waker().clone());  // 注册 Waker
        return Poll::Pending;
    }
    Poll::Ready(self.result)
}
```

**关联**: Future · async · Executor · 协作式调度
**深入**: [`02_async.md`](../../03_advanced/01_async/02_async.md)

---

## 二、编译错误码速查

| 错误码 | 含义 | 触发场景 | 解决方向 | 深入文件 |
|:---|:---|:---|:---|:---|
| **E0382** | borrow of moved value | Move 后使用原变量 | 改用 `clone()` 或重新设计所有权 | [01_ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) |
| **E0499** | cannot borrow as mutable more than once | 同时存在两个 `&mut T` | 缩小借用作用域或使用内部可变性 | [02_borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) |
| **E0502** | cannot borrow as mutable because borrowed as immutable | `&T` 和 `&mut T` 共存 | 确保 `&T` 在 `&mut T` 之前结束 | [02_borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) |
| **E0597** | borrowed value does not live long enough | 悬垂引用 | 确保引用 outlive 其指向的数据 | [03_lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) |
| **E0106** | missing lifetime specifier | 函数返回引用无生命周期标注 | 显式标注 `'a` 或使用 `'static` | [03_lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) |
| **E0204** | trait bound not satisfied | 为不满足条件的类型实现 Trait | 检查类型参数是否满足 Trait bounds | [01_traits](../../02_intermediate/00_traits/01_traits.md) |
| **E0277** | size not known at compile time | 使用 `?Sized` 但未正确处理 DST | 通过引用/Box 使用 DST | [02_generics](../../02_intermediate/01_generics/02_generics.md) |
| **E0308** | mismatched types | 类型不匹配 | 检查泛型参数、类型推断歧义 | [04_type_system](../../01_foundation/02_type_system/04_type_system.md) |
| **E0384** | reassignment of immutable variable | 修改不可变变量 | 改用 `let mut` 或 `Cell`/`RefCell` | [02_borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) |
| **E0392** | parameter `T` is never used | 泛型参数未在类型中使用 | 使用 `PhantomData<T>` 标记 | [02_generics](../../02_intermediate/01_generics/02_generics.md) |
| **E0433** | failed to resolve use statement | 模块路径错误 | 检查 `use` 路径和模块结构 | [04_type_system](../../01_foundation/02_type_system/04_type_system.md) |
| **E0495** | cannot infer an appropriate lifetime | 生命周期推断失败 | 显式标注生命周期约束 | [03_lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) |
| **E0520** | requires `Sync` bound | 跨线程共享非 Sync 类型 | 使用 `Mutex`/`RwLock` 包装 | [01_concurrency](../../03_advanced/00_concurrency/01_concurrency.md) |
| **E0596** | cannot borrow data in dereference of ... as mutable | 不可变上下文中需要可变引用 | 检查 `Deref` 返回的是否为 `&mut` | [02_borrowing](../../01_foundation/01_ownership_borrow_lifetime/02_borrowing.md) |
| **E0603** | module is private | 访问私有模块 | 使用 `pub` 暴露或检查可见性 | [04_type_system](../../01_foundation/02_type_system/04_type_system.md) |
| **E0658** | feature is unstable | 使用了不稳定特性 | 添加 `#![feature(...)]` 或使用稳定替代 | [03_evolution](../../07_future/03_evolution.md) |
| **E0716** | temporary value dropped while borrowed | 临时值的引用被延长 | 将临时值绑定到变量 | [03_lifetimes](../../01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md) |

[来源: [Rust Reference — Compiler Errors](https://doc.rust-lang.org/error_codes/) · [TRPL — Appendix: Error Codes](https://doc.rust-lang.org/book/appendix-02-operators.html)]

---

## 三、模式选择决策树（速查版）

```text
我需要...?
  ├─ 共享所有权？
  │   ├─ 单线程 → Rc<T>
  │   └─ 多线程 → Arc<T>
  ├─ 内部可变性？
  │   ├─ T: Copy（简单值）→ Cell<T>
  │   ├─ 单线程复杂借用 → RefCell<T>
  │   ├─ 多线程互斥 → Mutex<T>
  │   └─ 多读单写 → RwLock<T>
  ├─ 动态分发？
  │   ├─ 变体封闭（编译期已知）→ enum + match
  │   └─ 变体开放（运行时扩展）→ dyn Trait
  ├─ 错误处理？
  │   ├─ 可恢复错误 → Result<T, E>
  │   └─ 不可恢复错误 → panic!
  ├─ 异步？
  │   ├─ I/O 密集型 → async/await + Tokio
  │   └─ CPU 密集型 → std::thread
  └─ 零成本抽象？
      ├─ 泛型 → <T: Trait>
      └─ 编译期计算 → const generics / const fn
```

[来源: [TRPL — Smart Pointers](https://doc.rust-lang.org/book/ch15-00-smart-pointers.html) · [Rust Reference — Interior Mutability](https://doc.rust-lang.org/reference/interior-mutability.html)]

---

## 四、跨语言对照速查

| Rust | C++ | Java | Go | Haskell |
|:---|:---|:---|:---|:---|
| `Box<T>` | `unique_ptr<T>` | — | — | — |
| `Rc<T>` | `shared_ptr<T>` | — | — | — |
| `Arc<T>` | `shared_ptr<T>` (atomic) | — | — | — |
| `&T` / `&mut T` | `const T&` / `T&` | 引用 | — | — |
| `Trait` | 抽象类 / Interface | `interface` | `interface` | Typeclass |
| `enum` | `variant` (C++17) | — | — | ADT |
| `Option<T>` | `std::optional<T>` | `Optional<T>` | 多返回值 | `Maybe a` |
| `Result<T, E>` | `std::expected<T,E>` (C++23) | 异常 | 多返回值 | `Either e a` |
| `async/await` | Coroutines (C++20) | `CompletableFuture` | goroutine | `IO` monad |
| `panic!` | `std::terminate` | `RuntimeException` | `panic` | `error` |
| `Send/Sync` | — | — | — | — |
| `unsafe` | 默认开放 | `sun.misc.Unsafe` | `unsafe` | `unsafePerformIO` |

[来源: [Wikipedia — Comparison of Programming Languages](https://en.wikipedia.org/wiki/Comparison_of_programming_languages) · [TRPL — Appendix](https://doc.rust-lang.org/book/appendix-03-derivable-traits.html)]

---

> **深入阅读**: 本速查的完整理论背景见 [`semantic_space.md`](../00_framework/semantic_space.md) §4（等价表达的语义保持）；系统学习路径见 [`learning_guide.md`](learning_guide.md)。
---

> **权威来源**:
> [Rust Reference](https://doc.rust-lang.org/reference/),
> [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html),
> [Rustonomicon](https://doc.rust-lang.org/nomicon/),
> [Rust Standard Library](https://doc.rust-lang.org/std/),
> [Rust Async Book](https://rust-lang.github.io/async-book/),
> [Cargo Book](https://doc.rust-lang.org/cargo/)
>
> **速查来源索引**
>
> | 来源 | 链接 |
> |:---|:---|
> | Rust Reference | [doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/) |
> | TRPL | [doc.rust-lang.org/book](https://doc.rust-lang.org/book/title-page.html) |
> | Rustonomicon | [doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/) |
> | Rust Standard Library | [doc.rust-lang.org/std](https://doc.rust-lang.org/std/) |
> | Rust Async Book | [rust-lang.github.io/async-book](https://rust-lang.github.io/async-book/) |
> | Cargo Book | [doc.rust-lang.org/cargo](https://doc.rust-lang.org/cargo/) |
> | Wikipedia — PL Comparison | [en.wikipedia.org/wiki/Comparison_of_programming_languages](https://en.wikipedia.org/wiki/Comparison_of_programming_languages) |
>
> **权威来源对齐变更日志**:
>
> 2026-05-22 批量补充来源标注（Rust Reference、TRPL、Rustonomicon、标准库、Wikipedia 等）
>
> [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

## 认知路径

> **认知路径**: 本文件作为 Rust 分层知识体系的 **Rust 概念速查卡片（Quick Reference）** 元层导航节点，连接概念定义、学习路径与质量评估框架。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| Quick Reference 结构化定义 ⟹ 学习者认知锚点可建立 | 本文件定义了元层结构 | 支持上层概念定位 | 高 |

> **过渡**: 利用本文件的导航结构，读者可以从当前位置快速跃迁到任意概念层级，实现非线性学习。
> **过渡**: Rust 概念速查卡片（Quick Reference） 的维护需要与概念内容同步更新，确保元数据与实际知识体系的一致性。
> **过渡**: 将 Rust 概念速查卡片（Quick Reference） 作为学习起点或复习锚点，有助于建立全局视野，避免陷入局部细节而忽视整体架构。

### 反命题与边界

> **反命题**: "元层文档可以替代具体概念学习" —— 错误。Rust 概念速查卡片（Quick Reference） 提供的是导航与评估框架，不能替代对核心概念（L1-L5）的深入理解与实践。
> **内容分级**: [综述级]

## 嵌入式测验（Embedded Quiz）

### 测验 1：本文档《Rust 概念速查卡片（Quick Reference）》在 Rust 知识体系中属于哪一层级的元数据？（理解层）

**题目**: 本文档《Rust 概念速查卡片（Quick Reference）》在 Rust 知识体系中属于哪一层级的元数据？

<details>
<summary>✅ 答案与解析</summary>

属于 00_meta 元数据层，为整个知识体系提供导航、评估、审计和结构化的支持框架，辅助学习者定位和理解核心概念。
</details>

---

### 测验 2：《Rust 概念速查卡片（Quick Reference）》的主要用途是什么？（理解层）

**题目**: 《Rust 概念速查卡片（Quick Reference）》的主要用途是什么？

<details>
<summary>✅ 答案与解析</summary>

作为知识体系的支撑文档，提供学习路径导航、概念关系映射、质量评估标准或审计检查清单，帮助学习者和维护者高效使用知识库。
</details>

---

### 测验 3：元数据层文档能否替代 L1-L7 的核心概念学习？（理解层）

**题目**: 元数据层文档能否替代 L1-L7 的核心概念学习？

<details>
<summary>✅ 答案与解析</summary>

不能。元数据层提供导航和评估框架，但不能替代对核心概念（所有权、类型系统、并发等）的深入理解与实践。
</details>
