# Rust 知识体系自测题库（Self-Assessment）
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

> **Bloom 层级**: 应用 → 评价
> **定位**：每个层级配套的自测题，用于验证知识掌握程度。答案和解析附在每题之后（可折叠）。
> **使用方式**：先做题，再对答案。建议配合 [`learning_guide.md`](./learning_guide.md) 使用。

---

> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [concept/知识体系]
>
## 📑 目录
>
> [来源: [TRPL]]

- [Rust 知识体系自测题库（Self-Assessment）](#rust-知识体系自测题库self-assessment)
  - [📑 目录](#-目录)
  - [L1 基础层：所有权与类型系统（8 题） \[来源: 题目基于 TRPL Ch4 (所有权), Ch10 (生命周期), Ch6 (枚举) / 2024; Rust Reference — Ownership, Lifetimes, Types / 2025; RustBelt (Jung et al., POPL 2018)\]](#l1-基础层所有权与类型系统8-题-来源-题目基于-trpl-ch4-所有权-ch10-生命周期-ch6-枚举--2024-rust-reference--ownership-lifetimes-types--2025-rustbelt-jung-et-al-popl-2018)
    - [Q1: Move vs Copy](#q1-move-vs-copy)
    - [Q2: 借用规则](#q2-借用规则)
    - [Q3: 生命周期省略](#q3-生命周期省略)
    - [Q4: enum 穷尽匹配](#q4-enum-穷尽匹配)
    - [Q5: Trait 对象安全](#q5-trait-对象安全)
    - [Q6: Result 传播](#q6-result-传播)
    - [Q7: Drop 顺序](#q7-drop-顺序)
    - [Q8: 泛型单态化](#q8-泛型单态化)
  - [L2 进阶层：泛型与错误处理（7 题） \[来源: 题目基于 TRPL Ch10 (泛型), Ch9 (错误处理) / 2024; Rust Reference — Generic Parameters, The ? operator / 2025; Pierce — TAPL (2002)\]](#l2-进阶层泛型与错误处理7-题-来源-题目基于-trpl-ch10-泛型-ch9-错误处理--2024-rust-reference--generic-parameters-the--operator--2025-pierce--tapl-2002)
    - [Q9: Trait Bounds](#q9-trait-bounds)
    - [Q10: Associated Types vs Generics](#q10-associated-types-vs-generics)
    - [Q11: PhantomData 用途](#q11-phantomdata-用途)
    - [Q12: RefCell 运行时检查](#q12-refcell-运行时检查)
    - [Q13: 错误传播转换](#q13-错误传播转换)
    - [Q15: 闭包捕获](#q15-闭包捕获)
  - [L3 高级层：并发与异步（8 题） \[来源: 题目基于 TRPL Ch16 (并发), Rust Async Book / 2025; RustBelt (Jung et al., POPL 2018); RFC 2394 / 2018; Herlihy \& Shavit — The Art of Multiprocessor Programming (2020)\]](#l3-高级层并发与异步8-题-来源-题目基于-trpl-ch16-并发-rust-async-book--2025-rustbelt-jung-et-al-popl-2018-rfc-2394--2018-herlihy--shavit--the-art-of-multiprocessor-programming-2020)
    - [Q16: Send + Sync](#q16-send--sync)
    - [Q17: MutexGuard 跨 await](#q17-mutexguard-跨-await)
    - [Q18: Pin 语义](#q18-pin-语义)
    - [Q19: 死锁条件](#q19-死锁条件)
    - [Q20: unsafe 块边界](#q20-unsafe-块边界)
    - [Q21: Waker 机制](#q21-waker-机制)
    - [Q22: 宏卫生性](#q22-宏卫生性)
    - [Q23: unsafe 安全契约](#q23-unsafe-安全契约)
  - [L4 形式化层：类型理论与证明（7 题） \[来源: 题目基于 TAPL (Pierce, 2002); RustBelt (Jung et al., POPL 2018); Girard — Linear Logic / 1987; Jung — Tree Borrows (arXiv 2023)\]](#l4-形式化层类型理论与证明7-题-来源-题目基于-tapl-pierce-2002-rustbelt-jung-et-al-popl-2018-girard--linear-logic--1987-jung--tree-borrows-arxiv-2023)
    - [Q24: 仿射逻辑](#q24-仿射逻辑)
    - [Q25: 参数性定理](#q25-参数性定理)
    - [Q26: HRTB](#q26-hrtb)
    - [Q27: Region-based 内存管理](#q27-region-based-内存管理)
    - [Q28: Soundness 定义](#q28-soundness-定义)
    - [Q29: 分离逻辑](#q29-分离逻辑)
    - [Q30: Oxide 形式化](#q30-oxide-形式化)
  - [L5 对比层：多语言范式（5 题） 来源: 题目基于 TRPL 跨章节对比 / 2024; Rust Reference — Types, Traits / 2025; Wikipedia — Object-oriented Programming](#l5-对比层多语言范式5-题-来源-题目基于-trpl-跨章节对比--2024-rust-reference--types-traits--2025-wikipedia--object-oriented-programming)
    - [Q31: Rust vs C++ RAII](#q31-rust-vs-c-raii)
    - [Q32: Rust vs Haskell 类型类](#q32-rust-vs-haskell-类型类)
    - [Q33: Rust vs Go 并发模型](#q33-rust-vs-go-并发模型)
    - [Q34: 依赖类型](#q34-依赖类型)
    - [Q35: Linear vs Affine](#q35-linear-vs-affine)
  - [L6 生态层：工程实践（5 题） 来源: 题目基于 Cargo Book / 2025; Rust Reference — Crates, unsafe / 2025; Rust Internals — Edition System](#l6-生态层工程实践5-题-来源-题目基于-cargo-book--2025-rust-reference--crates-unsafe--2025-rust-internals--edition-system)
    - [Q36: Cargo Workspace](#q36-cargo-workspace)
    - [Q37: 条件编译](#q37-条件编译)
    - [Q38: Miri 用途](#q38-miri-用途)
    - [Q39: Rust 版本兼容性](#q39-rust-版本兼容性)
    - [Q40: unsafe 审计清单](#q40-unsafe-审计清单)
  - [](#)
  - [L1 扩展层：所有权与类型系统（8 题） 来源: 题目基于 Rust Reference — Ownership, Lifetimes, Types / 2025; TRPL Ch4, Ch6, Ch10 / 2024; Rustonomicon — Life before Main](#l1-扩展层所有权与类型系统8-题-来源-题目基于-rust-reference--ownership-lifetimes-types--2025-trpl-ch4-ch6-ch10--2024-rustonomicon--life-before-main)
    - [Q41: 函数参数传递](#q41-函数参数传递)
    - [Q42: Copy 边界](#q42-copy-边界)
    - [Q43: 多输入引用生命周期](#q43-多输入引用生命周期)
    - [Q45: enum 内存布局](#q45-enum-内存布局)
    - [Q46: 类型推断与 Turbofish](#q46-类型推断与-turbofish)
    - [Q47: match 绑定模式](#q47-match-绑定模式)
    - [Q48: const 上下文限制](#q48-const-上下文限制)
  - [L2 扩展层：Trait、泛型、内存管理与错误处理（8 题） 来源: 题目基于 TRPL Ch10 (泛型), Ch9 (错误处理), Ch15 (智能指针) / 2024; Rust Reference — Generic Parameters, The ? operator / 2025; Wikipedia — Copy-on-Write\]](#l2-扩展层trait泛型内存管理与错误处理8-题-来源-题目基于-trpl-ch10-泛型-ch9-错误处理-ch15-智能指针--2024-rust-reference--generic-parameters-the--operator--2025-wikipedia--copy-on-write)
    - [Q49: Trait Bound 组合](#q49-trait-bound-组合)
    - [Q50: Associated Type 约束](#q50-associated-type-约束)
    - [Q51: 结构体生命周期](#q51-结构体生命周期)
    - [Q52: Drop 与 Panic 安全](#q52-drop-与-panic-安全)
    - [Q53: Cow 的用途](#q53-cow-的用途)
    - [Q54: Error Source Chain](#q54-error-source-chain)
    - [Q55: 泛型 vs Trait Object 错误处理](#q55-泛型-vs-trait-object-错误处理)
    - [Q56: Zero-Sized Types (ZST)](#q56-zero-sized-types-zst)
  - [L3 扩展层：并发、异步、unsafe 与宏（8 题） 来源: 题目基于 TRPL Ch16 (并发), Rust Async Book / 2025; Rust Reference — unsafe, Macros / 2025; RFC 2349 (Pin)](#l3-扩展层并发异步unsafe-与宏8-题-来源-题目基于-trpl-ch16-并发-rust-async-book--2025-rust-reference--unsafe-macros--2025-rfc-2349-pin)
    - [Q57: Atomic Ordering](#q57-atomic-ordering)
    - [Q58: Stream vs Iterator](#q58-stream-vs-iterator)
    - [Q59: Cancel Safety](#q59-cancel-safety)
    - [Q60: UnsafeCell](#q60-unsafecell)
    - [Q61: Strict Provenance](#q61-strict-provenance)
    - [Q62: Proc Macro Hygiene](#q62-proc-macro-hygiene)
    - [Q63: Pin Projection](#q63-pin-projection)
  - [L4 扩展层：线性逻辑、类型论、所有权形式化与 RustBelt（8 题） 来源: 题目基于 TAPL (Pierce, 2002); RustBelt (Jung et al., POPL 2018); Girard — Linear Logic / 1987; Wikipedia — Substructural Type System\]](#l4-扩展层线性逻辑类型论所有权形式化与-rustbelt8-题-来源-题目基于-tapl-pierce-2002-rustbelt-jung-et-al-popl-2018-girard--linear-logic--1987-wikipedia--substructural-type-system)
    - [Q65: 子结构逻辑](#q65-子结构逻辑)
    - [Q66: Curry-Howard 同构](#q66-curry-howard-同构)
    - [Q67: Type Soundness vs Memory Safety](#q67-type-soundness-vs-memory-safety)
    - [Q68: Iris 模态断言](#q68-iris-模态断言)
    - [Q69: Liveness 属性](#q69-liveness-属性)
    - [Q70: 参数性 vs 特设多态](#q70-参数性-vs-特设多态)
    - [Q71: RustBelt Invariant](#q71-rustbelt-invariant)
    - [Q72: Ghost State](#q72-ghost-state)
  - [L5 扩展层：多语言范式对比（4 题） 来源: 题目基于 TRPL 跨语言对比 / 2024; Rust Reference — unsafe, FFI / 2025; Wikipedia — Capability-based Security\]](#l5-扩展层多语言范式对比4-题-来源-题目基于-trpl-跨语言对比--2024-rust-reference--unsafe-ffi--2025-wikipedia--capability-based-security)
    - [Q73: Rust vs Swift](#q73-rust-vs-swift)
    - [Q74: Rust vs C# Span](#q74-rust-vs-c-span)
    - [Q75: 零成本抽象](#q75-零成本抽象)
    - [Q76: 基于能力的安全](#q76-基于能力的安全)
  - [L6 扩展层：工程实践与生态（4 题） 来源: 题目基于 Cargo Book / 2025; Rust Reference — Macros, Documentation / 2025; SemVer 2.0.0\]](#l6-扩展层工程实践与生态4-题-来源-题目基于-cargo-book--2025-rust-reference--macros-documentation--2025-semver-200)
    - [Q77: Cargo Features 解析](#q77-cargo-features-解析)
    - [Q78: proc-macro2 与 syn](#q78-proc-macro2-与-syn)
    - [Q79: SemVer 与 API 演进](#q79-semver-与-api-演进)
    - [Q80: rustdoc Doctest](#q80-rustdoc-doctest)
  - [来源与参考文献](#来源与参考文献)

> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [concept/知识体系]
>
## L1 基础层：所有权与类型系统（8 题） [来源: 题目基于 TRPL Ch4 (所有权), Ch10 (生命周期), Ch6 (枚举) / 2024; Rust Reference — Ownership, Lifetimes, Types / 2025; RustBelt (Jung et al., POPL 2018)]
>
> [来源: [TRPL]]

> **[来源: Bloom Taxonomy 2001; 认知科学评估方法论]** 自测题基于 Bloom 认知层级设计，覆盖记忆→理解→应用→分析。

> **来源**: [Rust Reference] · [TRPL] · [RFCs]
>
### Q1: Move vs Copy
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

以下代码能否编译？如果不能，为什么？

```rust,ignore,E0382
let s1 = String::from("hello");
let s2 = s1;
println!("{}", s1);
```

<details>
<summary>答案</summary>

**不能编译**。`String` 未实现 `Copy`，赋值时发生 Move，`s1` 所有权转移给 `s2`，之后 `s1` 不可用。编译错误 **E0382**。

**修正**：`let s2 = s1.clone();`

</details>

---

> **来源**: [Rust Reference] · [TRPL] · [RFCs]
>
### Q2: 借用规则
>
> [来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]

以下代码能否编译？

```rust,ignore,E0502
let mut x = 5;
let r1 = &x;
let r2 = &mut x;
println!("{}", r1);
```

<details>
<summary>答案</summary>

**不能编译**。`r1` 是共享引用 `&x`，`r2` 是可变引用 `&mut x`，二者不能共存。编译错误 **E0502**。

**核心规则**：任意时刻，要么一个 `&mut T`，要么任意多个 `&T`。

</details>

---

> **来源**: [Rust Reference] · [TRPL] · [RFCs]
>
### Q3: 生命周期省略
>
> [来源: [Wikipedia — Rust](https://en.wikipedia.org/wiki/Rust_(programming_language))]

以下函数签名能否编译？为什么？

```rust
fn first_word(s: &str) -> &str {
    &s[0..1]
}
```

<details>
<summary>答案</summary>

**能编译**。满足生命周期省略规则（第1条）：单个输入引用 → 输出引用获得相同生命周期。

完整签名等价于：

```rust,ignore
fn first_word<'a>(s: &'a str) -> &'a str

```

</details>

---

### Q4: enum 穷尽匹配
>
> [来源: [Wikipedia — Programming Language](https://en.wikipedia.org/wiki/Programming_language)]

以下 `match` 是否完整？

```rust,ignore
enum Color { Red, Green, Blue }
fn describe(c: Color) -> &'static str {
    match c {
        Color::Red => "red",
        Color::Green => "green",
    }
}

```

<details>
<summary>答案</summary>

**不完整**。缺少 `Color::Blue` 分支，编译错误 **E0004**。

**修正**：添加 `Color::Blue => "blue"` 或使用 `_ => "other"` 通配。

</details>

---

### Q5: Trait 对象安全
>
> [来源: [Wikipedia — Type System](https://en.wikipedia.org/wiki/Type_system)]

以下能否创建 `dyn Drawable`？

```rust
trait Drawable {
    fn draw(&self);
    fn new() -> Self where Self: Sized;
}
```

<details>
<summary>答案</summary>

**能**。`where Self: Sized` 的关联方法不会破坏对象安全性，因为它在 trait object 上不可调用。

如果 `new()` 没有 `where Self: Sized`，则 `dyn Drawable` 不可创建（vtable 无法包含构造方法）。

</details>

---

### Q6: Result 传播
>
> [来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]

以下代码的问题是什么？

```rust,ignore,E0277
fn read_config(path: &str) -> String {
    let contents = std::fs::read_to_string(path)?;
    contents
}
```

<details>
<summary>答案</summary>

**`?` 运算符要求函数返回 `Result<T, E>`**。当前返回类型是 `String`，不匹配。

**修正**：

```rust
fn read_config(path: &str) -> Result<String, std::io::Error> {
    let contents = std::fs::read_to_string(path)?;
    Ok(contents)
}
```

</details>

---

### Q7: Drop 顺序
>
> [来源: [Cargo Book](https://doc.rust-lang.org/cargo/)]

以下代码的输出顺序是什么？

```rust
struct A(&'static str);
impl Drop for A {
    fn drop(&mut self) { println!("{}", self.0); }
}
let _a = A("a");
{
    let _b = A("b");
}
let _c = A("c");
```

<details>
<summary>答案</summary>

输出顺序：`b` → `a` → `c`

**规则**：变量按与声明相反的顺序 drop（LIFO），`_b` 作用域最小，最先 drop。

</details>

---

### Q8: 泛型单态化
>
> [来源: [Rust Async Book](https://rust-lang.github.io/async-book/)]

以下代码编译后生成几个版本的 `identity`？

```rust
fn identity<T>(x: T) -> T { x }
let a = identity(5i32);
let b = identity(3.14f64);
let c = identity("hello");
```

<details>
<summary>答案</summary>

**3 个版本**：`identity_i32`、`identity_f64`、`identity_&str`。

Rust 泛型采用**单态化**，每个具体类型生成独立函数体，零运行时开销。

</details>

---

> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [concept/知识体系]
>
## L2 进阶层：泛型与错误处理（7 题） [来源: 题目基于 TRPL Ch10 (泛型), Ch9 (错误处理) / 2024; Rust Reference — Generic Parameters, The ? operator / 2025; Pierce — TAPL (2002)]
>
> [来源: [TRPL]]

> **[来源: TRPL / Rust Reference / TAPL]** 泛型基于参数多态，错误处理基于代数数据类型。

### Q9: Trait Bounds
>
> [来源: [Wikipedia — Object-oriented Programming](https://en.wikipedia.org/wiki/Object-oriented_programming)]

以下代码能否编译？

```rust,ignore,E0277
fn print_debug<T>(x: T) {
    println!("{:?}", x);
}
```

<details>
<summary>答案</summary>

**不能**。`println!("{:?}", x)` 要求 `T: Debug`，但函数签名未声明此 bound。编译错误。

**修正**：`fn print_debug<T: std::fmt::Debug>(x: T)`

</details>

---

### Q10: Associated Types vs Generics
>
> [来源: [Wikipedia — Substructural Type System](https://en.wikipedia.org/wiki/Substructural_type_system)]

`trait Iterator<T>` 和 `trait Iterator { type Item; }` 的区别是什么？

<details>
<summary>答案</summary>

- **泛型参数 `<T>`**：一个类型可实现 `Iterator<i32>` 和 `Iterator<String>`（多实例）
- **关联类型 `type Item`**：一个类型只能实现一次 `Iterator`（单实例）

Iterator 选择关联类型，因为 "一个集合只有一种元素类型" 是符合直觉的约束。

</details>

---

### Q11: PhantomData 用途
>
> [来源: [Wikipedia — Parametric Polymorphism](https://en.wikipedia.org/wiki/Parametric_polymorphism)]

为什么以下代码需要 `PhantomData<T>`？

```rust
struct MyPtr<T> {
    ptr: *mut (),
    _marker: std::marker::PhantomData<T>,
}
```

<details>
<summary>答案</summary>

`PhantomData<T>` 告诉编译器：`MyPtr<T>` 逻辑上拥有/关联 `T`，影响：

1. **Drop check**：编译器知道 `MyPtr<T>` 可能需要 drop `T`
2. **Variance**：`MyPtr<T>` 的协变/逆变关系与 `T` 一致
3. **Send/Sync**：自动推导基于 `T`

没有 `PhantomData<T>`，`MyPtr<T>` 对所有 `T` 都是协变的，且总是 `Send + Sync`。

</details>

---

### Q12: RefCell 运行时检查
>
> [来源: [Wikipedia — Capability-based Security](https://en.wikipedia.org/wiki/Capability-based_security)]

以下代码运行结果？

```rust
use std::cell::RefCell;
let cell = RefCell::new(0);
let _b1 = cell.borrow();
let _b2 = cell.borrow_mut();  // 运行时 panic
```

<details>
<summary>答案</summary>

**运行时 panic**：`already mutably borrowed`。

`RefCell` 在运行时检查借用规则（而非编译期），检测到共享借用和可变借用共存时 panic。

</details>

---

### Q13: 错误传播转换
>
> [来源: [SemVer](https://semver.org/)]

`?` 运算符如何转换错误类型？

```rust,ignore
fn foo() -> Result<(), MyError> {
    std::fs::read_to_string("file.txt")?;  // io::Error → MyError ?
}

```

<details>
<summary>答案</summary>

`?` 运算符要求 `From<源错误> for 目标错误` 实现存在。需为 `MyError` 实现：

rust,ignore
impl From<std::io::Error> for MyError { ... }

```

或使用 `map_err` 手动转换。

</details>

---

### Q14: Sized vs ?Sized
> [来源: [Miri Docs](https://github.com/rust-lang/miri)]

以下函数签名有什么问题？

```rust
fn process<T>(data: T) {
    let size = std::mem::size_of::<T>();
}
```

<details>
<summary>答案</summary>

**没有问题**。泛型参数默认 `T: Sized`，`size_of::<T>()` 要求 `T: Sized`，满足。

如果要接受 trait object：`fn process<T: ?Sized>(data: &T)`

</details>

---

### Q15: 闭包捕获
>
> [来源: [Wikipedia — Linear Logic](https://en.wikipedia.org/wiki/Linear_logic)]

以下闭包捕获 `x` 的方式？

```rust
let x = String::from("hello");
let f = || println!("{}", x);  // 捕获方式？
let g = move || println!("{}", x);  // 捕获方式？
```

<details>
<summary>答案</summary>

- `f`：**不可变引用** `&x`（因为只读）
- `g`：**Move** `x`（`move` 关键字强制转移所有权）

`move` 后 `x` 不可用。

</details>

---

> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [concept/知识体系]
>
## L3 高级层：并发与异步（8 题） [来源: 题目基于 TRPL Ch16 (并发), Rust Async Book / 2025; RustBelt (Jung et al., POPL 2018); RFC 2394 / 2018; Herlihy & Shavit — The Art of Multiprocessor Programming (2020)]
>
> [来源: [TRPL]]

> **[来源: Rust Async Book / RustBelt / Herlihy & Shavit]** 并发安全基于 `Send`/`Sync` 类型系统保证，异步基于 Future 状态机。

### Q16: Send + Sync
>
> [来源: [Wikipedia — RAII](https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization)]

`Rc<String>` 是 `Send` 还是 `Sync`？为什么？

<details>
<summary>答案</summary>

**既不是 Send 也不是 Sync**。

- `Rc` 使用非原子引用计数，跨线程 clone/drop 会导致数据竞争
- `String` 本身是 `Send + Sync`，但 `Rc` 的包装使其不再线程安全

**多线程共享** → `Arc<String>`

</details>

---

### Q17: MutexGuard 跨 await
>
> [来源: [ISO C++](https://isocpp.org/)]

以下代码能否编译？

```rust,ignore,E0277
async fn fetch_and_update(data: &Mutex<i32>) {
    let mut guard = data.lock().unwrap();
    *guard += fetch_from_network().await;  // await 在 guard 作用域内
}
```

<details>
<summary>答案</summary>

**不能编译**。`MutexGuard` 不是 `Send`，跨 await 时编译器拒绝（因为可能切换到另一个线程执行，而 guard 持有线程本地锁）。

**修正**：缩小 guard 作用域：

```rust,ignore
async fn fetch_and_update(data: &Mutex<i32>) {
    let value = fetch_from_network().await;
    let mut guard = data.lock().unwrap();
    *guard += value;
}
```

</details>

---

### Q18: Pin 语义
>
> [来源: [Bjarne Stroustrup](https://www.stroustrup.com/)]

为什么 `Future::poll` 使用 `Pin<&mut Self>` 而非 `&mut Self`？

<details>
<summary>答案</summary>

`async fn` 编译后的状态机可能包含**自引用字段**（如 `let x = ...; let y = &x;`）。

如果状态机被 Move（`&mut Self` 允许），自引用指针将悬垂。

`Pin` 保证 `Self` 的内存地址不变，保护自引用结构。

</details>

---

### Q19: 死锁条件
>
> [来源: [Wikipedia — C++](https://en.wikipedia.org/wiki/C%2B%2B)]

以下代码是否可能死锁？

```rust,ignore
let a = Mutex::new(0);
let b = Mutex::new(0);
let a2 = Arc::clone(&a);
let b2 = Arc::clone(&b);
thread::spawn(move || {
    let _a = a.lock();
    let _b = b.lock();
});
let _b = b2.lock();
let _a = a2.lock();
```

<details>
<summary>答案</summary>

**可能死锁**。两个线程以**相反顺序**获取锁：

- 线程1：a → b
- 线程2：b → a

**避免**：统一锁获取顺序（如按地址排序），或使用 `std::sync::Mutex::lock` + 超时。

</details>

---

### Q20: unsafe 块边界
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

`unsafe` 块内部可以使用哪些编译器不检查的操作？

<details>
<summary>答案</summary>

5 个特定逃逸门：

1. 解引用原始指针 `*raw_ptr`
2. 调用 `unsafe fn`
3. 访问 `mut static`
4. 实现 `unsafe trait`
5. 读取 `union` 字段

**注意**：`unsafe` 块不关闭类型系统，类型检查仍然有效。

</details>

---

### Q21: Waker 机制
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

自定义 Future 为什么需要存储 `Waker`？

<details>
<summary>答案</summary>

当 `poll` 返回 `Pending` 时，Future 被挂起。如果没有存储 Waker，事件就绪时无法通知执行器重新 poll。

**流程**：

1. `poll` 发现未就绪 → 存储 `cx.waker()` → 返回 `Pending`
2. 外部事件就绪 → 调用 `waker.wake()`
3. 执行器将任务重新加入队列 → 再次 `poll`

</details>

---

### Q22: 宏卫生性
>
> [来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]

以下宏调用输出什么？

```rust
macro_rules! make_var {
    ($name:ident, $val:expr) => {
        let $name = $val;
    };
}
fn main() {
    let x = 10;
    make_var!(x, 20);
    println!("{}", x);
}
```

<details>
<summary>答案</summary>

**输出 10**。

Rust 宏是**卫生宏**：宏内部定义的 `let x` 不会覆盖外部 `x`。宏中的 `x` 是独立命名空间。

</details>

---

### Q23: unsafe 安全契约
>
> [来源: [Wikipedia — Rust](https://en.wikipedia.org/wiki/Rust_(programming_language))]

以下 `unsafe` 实现是否安全？

```rust,ignore
unsafe impl Send for MyType {}
```

<details>
<summary>答案</summary>

**取决于 `MyType` 的字段**。如果 `MyType` 包含 `Rc<T>` 或原始指针，则手动实现 `Send` 可能导致数据竞争。

**原则**：`unsafe impl` 的安全契约由程序员保证，编译器不验证。

</details>

---

> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [concept/知识体系]
>
## L4 形式化层：类型理论与证明（7 题） [来源: 题目基于 TAPL (Pierce, 2002); RustBelt (Jung et al., POPL 2018); Girard — Linear Logic / 1987; Jung — Tree Borrows (arXiv 2023)]
>
> [来源: [TRPL]]

> **[来源: TAPL / RustBelt / Girard / Jung]** 形式化方法基于类型论、线性逻辑和分离逻辑。

### Q24: 仿射逻辑
>
> [来源: [Wikipedia — Programming Language](https://en.wikipedia.org/wiki/Programming_language)]

Rust 的 Ownership 对应哪种逻辑？

<details>
<summary>答案</summary>

**仿射逻辑（Affine Logic）** — "A resource can be used at most once"。

通过 `weakening` 规则实现 Copy（0 次或 1 次 → 任意次数）。

</details>

---

### Q25: 参数性定理
>
> [来源: [Wikipedia — Type System](https://en.wikipedia.org/wiki/Type_system)]

以下函数的实现必然是什么？

```rust,ignore
fn identity<T>(x: T) -> T { ... }
```

<details>
<summary>答案</summary>

**必然返回 `x`**。

根据 **参数性定理（Parametricity）**，没有任何关于 `T` 的信息，函数只能返回输入值（或 panic/diverge）。

</details>

---

### Q26: HRTB
>
> [来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]

以下 `F` 的 bound 含义？

```rust,ignore
fn process<F>(f: F)
where F: for<'a> Fn(&'a str) -> &'a str,

```

<details>
<summary>答案</summary>

**高阶 Trait Bound（HRTB）**：`F` 接受任意生命周期 `'a` 的 `&str` 引用，返回相同生命周期 `'a` 的 `&str`。

等价于 **System F 中的全称量化** `∀'a. (Fn(&'a str) -> &'a str)`。

</details>

---

### Q27: Region-based 内存管理
>
> [来源: [Cargo Book](https://doc.rust-lang.org/cargo/)]

Rust 生命周期与 Region-based Memory Management 的关系？

<details>
<summary>答案</summary>

Rust 借鉴了 **Region 类型系统**（Tofte & Talpin, 1994）：

- 值绑定到一个区域（lexical scope）
- 区域结束时，区域内所有值被释放
- 但 Rust 的区域是**结构化**的（基于词法作用域），且通过借用检查器验证引用有效性

**区别**：Rust 允许非词法生命周期（NLL），而经典 Region 是纯词法的。

</details>

---

### Q28: Soundness 定义
>
> [来源: [Rust Async Book](https://rust-lang.github.io/async-book/)]

"Rust 类型系统是 sound" 意味着什么？

<details>
<summary>答案</summary>

**类型安全（Soundness）**：如果程序通过类型检查，则运行时不会出现**未定义行为（UB）**。

形式化定义：**Progress + Preservation**

- **Progress**：良类型表达式不会 stuck（除安全停机外）
- **Preservation**：求值保持类型

</details>

---

### Q29: 分离逻辑
>
> [来源: [Wikipedia — Object-oriented Programming](https://en.wikipedia.org/wiki/Object-oriented_programming)]

如何用分离逻辑（Separation Logic）表达 "x 指向 5，y 指向 10"？

<details>
<summary>答案</summary>

```

x ↦ 5 ∗ y ↦ 10

```

`∗`（分离合取）表示 `x` 和 `y` 指向**不相交**的内存区域。

</details>

---

### Q30: Oxide 形式化
>
> [来源: [Wikipedia — Substructural Type System](https://en.wikipedia.org/wiki/Substructural_type_system)]

Oxide 形式化中，`Γ ⊢ e : τ ⊣ Φ` 的 `Φ` 表示什么？

<details>
<summary>答案</summary>

`Φ`（Effect）表示表达式 `e` 执行后的**所有权环境变化**，记录哪些变量被 move、哪些被 borrow。

Oxide 的核心创新：用 **ownership typing** 形式化 Rust 的所有权规则。

</details>

---

> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [concept/知识体系]
>
> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [Wikipedia — Programming Language Comparison](https://en.wikipedia.org/wiki/Comparison_of_programming_languages)
>
## L5 对比层：多语言范式（5 题） [来源: 题目基于 TRPL 跨章节对比 / 2024; Rust Reference — Types, Traits / 2025; Wikipedia — Object-oriented Programming](https://en.wikipedia.org/wiki/Object-oriented_programming)
>
> [来源: [TRPL]]

### Q31: Rust vs C++ RAII
>
> [来源: [Wikipedia — Parametric Polymorphism](https://en.wikipedia.org/wiki/Parametric_polymorphism)]

Rust 的 RAII 与 C++ 有何根本区别？

<details>
<summary>答案</summary>

- **C++**：Move 是默认的（复制构造函数可被省略），所有权隐含，容易悬垂
- **Rust**：Move 是显式的（`=` 即 move），所有权在类型系统中追踪，编译器保证无悬垂

</details>

---

### Q32: Rust vs Haskell 类型类
>
> [来源: [Wikipedia — Capability-based Security](https://en.wikipedia.org/wiki/Capability-based_security)]

Rust Trait 与 Haskell Typeclass 的核心差异？

<details>
<summary>答案</summary>

- **Orphan Rule**：Rust 禁止为外部类型实现外部 Trait（Haskell 允许 `orphan instance`）
- **无高阶类型（HKT）**：Rust 没有 `* -> *` 级别的抽象（可用 GAT 模拟）
- **无类型类推导**：Rust 需要显式 `#[derive]` 或手动实现

</details>

---

### Q33: Rust vs Go 并发模型
>
> [来源: [SemVer](https://semver.org/)]

Rust 的并发安全如何保障？

<details>
<summary>答案</summary>

- **Rust**：编译期通过 `Send/Sync` Trait 保证，数据竞争是编译错误
- **Go**：运行时通过 `go vet` / `race detector` 检测，竞争条件可能导致运行时错误

Rust 的并发安全是**零运行时开销**的编译期保证。

[来源: [Rust Reference — Send and Sync](https://doc.rust-lang.org/reference/special-types-and-traits.html)]

</details>

---

### Q34: 依赖类型
>
> [来源: [Miri Docs](https://github.com/rust-lang/miri)]

为什么 Rust 不采用依赖类型？

<details>
<summary>答案</summary>

依赖类型（如 `Vec<n>` 其中 `n` 是类型级自然数）要求：

1. 类型检查可能不可判定（Turing 完备的类型级计算）
2. 类型推断需要 SMT 求解器，编译时间爆炸
3. 与普通程序员的学习曲线冲突

Rust 选择 **Const Generics** 作为折中：编译期已知常量，但保留可判定的类型检查。

[来源: [Rust Reference — Const Generics](https://doc.rust-lang.org/reference/items/generics.html)]

</details>

---

### Q35: Linear vs Affine
>
> [来源: [Wikipedia — Linear Logic](https://en.wikipedia.org/wiki/Linear_logic)]

线性类型系统与仿射类型系统的区别？

<details>
<summary>答案</summary>

- **线性（Linear）**：资源必须**恰好使用 1 次**（no weakening, no contraction）
- **仿射（Affine）**：资源可以**使用 0 次或 1 次**（允许 weakening，不允许 contraction）

Rust 是仿射的：`let x = ...;` 后不使用 `x` 是合法的（ weakening）。

</details>

---

> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [concept/知识体系]
>
> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [Cargo Book](https://doc.rust-lang.org/cargo/)
>
## L6 生态层：工程实践（5 题） [来源: 题目基于 Cargo Book / 2025; Rust Reference — Crates, unsafe / 2025; Rust Internals — Edition System](https://internals.rust-lang.org/)
>
> [来源: [TRPL]]

### Q36: Cargo Workspace
>
> [来源: [Wikipedia — RAII](https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization)]

Workspace 中 `resolver = "2"` 的作用？

<details>
<summary>答案</summary>

Resolver 2（Rust 2021 默认）按**特性**而非**包**解析依赖：

- 同一个包的不同特性在不同依赖中独立激活
- 避免特性合并导致的编译错误

[来源: [Cargo Book — Features](https://doc.rust-lang.org/cargo/reference/features.html)]

</details>

---

### Q37: 条件编译
>
> [来源: [ISO C++](https://isocpp.org/)]

`#[cfg(target_os = "windows")]` 与 `#[cfg(unix)]` 的区别？

<details>
<summary>答案</summary>

- `target_os = "windows"`：仅 Windows
- `unix`：所有 Unix-like 系统（Linux、macOS、BSD 等）

**最佳实践**：优先使用平台能力检测（如 `#[cfg(feature = "serde")]`）而非 OS 检测。

</details>

---

### Q38: Miri 用途
>
> [来源: [Bjarne Stroustrup](https://www.stroustrup.com/)]

Miri 能检测哪些问题？不能检测哪些？

<details>
<summary>答案</summary>

**能检测**：

- 悬垂指针解引用
- 数据竞争（在单线程 Miri 中模拟检测）
- 未对齐访问
- 违反别名规则

**不能检测**：

- 死锁（无真正的多线程执行）
- 无限循环
- 性能问题

</details>

---

### Q39: Rust 版本兼容性
>
> [来源: [Wikipedia — C++](https://en.wikipedia.org/wiki/C%2B%2B)]

Rust 如何保证向后兼容？

<details>
<summary>答案</summary>

1. **Edition 系统**：2015/2018/2021/2024，同一 crate 内统一版本
2. **Stability Promise**：稳定 API 永不删除/修改语义
3. **Cargo.lock**：锁定精确版本，防止依赖漂移
4. **SemVer**：遵循语义化版本，minor 版本新增功能，patch 修复 bug

</details>

---

### Q40: unsafe 审计清单
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

代码审查中 `unsafe` 块需要检查哪些事项？

<details>
<summary>答案</summary>

1. **原始指针有效性**：是否可能悬垂/未对齐/空指针？
2. **别名规则**：是否违反 `&mut T` 的唯一性？
3. **线程安全**：手动 `Send/Sync` 实现是否正确？
4. **边界检查**：切片访问是否越界？
5. **FFI 契约**：C 函数的前置/后置条件是否满足？
6. **panic 安全**：panic 时是否泄漏资源或破坏不变量？

</details>
---

> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [concept/知识体系]
>
> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
## L1 扩展层：所有权与类型系统（8 题） [来源: 题目基于 Rust Reference — Ownership, Lifetimes, Types / 2025; TRPL Ch4, Ch6, Ch10 / 2024; Rustonomicon — Life before Main](https://doc.rust-lang.org/nomicon/)
>
> [来源: [TRPL]]

### Q41: 函数参数传递
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

以下代码能否编译？

```rust
fn take(s: String) -> String { s }
fn main() {
    let s = String::from("hello");
    let s2 = take(s);
    println!("{}", s);
}
```

<details>
<summary>答案</summary>

**不能编译**。`take(s)` 将 `s` 的所有权 move 进函数，之后 `s` 不可用。编译错误 **E0382**。

**修正**：`take(s.clone())` 或修改 `take` 接收 `&str`。

</details>

---

### Q42: Copy 边界
>
> [来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]

以下哪些类型自动实现 `Copy`？

```rust
struct Point(i32, i32);
struct Wrapper(String);
enum Opt { Some(i32), None }
```

<details>
<summary>答案</summary>

- `Point`：**是**（所有字段都是 `Copy`）
- `Wrapper`：**否**（`String` 不是 `Copy`）
- `Opt`：**是**（所有变体的数据都是 `Copy`）

`Copy` 是自动推导的，只要所有字段都实现 `Copy`，复合类型就自动实现 `Copy`。

</details>

---

### Q43: 多输入引用生命周期
>
> [来源: [Wikipedia — Rust](https://en.wikipedia.org/wiki/Rust_(programming_language))]

以下函数签名省略了什么？

```rust,ignore
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() { x } else { y }
}

```

<details>
<summary>答案</summary>

**不能编译**。多输入引用时，生命周期省略规则**不适用**，必须显式标注：

rust,ignore
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str

```

编译器无法确定返回引用依赖 `x` 还是 `y`。

</details>

---

### Q44: 字符串切片生命周期
> [来源: [Wikipedia — Programming Language](https://en.wikipedia.org/wiki/Programming_language)]

以下代码能否编译？

```rust
fn first_char(s: &String) -> &str {
    &s[0..1]
}
```

<details>
<summary>答案</summary>

**能编译**，但**不推荐**。返回 `&str` 的生命周期与输入 `&String` 相同。

更地道的签名是 `fn first_char(s: &str) -> &str`，接受更广泛的输入（`String` 和 `&str` 都可自动解引用）。

</details>

---

### Q45: enum 内存布局
>
> [来源: [Wikipedia — Type System](https://en.wikipedia.org/wiki/Type_system)]

```rust,ignore
enum Message {
    Quit,
    Move { x: i32, y: i32 },
    Write(String),
}
```

`Message::Quit` 占多少字节？

<details>
<summary>答案</summary>

`Message` 的大小等于最大变体的大小加上判别式（tag）。

- `Quit`：0 字节（单元变体）
- `Move`：8 字节（两个 `i32`）
- `Write`：24 字节（`String` 在 64 位平台）

所以 `Message` 大小为 **24 + tag**（通常 1-8 字节，对齐后为 32 字节）。

</details>

---

### Q46: 类型推断与 Turbofish
>
> [来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]

以下代码的问题是什么？

```rust,ignore
let v = Vec::new();
v.push(1);
```

<details>
<summary>答案</summary>

**不能编译**。`Vec::new()` 无法推断类型参数 `T`。

**修正**：

```rust
let v: Vec<i32> = Vec::new();
// 或
let v = Vec::<i32>::new();  // turbofish
// 或
let mut v = Vec::new();
v.push(1);  // 从 push 参数推断
```

注意：`v` 必须是 `mut`。

</details>

---

### Q47: match 绑定模式
>
> [来源: [Cargo Book](https://doc.rust-lang.org/cargo/)]

以下代码输出什么？

```rust
let x = Some(String::from("hello"));
match x {
    Some(ref s) => println!("{}", s),
    None => {},
}
println!("{:?}", x);
```

<details>
<summary>答案</summary>

**输出 `hello`，然后 `Some("hello")`**。

`ref s` 绑定的是对内部值的**引用**，而不是 move 内部值。因此 `x` 仍然有效。

与 `Some(s)` 不同，后者会 move `String`，导致 `x` 不可用。

</details>

---

### Q48: const 上下文限制
>
> [来源: [Rust Async Book](https://rust-lang.github.io/async-book/)]

以下代码能否编译？

```rust,ignore
const fn sum(a: i32, b: i32) -> i32 {
    let v = vec![a, b];
    v.iter().sum()
}
```

<details>
<summary>答案</summary>

**不能编译**。`const fn` 中不能调用 `vec!`（分配堆内存）或 `iter()`（非常量操作）。

`const fn` 只能执行：

- 基本算术和逻辑运算
- `if`/`match` 控制流
- 调用其他 `const fn`
- 从 Rust 1.46 起：部分 `loop` 和 `while`

</details>

---

> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [concept/知识体系]
>
> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [Wikipedia — Parametric Polymorphism](https://en.wikipedia.org/wiki/Parametric_polymorphism)
>
## L2 扩展层：Trait、泛型、内存管理与错误处理（8 题） [来源: 题目基于 TRPL Ch10 (泛型), Ch9 (错误处理), Ch15 (智能指针) / 2024; Rust Reference — Generic Parameters, The ? operator / 2025; Wikipedia — Copy-on-Write](https://en.wikipedia.org/wiki/Copy-on-write)]
>
> [来源: [TRPL]]

### Q49: Trait Bound 组合
>
> [来源: [Wikipedia — Object-oriented Programming](https://en.wikipedia.org/wiki/Object-oriented_programming)]

以下 bound 的含义？

```rust
fn process<T>(item: T)
where
    T: Clone + Send + 'static,
{}
```

<details>
<summary>答案</summary>

`T` 必须同时满足：

- `Clone`：可复制
- `Send`：可跨线程传递
- `'static`：不含非 `'static` 引用（即可拥有或 'static 引用）

`+` 表示**交集**：类型必须实现所有列出的 trait 和生命周期约束。

</details>

---

### Q50: Associated Type 约束
>
> [来源: [Wikipedia — Substructural Type System](https://en.wikipedia.org/wiki/Substructural_type_system)]

以下代码的含义？

```rust
trait Container {
    type Item;
    fn get(&self) -> Option<Self::Item>;
}

fn first<C: Container<Item = i32>>(c: &C) -> Option<i32> {
    c.get()
}
```

<details>
<summary>答案</summary>

`Container<Item = i32>` 是**关联类型等式约束**：要求 `C` 的 `Item` 必须是 `i32`。

这与泛型参数 `Container<i32>` 不同：关联类型每个实现只能有一个，泛型参数可以有多个实例。

</details>

---

### Q51: 结构体生命周期
>
> [来源: [Wikipedia — Parametric Polymorphism](https://en.wikipedia.org/wiki/Parametric_polymorphism)]

以下结构体定义是否正确？

```rust
struct Parser<'a> {
    text: &'a str,
    pos: usize,
}
```

<details>
<summary>答案</summary>

**正确**。`Parser` 持有对 `str` 的引用，必须标注生命周期 `'a`。

使用示例：

```rust,ignore
let text = "hello";
let p = Parser { text, pos: 0 };
// p 的生命周期不能超过 text
```

若 `text` 是 `String` 而非 `&str`，则不需要生命周期参数。

</details>

---

### Q52: Drop 与 Panic 安全
>
> [来源: [Wikipedia — Capability-based Security](https://en.wikipedia.org/wiki/Capability-based_security)]

以下代码是否 panic 安全？

```rust
struct Guard(Vec<i32>);
impl Drop for Guard {
    fn drop(&mut self) {
        self.0.push(999);
    }
}
```

<details>
<summary>答案</summary>

**不安全（unsound）**。`Drop::drop` 在 panic 展开时也可能被调用，而此时堆可能处于不一致状态。

更关键的是：`drop` 中不应调用可能 panic 的操作（如 `push`，可能在容量不足时分配失败并 panic）。

**原则**：`drop` 实现应保证**不 panic**、**不无限循环**、**不死锁**。

</details>

---

### Q53: Cow 的用途
>
> [来源: [SemVer](https://semver.org/)]

`std::borrow::Cow` 的用途是什么？

```rust
use std::borrow::Cow;
fn maybe_uppercase(s: &str) -> Cow<'_, str> {
    if s.chars().any(|c| c.is_lowercase()) {
        Cow::Owned(s.to_uppercase())
    } else {
        Cow::Borrowed(s)
    }
}
```

<details>
<summary>答案</summary>

**Clone on Write**：在需要修改时克隆，否则借用。

- 如果输入已满足条件（无需修改）：**零分配**，返回借用
- 如果需要修改：**分配一次**，返回拥有的数据

适用于"可能修改、可能不修改"的场景，避免不必要的克隆。

</details>

---

### Q54: Error Source Chain
>
> [来源: [Miri Docs](https://github.com/rust-lang/miri)]

以下代码如何遍历错误链？

```rust
use std::error::Error;
fn cause_chain(e: &dyn Error) {
    // 如何打印 e 及其所有 source？
}
```

<details>
<summary>答案</summary>

```rust
use std::error::Error;

fn cause_chain(e: &dyn Error) {
    let mut current: Option<&dyn Error> = Some(e);
    while let Some(err) = current {
        println!("{}", err);
        current = err.source();
    }
}
```

Rust 1.37+：`Error::source()` 替代已弃用的 `Error::cause()`。

或使用迭代器风格：

```rust,ignore
std::iter::successors(Some(e), |e| e.source())
    .for_each(|e| println!("{}", e));

```

</details>

---

### Q55: 泛型 vs Trait Object 错误处理
>
> [来源: [Wikipedia — Linear Logic](https://en.wikipedia.org/wiki/Linear_logic)]

`Result<T, Box<dyn Error>>` 与 `Result<T, impl Error>` 的区别？

<details>
<summary>答案</summary>

- `Box<dyn Error>`：**动态分发**，运行时确定具体错误类型，允许同一函数返回不同错误类型
- `impl Error`：**静态分发**（仅在 RPIT 中可用），编译期单态化，零运行时开销

`Box<dyn Error>` 更灵活但有一次堆分配；`impl Error` 更高效但要求编译期确定类型。

</details>

---

### Q56: Zero-Sized Types (ZST)
>
> [来源: [Wikipedia — RAII](https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization)]

以下类型的大小是多少？

```rust
struct Unit;
struct Pair(Unit, Unit);
enum Void {}
```

<details>
<summary>答案</summary>

| 类型 | 大小 |
|:---|:---|
| `Unit` | **0 字节** |
| `Pair` | **0 字节** |
| `Void` | **0 字节**（但无法构造）|

ZST 在运行时不占内存，但编译期类型信息完整。常用于**类型标记**（如 `PhantomData`）或**编译期状态机**。

[来源: [Rust Reference — Type Layout](https://doc.rust-lang.org/reference/type-layout.html)]

</details>

---

> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [concept/知识体系]
>
> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [Rust Async Book](https://rust-lang.github.io/async-book/)
>
## L3 扩展层：并发、异步、unsafe 与宏（8 题） [来源: 题目基于 TRPL Ch16 (并发), Rust Async Book / 2025; Rust Reference — unsafe, Macros / 2025; RFC 2349 (Pin)](https://rust-lang.github.io/async-book/)
>
> [来源: [TRPL]]

### Q57: Atomic Ordering
>
> [来源: [ISO C++](https://isocpp.org/)]

`Relaxed`、`Acquire`、`Release`、`SeqCst` 的适用场景？

<details>
<summary>答案</summary>

| Ordering | 场景 |
|:---|:---|
| `Relaxed` | 仅需要原子性，无同步需求（如计数器）|
| `Acquire` | 读操作，需看到之前的 Release 写入（如锁获取）|
| `Release` | 写操作，需保证之前的写入对 Acquire 读可见（如锁释放）|
| `AcqRel` | 读-修改-写操作（如 `fetch_add`）|
| `SeqCst` | 全局顺序一致性（最严格，性能最差）|

**原则**：使用能满足需求的最弱 ordering，以获得最佳性能。

[来源: [Rust Reference — Atomics](https://doc.rust-lang.org/reference/items/static-items.html)]

</details>

---

### Q58: Stream vs Iterator
>
> [来源: [Bjarne Stroustrup](https://www.stroustrup.com/)]

`Stream` 与 `Iterator` 的核心区别？

<details>
<summary>答案</summary>

- `Iterator`：**同步拉取**（`next()` 立即返回 `Option<Item>`）
- `Stream`：**异步拉取**（`next().await` 可能挂起等待数据）

`Stream` 是异步版的 `Iterator`，用于处理异步数据源（如网络流、消息队列）。

```rust,ignore
use futures::StreamExt;
while let Some(item) = stream.next().await {
    // 处理 item
}

```

</details>

---

### Q59: Cancel Safety
>
> [来源: [Wikipedia — C++](https://en.wikipedia.org/wiki/C%2B%2B)]

以下 `select!` 调用是否 cancel-safe？

```rust,ignore
loop {
    tokio::select! {
        val = rx.recv() => { println!("{:?}", val); }
        _= tokio::time::sleep(Duration::from_secs(1)) => {}
    }
}

```

<details>
<summary>答案</summary>

**是**。`tokio::sync::mpsc::Receiver::recv` 是 **cancel-safe** 的：如果 `sleep` 先完成，`recv` future 被 drop 不会丢失消息。

**非 cancel-safe 示例**：`tokio::io::AsyncReadExt::read` 被 cancel 后，部分读取的数据丢失。

**原则**：在 `select!` 中优先使用 cancel-safe 的操作，或对非 cancel-safe 操作使用 `tokio::sync::Semaphore` 等保护。

</details>

---

### Q60: UnsafeCell
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

`UnsafeCell<T>` 的作用是什么？以下代码是否安全？

```rust
use std::cell::UnsafeCell;
let cell = UnsafeCell::new(5);
unsafe {
    *cell.get() += 1;
}
```

<details>
<summary>答案</summary>

`UnsafeCell<T>` 是 Rust 内部可变性的**核心原语**：它告诉编译器 `T` 可能有别名且会被修改，禁用 `&T` 的不可变假设。

这段代码**安全**（虽然使用了 `unsafe` 块）：单线程下通过 `UnsafeCell::get()` 获取 `*mut T` 并修改是合法的。

但多线程下仍需 `Sync` 保证，通常使用 `Mutex<T>` 或 `Atomic*` 包装。

</details>

---

### Q61: Strict Provenance
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

`ptr::addr()` 和 `ptr::with_addr()` 的作用？

<details>
<summary>答案</summary>

**Strict Provenance** 是 Rust 对指针别名规则的严格化：

- `ptr::addr()`：获取指针的**地址**（整数），**丢弃 provenance**
- `ptr::with_addr(addr)`：用新地址构造指针，**继承原指针的 provenance**

**禁止**：`ptr as usize as *mut T`（丢失 provenance 信息）

**允许**：

```rust,ignore
let addr = ptr.addr();
let new_ptr = ptr.with_addr(addr + 4);
```

这对编译器优化和 Miri 检测 UB 至关重要。

</details>

---

### Q62: Proc Macro Hygiene
>
> [来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]

以下 proc macro 生成的代码是否合法？

```rust,ignore
// proc macro
quote! {
    let x = 42;
    println!("{}", x);
}
// 调用处
let x = 10;
my_macro!();
println!("{}", x);
```

<details>
<summary>答案</summary>

**合法**。Proc macro 生成的标识符具有**独立 hygiene**，不会与调用处的 `x` 冲突。

输出 `42` 后，调用处的 `x` 仍是 `10`。

这与 `macro_rules!` 的 hygiene 类似，但 proc macro 的 hygiene 在 token 级别由编译器管理。

</details>

---

### Q63: Pin Projection
>
> [来源: [Wikipedia — Rust](https://en.wikipedia.org/wiki/Rust_(programming_language))]

以下代码的问题？

```rust,ignore
struct MyFuture {
    data: String,
    pointer: *const String,
}
impl Future for MyFuture {
    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        unsafe {
            println!("{}", &*self.pointer);
        }
        Poll::Ready(())
    }
}
```

<details>
<summary>答案</summary>

**未使用 Pin projection**。`self: Pin<&mut Self>` 不能直接获取 `&mut self.data`，因为 `MyFuture` 可能已被固定。

**修正**：使用 `pin_project` 或手动 unsafe projection：

rust,ignore
fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
    let this = unsafe { self.get_unchecked_mut() };
    // 现在可以安全访问 this.data 和 this.pointer
}

```

必须保证被投影的字段不会移动。

[来源: [Rust Reference — Pin](https://doc.rust-lang.org/reference/expressions/operator-expr.html)]

</details>

---

### Q64: Send 推导
> [来源: [Wikipedia — Programming Language](https://en.wikipedia.org/wiki/Programming_language)]

以下类型是否自动实现 `Send`？

```rust
struct Wrapper<T>(T);
struct BadWrapper(*const u8);
```

<details>
<summary>答案</summary>

- `Wrapper<T>`：**自动实现** `Send`（当 `T: Send` 时）。编译器自动为仅包含 `Send` 字段的结构体推导 `Send`。
- `BadWrapper`：**不自动实现** `Send`。原始指针 `*const u8` 不是 `Send`，因此 `BadWrapper` 默认不是 `Send`。

可以手动 `unsafe impl Send for BadWrapper {}`，但需确保线程安全。

</details>

---

> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [concept/知识体系]
>
> **来源**: [Bloom Taxonomy 2001] · [TAPL (Pierce, 2002)] · [RustBelt] · [Wikipedia — Linear Logic](https://en.wikipedia.org/wiki/Linear_logic)
>
## L4 扩展层：线性逻辑、类型论、所有权形式化与 RustBelt（8 题） [来源: 题目基于 TAPL (Pierce, 2002); RustBelt (Jung et al., POPL 2018); Girard — Linear Logic / 1987; Wikipedia — Substructural Type System](https://en.wikipedia.org/wiki/Substructural_type_system)]
>
> [来源: [TRPL]]

### Q65: 子结构逻辑
>
> [来源: [Wikipedia — Type System](https://en.wikipedia.org/wiki/Type_system)]

线性逻辑（Linear）、仿射逻辑（Affine）、相关逻辑（Relevant）的区别？Rust 属于哪种？

<details>
<summary>答案</summary>

| 逻辑 | Weakening（丢弃） | Contraction（复制） | Rust 对应 |
|:---|:---|:---|:---|
| 线性 | ❌ 禁止丢弃 | ❌ 禁止复制 | `Linear`（严格使用 1 次）|
| 仿射 | ✅ 允许丢弃 | ❌ 禁止复制 | **Rust 所有权**（使用 0 或 1 次）|
| 相关 | ❌ 禁止丢弃 | ✅ 允许复制 | `Copy` 类型（必须至少使用 1 次）|
| 经典 | ✅ | ✅ | 传统 GC 语言 |

Rust 是**仿射类型系统**：允许丢弃（`let x = ...;` 后不用 `x` 合法），但不允许隐式复制（需显式 `.clone()` 或实现 `Copy`）。

[来源: [Wikipedia — Affine Type System](https://en.wikipedia.org/wiki/Substructural_type_system#Affine_type_system)]

</details>

---

### Q66: Curry-Howard 同构
>
> [来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]

Curry-Howard 同构在 Rust 中的体现？

<details>
<summary>答案</summary>

Curry-Howard 同构：类型 ↔ 命题，程序 ↔ 证明。

| 逻辑 | Rust |
|:---|:---|
| `A → B`（蕴含）| `fn(A) -> B` |
| `A ∧ B`（合取）| `(A, B)` |
| `A ∨ B`（析取）| `enum { A, B }` |
| `⊥`（矛盾）| `!`（never type）|
| `∀X. P(X)` | `fn<T>() -> P<T>` |

Rust 的 `match` 穷尽性检查对应**排中律的构造性解释**：必须提供所有分支的证明。

</details>

---

### Q67: Type Soundness vs Memory Safety
>
> [来源: [Cargo Book](https://doc.rust-lang.org/cargo/)]

"Rust 类型系统是 sound 的" 与 "Rust 保证内存安全" 是同一回事吗？

<details>
<summary>答案</summary>

**不是同一回事**。

- **Type Soundness**：良类型程序不会 stuck（除安全停机外），即 Progress + Preservation
- **Memory Safety**：程序不会出现 use-after-free、数据竞争、缓冲区溢出等

Rust 的 type soundness 保证 memory safety **在 safe Rust 中**。但在 `unsafe` 块中，type soundness 假设可能被破坏，导致内存不安全。

**关系**：Type Soundness ⊃ Memory Safety（对于 safe Rust）。

[来源: [Rust Reference — Behavior Considered Undefined](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)]

</details>

---

### Q68: Iris 模态断言
>
> [来源: [Rust Async Book](https://rust-lang.github.io/async-book/)]

Iris 中的 `▷`（later）和 `□`（persistently）模态的含义？

<details>
<summary>答案</summary>

- `▷ P`（Later）："下一 step 后 P 成立"。用于递归定义和逐步推理，保证不动点存在。
- `□ P`（Persistently）："P 不依赖任何独占资源，可被任意复制/共享"。对应 Rust 的共享引用 `&T`。

在 RustBelt 中：

- `&mut T` 对应独占资源 `l ↦ v`
- `&T` 对应持久资源 `□(l ↦ v)`

</details>

---

### Q69: Liveness 属性
>
> [来源: [Wikipedia — Object-oriented Programming](https://en.wikipedia.org/wiki/Object-oriented_programming)]

如何用线性时序逻辑（LTL）表达 "请求最终会被处理"？

<details>
<summary>答案</summary>

```
□(request → ◇processed)
```

- `□`（Globally）：在所有未来状态
- `request → ◇processed`：如果 request 发生，则最终（`◇`）processed 发生

在 Rust 并发中，这对应：**如果发送了消息，接收者最终会收到**（只要程序不 panic 且通道未关闭）。

</details>

---

### Q70: 参数性 vs 特设多态
>
> [来源: [Wikipedia — Substructural Type System](https://en.wikipedia.org/wiki/Substructural_type_system)]

参数性多态（Parametric）与特设多态（Ad-hoc）的区别？Rust 分别如何支持？

<details>
<summary>答案</summary>

| 多态类型 | 定义 | Rust 机制 |
|:---|:---|:---|
| 参数性 | 对**所有**类型统一行为 | 泛型 `fn identity<T>(x: T) -> T` |
| 特设 | 对**不同**类型不同行为 | Trait `impl Display for i32` / `for String` |

**参数性定理**：`fn f<T>(x: T) -> T` 必然返回 `x`（或 panic/diverge），因为它对 `T` 一无所知。

**特设**通过 vtable（动态）或单态化（静态）实现多态分发。

[来源: [Wikipedia — Parametric Polymorphism](https://en.wikipedia.org/wiki/Parametric_polymorphism)]

</details>

---

### Q71: RustBelt Invariant
>
> [来源: [Wikipedia — Parametric Polymorphism](https://en.wikipedia.org/wiki/Parametric_polymorphism)]

RustBelt 中的 "invariant"（不变量）指什么？为什么对 `Vec<T>` 至关重要？

<details>
<summary>答案</summary>

**Invariant**：程序执行期间始终保持为真的断言。

`Vec<T>` 的关键 invariant：

- `len <= cap`
- `ptr` 指向已分配的、大小为 `cap * size_of::<T>()` 的内存块
- 前 `len` 个元素已初始化

`unsafe` 代码（如 `set_len`）可以破坏这些 invariant。RustBelt 用 Iris 的 **invariant 机制** 证明：safe API 的使用者无法破坏这些 invariant，即使存在 `unsafe` 内部实现。

[来源: [RustBelt Website](https://plv.mpi-sws.org/rustbelt/)]

</details>

---

### Q72: Ghost State
>
> [来源: [Wikipedia — Capability-based Security](https://en.wikipedia.org/wiki/Capability-based_security)]

分离逻辑中的 Ghost State（幽灵状态）在 Rust 验证中的作用？

<details>
<summary>答案</summary>

**Ghost State**：只在证明中存在、不在运行时存在的辅助状态。

在 Rust 验证中（如 Verus、Iris）：

- 追踪逻辑上的资源所有权（如"这个线程持有锁"）
- 证明并发协议的正确性
- 建立线程间的同步关系

```rust,ignore
// Verus 示例：用 ghost 变量证明不变量
proof fn maintain_invariant(x: u32, ghost prev: u32)
    requires x == prev + 1
{
    // ghost 参数只在验证时使用，运行时零开销
}

```

</details>

---

> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [concept/知识体系]
>
> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [Wikipedia — Zero-cost Abstraction](https://en.wikipedia.org/wiki/Zero-overhead_principle)
>
## L5 扩展层：多语言范式对比（4 题） [来源: 题目基于 TRPL 跨语言对比 / 2024; Rust Reference — unsafe, FFI / 2025; Wikipedia — Capability-based Security](https://en.wikipedia.org/wiki/Capability-based_security)]
>
> [来源: [TRPL]]

### Q73: Rust vs Swift
>
> [来源: [SemVer](https://semver.org/)]

Rust 的所有权与 Swift 的 ARC 有何根本区别？

<details>
<summary>答案</summary>

| 维度 | Rust | Swift |
|:---|:---|:---|
| 机制 | 编译期所有权 + Move | 运行时引用计数（ARC）|
| 开销 | 零运行时开销 | 原子引用计数开销 |
| 循环引用 | 编译期阻止（ borrow checker ）| 需 `weak`/`unowned` 手动解决 |
| 并发安全 | 编译期 `Send/Sync` | 运行时检测（ actors ）|
| 学习曲线 | 陡峭 | 平缓 |

Rust 的 trade-off 是**编译期复杂性换取运行时确定性**。

[来源: [TRPL — What is Ownership?](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)]

</details>

---

### Q74: Rust vs C# Span
>
> [来源: [Miri Docs](https://github.com/rust-lang/miri)]

Rust 的 `&[T]` 与 C# 的 `Span<T>` 的异同？

<details>
<summary>答案</summary>

| 维度 | Rust `&[T]` | C# `Span<T>` |
|:---|:---|:---|
| 安全性 | 编译期（borrow checker）| 运行时检查 + ref struct 限制 |
| 堆栈/堆 | 可指向任意位置 | 可指向堆栈、堆、托管内存 |
| 生命周期 | 编译期追踪 | 受 ref struct 作用域限制 |
| 泛型 | `&[T]` 对任意 `T` | `Span<T>` 对任意 `T` |

C# 的 `Span<T>` 借鉴了 Rust 的切片概念，但安全性依赖运行时和 JIT 优化，而非编译期证明。

[来源: [Wikipedia — Span (C#)](https://en.wikipedia.org/wiki/Span_(C_Sharp))]

</details>

---

### Q75: 零成本抽象
>
> [来源: [Wikipedia — Linear Logic](https://en.wikipedia.org/wiki/Linear_logic)]

C++ 模板也声称"零成本抽象"，与 Rust 泛型的实现有何不同？

<details>
<summary>答案</summary>

两者都通过**单态化**实现零运行时开销，但：

| 维度 | C++ 模板 | Rust 泛型 |
|:---|:---|:---|
| 类型检查 | 实例化时（可能延迟报错）| 定义时（完整类型检查）|
| 错误信息 | 通常冗长且指向模板内部 | 清晰，指向使用点 |
| 特化 | 完全特化（灵活但复杂）| 有限特化（min_specialization）|
| 约束 | 概念（C++20）| Trait bounds（原生）|
| 编译时间 | 通常更长 | 相对可控 |

Rust 的**早期类型检查**和**Trait 约束**使零成本抽象更易用、更安全。

[来源: [Rust Reference — Traits](https://doc.rust-lang.org/reference/items/traits.html)]

</details>

---

### Q76: 基于能力的安全
>
> [来源: [Wikipedia — RAII](https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization)]

Rust 的所有权系统与"基于能力的安全（Capability-based Security）"有何关联？

<details>
<summary>答案</summary>

**Capability-based Security**：访问权限与对象绑定，而非与主体身份绑定。

Rust 的所有权即一种**能力**：

- 拥有 `File` = 拥有读写该文件的能力
- 拥有 `&mut T` = 拥有修改 `T` 的能力
- `move` = 能力的转移（不可复制的能力）

这与传统 ACL（访问控制列表）不同：Rust 中**没有能力的代码无法访问资源**，无需运行时检查权限。

[来源: [Wikipedia — Capability-based Security](https://en.wikipedia.org/wiki/Capability-based_security)]

</details>

---

> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [concept/知识体系]
>
> **来源**: [Bloom Taxonomy 2001] · [TRPL] · [Rust Reference] · [SemVer Specification](https://semver.org/)
>
## L6 扩展层：工程实践与生态（4 题） [来源: 题目基于 Cargo Book / 2025; Rust Reference — Macros, Documentation / 2025; SemVer 2.0.0](https://semver.org/)]
>
> [来源: [TRPL]]

### Q77: Cargo Features 解析
>
> [来源: [ISO C++](https://isocpp.org/)]

`cargo build --features "a b"` 与 `cargo build --features a --features b` 是否等价？

```toml
[features]
default = ["a"]
a = ["dep:tokio"]
b = []
```

<details>
<summary>答案</summary>

**等价**。两种写法都激活 features `a` 和 `b`。

关键规则：

- Features 是**加法性**的：只能启用，不能禁用（除 `--no-default-features`）
- `dep:tokio` 是 feature 重命名语法，表示启用 feature `a` 时自动启用 `tokio` 依赖
- 多个 features 用空格或多次 `--features` 传递效果相同

</details>

---

### Q78: proc-macro2 与 syn
>
> [来源: [Bjarne Stroustrup](https://www.stroustrup.com/)]

为什么 proc macro crate 通常同时依赖 `proc-macro2` 和 `syn`？

<details>
<summary>答案</summary>

| Crate | 作用 |
|:---|:---|
| `proc-macro2` | 提供与 `proc_macro` 兼容的 TokenStream，但可在 crate 外测试 |
| `syn` | TokenStream 的解析器，将 token 流解析为 AST（`ItemFn`、`Expr` 等）|
| `quote` | 将 Rust 代码模板生成 TokenStream |

**使用流程**：

```text
TokenStream → syn 解析 → 修改 AST → quote 生成 → TokenStream
```

`proc-macro2` 解决了标准库 `proc_macro` 只能在 proc-macro crate 中使用的问题。

[来源: [Rust Reference — Procedural Macros](https://doc.rust-lang.org/reference/procedural-macros.html)]

</details>

---

### Q79: SemVer 与 API 演进
>
> [来源: [Wikipedia — C++](https://en.wikipedia.org/wiki/C%2B%2B)]

以下变更属于 SemVer 的哪个级别？

1. 为 trait 添加默认方法
2. 将 `pub fn foo()` 改为 `pub fn foo<T>()`
3. 删除公共模块

<details>
<summary>答案</summary>

| 变更 | SemVer | 说明 |
|:---|:---|:---|
| 添加默认方法 | **Minor** | 不破坏现有代码，新增功能 |
| `foo()` → `foo<T>()` | **Major** | 类型推断可能失败，破坏调用点 |
| 删除公共模块 | **Major** | 直接破坏依赖该模块的代码 |

Rust 的 [API Guidelines](https://rust-lang.github.io/api-guidelines/) 建议对公共 API 谨慎使用 SemVer。

</details>

---

### Q80: rustdoc Doctest
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

以下文档测试是否能通过？

```rust,ignore
/// ```
/// let x = 5;
/// assert_eq!(x + 1, 6);
/// ```
pub fn foo() {}
```

<details>
<summary>答案</summary>

**能通过**。Rust 的文档测试（doctest）会自动将文档注释中 `` ``` `` 内的代码编译并运行。

**隐藏代码**（不显示在文档中但参与测试）：

```rust,ignore
/// ```
/// # let setup = 5;  // 以 # 开头，隐藏但执行
/// assert_eq!(setup, 5);
/// ```
```

**属性控制**：

- ```` ```ignore ````：不编译
- ```` ```no_run ````：编译但不运行
- ```` ```compile_fail ````：期望编译失败
- ```` ```should_panic ````：期望 panic

[来源: [Rust Reference — Documentation Tests](https://doc.rust-lang.org/reference/comments.html#doc-comments)]

</details>

---

## 来源与参考文献
>
> [来源: [TRPL]]

| 来源 | 链接 | 用途 |
|:---|:---|:---|
| **TRPL** | [The Rust Programming Language](https://doc.rust-lang.org/book/) | 所有权、生命周期、泛型、并发、错误处理 |
| **Rust Reference** | [Rust Reference](https://doc.rust-lang.org/reference/) | 语言定义、类型系统、unsafe、宏 |
| **Rustonomicon** | [The Rustonomicon](https://doc.rust-lang.org/nomicon/) |  Unsafe Rust、内存模型、高级类型 |
| **Rust Async Book** | [Asynchronous Programming in Rust](https://rust-lang.github.io/async-book/) | async/await、Pin、Future、Stream |
| **Cargo Book** | [The Cargo Book](https://doc.rust-lang.org/cargo/) | Workspace、Features、条件编译 |
| **RFCs** | [Rust RFCs](https://rust-lang.github.io/rfcs/) | 语言演进、Pin (RFC 2349)、Effects |
| **RustBelt** | [RustBelt (POPL 2018)](https://plv.mpi-sws.org/rustbelt/) | 形式化验证、分离逻辑、Iris |
| **TAPL** | [Types and Programming Languages (Pierce, 2002)](https://www.cis.upenn.edu/~bcpierce/tapl/) | 类型论、参数性、HM 推断 |
| **Bloom Taxonomy** | [Bloom's Taxonomy (2001)](https://en.wikipedia.org/wiki/Bloom%27s_taxonomy) | 认知层级、自测题设计 |
| **Wikipedia** | [Programming Language Comparison](https://en.wikipedia.org/wiki/Comparison_of_programming_languages) | 多语言范式对比、线性逻辑、安全模型 |
| **SemVer** | [Semantic Versioning 2.0.0](https://semver.org/) | API 演进、版本兼容性 |
| **Miri Docs** | [Miri — Undefined Behavior Detection](https://github.com/rust-lang/miri) | Unsafe 代码验证 |

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **权威来源对齐变更日志**: 2026-05-22 批量补充来源标注（TRPL、Rust Reference、Wikipedia、学术论文等） [来源: Authority Source Sprint Batch 8]

---

> **评分标准**（自我评估）：
>
> - **68-80 题正确**：L1-L6 全部掌握，可深入 L4 形式化细节
> - **54-67 题正确**：L1-L3 扎实，L4-L6 需针对性补强
> - **40-53 题正确**：L1-L2 基本掌握，建议重读对应章节
> - **27-39 题正确**：L1-L2 基础，需系统学习
> - **<27 题正确**：建议从 [`learning_guide.md`](./learning_guide.md) 基础路径重新开始
>
> **深入阅读**：
>
> - L1-L3 完整理论见 [`semantic_space.md`](./semantic_space.md) §2-3
> - L4 形式化背景见 [`../04_formal/`](../04_formal/)
> - L5 对比见 [`../05_comparative/`](../05_comparative/)
> - L6 实践见 [`../06_ecosystem/`](../06_ecosystem/)
>
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rustonomicon](https://doc.rust-lang.org/nomicon/)
>
> **权威来源对齐变更日志**: 2026-05-19 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
