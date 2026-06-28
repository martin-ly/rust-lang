# 所有权模型综合指南 / Ownership Model Comprehensive Guide

> **Bloom 层级**: 分析/评价/创造 (L5–L6)
> **工具/论文**: RustBelt (POPL 2018), Aeneas (ICFP 2022), Stacked/Tree Borrows, Ferrocene Language Specification
> **状态**: ✅ 已提炼归档
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **最后更新**: 2026-06-25
> **权威来源**: [Rust Reference — Ownership](https://doc.rust-lang.org/reference/ownership.html), [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/), [Aeneas](https://arxiv.org/abs/2206.07185), [Tree Borrows (PLDI 2025)](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
> **受众**: [进阶] / [专家]
> **内容分级**: [综述级]
> 本文内容来自已归档的 `docs/research_notes/formal_methods/10_ownership_model.md`，经提炼后迁移。

---

## 📋 目录

- [所有权模型综合指南 / Ownership Model Comprehensive Guide](.#所有权模型综合指南--ownership-model-comprehensive-guide)
  - [📋 目录](.#-目录)
  - [🎯 学习目标 / 概述](.#-学习目标--概述)
  - [1. 所有权作为权限/资源模型](.#1-所有权作为权限资源模型)
    - [1.1 移动、复制与借用](.#11-移动复制与借用)
    - [1.2 可变/共享与唯一性](.#12-可变共享与唯一性)
  - [2. 形式化直觉](.#2-形式化直觉)
    - [2.1 线性/仿射逻辑映射](.#21-线性仿射逻辑映射)
    - [2.2 分数权限](.#22-分数权限)
    - [2.3 区域类型与生命周期](.#23-区域类型与生命周期)
  - [3. 线程安全语义：Send / Sync / Pin / Unpin](.#3-线程安全语义send--sync--pin--unpin)
  - [4. CVE 与违反所有权规则的真实案例](.#4-cve-与违反所有权规则的真实案例)
  - [5. Aeneas / LLBC 与 RustBelt / Iris 视角](.#5-aeneas--llbc-与-rustbelt--iris-视角)
    - [5.1 Aeneas：函数式翻译](.#51-aeneas函数式翻译)
    - [5.2 RustBelt / Iris：分离逻辑](.#52-rustbelt--iris分离逻辑)
    - [5.3 两者互补](.#53-两者互补)
  - [6. 与概念文档的衔接](.#6-与概念文档的衔接)
  - [💻 可运行示例](.#-可运行示例)
    - [示例 1：所有权链与部分移动](.#示例-1所有权链与部分移动)
    - [示例 2：借用链与传递性](.#示例-2借用链与传递性)
    - [示例 3：共享只读到独占写入的切换](.#示例-3共享只读到独占写入的切换)
  - [📚 权威来源索引](.#-权威来源索引)

---

## 🎯 学习目标 / 概述

本文将 Rust 所有权系统提炼为**可组合的资源/权限模型**：每个值在任意时刻只存在一份独占所有权；所有权可通过移动转移、通过复制拆分、通过借用临时委托。理解这套模型后，可解释编译器为何能静态排除空指针、悬垂指针、use-after-free 与数据竞争，并能在阅读 RustBelt、Aeneas 等学术工具时建立直觉。

学习本文后，你应能：

1. 用「权限 token」重新描述 move、copy、borrow、mutable/shared、uniqueness。
2. 把所有权规则对应到线性/仿射逻辑、分数权限、区域类型。
3. 从语义层面解释 `Send`/`Sync`/`Pin`/`Unpin` 的设计。
4. 识别 CVE/bug 中所有权/借用不变量被破坏的根因。
5. 比较 Aeneas 的函数式翻译与 RustBelt/Iris 的分离逻辑方法。

---

## 1. 所有权作为权限/资源模型

Rust 所有权的本质不是「谁持有指针」，而是**谁持有对某段内存的合法操作权限**。每个 owned 值都附带一个不可伪造的 token；token 决定能否读、写、释放或共享该值。

### 1.1 移动、复制与借用

| 操作 | 权限变化 | Rust 语法 | 形式化含义 |
| :--- | :--- | :--- | :--- |
| **Move** | token 完全转移 | `let y = x;` | `Ω(x) = Moved`, `Ω(y) = Owned` |
| **Copy** | token 复制为等价 token | `let y = x;` (`T: Copy`) | `Ω(x)=Owned`, `Ω(y)=Owned`，值按位副本 |
| **不可变借用** | 分出只读分数权限 | `let r = &x;` | `Ω(x)=Owned`，持有 `q∈(0,1)` 读取份额 |
| **可变借用** | 临时出让独占写入权限 | `let r = &mut x;` | `Ω(x)=Owned`，`r` 独占 `x` 直至归还 |

移动使原变量失去 token，因此后续访问会在类型系统层面被拒绝；复制保留原 token，故两端仍可使用；借用不转移 token，只是临时附加约束。

```rust
fn move_copy_borrow() {
    let s = String::from("hello"); // s 持有 token
    let t = s;                     // move：token 转到 t
    // println!("{}", s);          // 错误：s 不再持有 token

    let n = 42;                    // i32: Copy
    let m = n;                     // 复制 token
    println!("{} {}", n, m);       // OK

    let r = &t;                    // 借出只读权限
    println!("{} {}", t, r);       // OK：t 仍拥有 token
} // 借用与 t 按作用域释放
```

### 1.2 可变/共享与唯一性

Rust 借用规则可概括为**「共享不可变，可变不共享」**：

- 任意多个 `&T` 可同时存在（共享只读）。
- 一个 `&mut T` 存在时，不能再有其它 `&T` 或 `&mut T` 指向同一数据。
- 所有权 token 始终保留在原变量，借用结束后自动归还。

这一规则等价于**读写锁的编译期版本**：读锁可并发，写锁独占。它保证 Safe Rust 不会出现数据竞争。

```rust
fn shared_vs_unique() {
    let mut v = vec![1, 2, 3];

    let r1 = &v;      // 共享只读开始
    let r2 = &v;
    println!("{} {}", r1.len(), r2.len());

    // let r3 = &mut v; // 错误：共享期间不可变

    let _ = (r1, r2); // 显式结束共享只读（或等待作用域结束）

    let r3 = &mut v;  // 现在可独占写入
    r3.push(4);
} // r3 归还 token，v 正常 drop
```

> **唯一性（uniqueness）**是 Rust 安全保证的根基。`&mut T` 不仅是「可变引用」，更是**一段时期内对 `T` 的唯一访问通道**；编译器可据此重排、优化并拒绝别名冲突。

---

## 2. 形式化直觉

### 2.1 线性/仿射逻辑映射

Rust 的所有权系统可看作**子结构类型系统（substructural type system）**的实例：

| 类型系统概念 | Rust 对应 | 使用次数 |
| :--- | :--- | :--- |
| 线性（Linear） | 必须恰好使用一次 | `String` 等 owned 值 |
| 仿射（Affine） | 最多使用一次 | 大多数 Move 类型 |
| 相关（Relevant） | 可任意使用 | `Copy` 类型如 `i32`、`&T` |

`let y = x;` 对 Move 类型是**收缩（contraction）的禁用**：不能把同一个资源用两次；对 Copy 类型则是收缩允许，因此可重复使用。

分离逻辑（Separation Logic）为借用提供自然解释：

- `P * Q`：两个断言持有不相交的资源，对应两个独立所有者。
- `P → Q`（magic wand）：若把 `P` 的资源还回，则得到 `Q`；对应可变借用结束后原变量恢复更新后的值。
- Frame Rule：借用不破坏周围所有权环境。

### 2.2 分数权限

不可变借用 `&T` 可视为把所有权拆分为**分数权限（fractional permissions）**：每个 `&T` 持有 `q ∈ (0,1)` 的读取份额，所有份额之和不超过 1。可变借用 `&mut T` 则持有完整 1 份并附带排他标记，故不能再拆分。

RustBelt/Iris 的资源代数可写作：

```text
OwnState := Owned | Borrowed_Imm(q) | Borrowed_Mut | Moved
(m₁, v) · (m₂, v) = (m₁+m₂, v)   if both Borrowed_Imm 且值相同
(m₁, v) · (m₂, v) = undefined    if both Borrowed_Mut
```

分数权限解释了为何多个 `&T` 能共存：它们只是同一资源的多个只读份额；而 `&mut T` 会冲突，因为资源已被完整占用。

### 2.3 区域类型与生命周期

生命周期 `'a` 本质上是**区域类型（region types）**的语法糖：把引用的有效时间建模为一个作用域集合。区域子类型规则为：

```text
ℓ₂ <: ℓ₁  iff  scope(ℓ₁) ⊇ scope(ℓ₂)
```

即「活得长的是活得短的超类型」。Rust 编译器通过约束生成与约束求解（类似 Tofte–Talpin 区域推断）为每个引用分配最小生命周期，并拒绝 `scope(r) ⊈ scope(owner)` 的程序。

```rust
fn region_subtyping<'a, 'b>(x: &'a i32, y: &'b i32) -> &'a i32
where
    'a: 'b, // 'a 包含 'b
{
    x // 返回较长生命周期的引用是安全的
}
```

更深入的 lifetime formalization 见 `docs/research_notes/formal_methods/lifetime_formalization.md`。

---

## 3. 线程安全语义：Send / Sync / Pin / Unpin

| Trait | 语义 | 直观含义 |
| :--- | :--- | :--- |
| `Send` | `T: Send` 表示把值**转移**到另一线程后，原线程不再访问 | 独占资源可安全跨线程 |
| `Sync` | `T: Sync` 表示 `&T` 可在多线程间安全共享 | 共享只读不引发数据竞争 |
| `Pin<P>` | 保证 `P` 指向的值地址固定，不会被 move | 自引用结构的安全前提 |
| `Unpin` | 表示该类型即使被 `Pin` 包装也允许安全移动 | `Pin` 的「退出阀门」 |

关键定理：`Sync(T) ⟺ Send(&T)`。因为共享 `&T` 跨线程等价于把 `&T` 这个值发送到另一线程。

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn send_sync_semantics() {
    let data: Arc<Mutex<Vec<i32>>> = Arc::new(Mutex::new(vec![1, 2, 3]));

    let data_clone = Arc::clone(&data);      // Arc 复制计数，不转移所有权
    thread::spawn(move || {                  // move 把 clone 的 Arc 发送到新线程
        data_clone.lock().unwrap().push(4);  // Mutex 提供可变访问的互斥
    });

    data.lock().unwrap().push(5);
} // 两个 Arc 都 drop 后才释放 Vec
```

`Pin` 解决自引用问题：当结构体内部指针指向自己的字段时，整体移动会让内部指针悬垂。`Pin<Box<SelfReferential>>` 承诺该内存位置固定。

```rust
use std::marker::PhantomPinned;

struct SelfReferential {
    data: String,
    _pin: PhantomPinned,
}

fn pin_semantics() {
    let sr = Box::pin(SelfReferential {
        data: String::from("pinned"),
        _pin: PhantomPinned,
    });

    // sr 无法被 move；内部潜在自引用保持有效
    assert_eq!(sr.data, "pinned");
}
```

---

## 4. CVE 与违反所有权规则的真实案例

下表总结源码中提到的 CVE/bug，并指出被破坏的所有权不变量：

| CVE / Bug | 被破坏的不变量 | Rust 防护 |
| :--- | :--- | :--- |
| **CVE-2015-0235** (Ghost, glibc) | 悬垂指针/缓冲区溢出 | 借用规则 8：`scope(r) ⊆ scope(owner)` |
| **CVE-2018-1000810** (`str::repeat`) | 整数溢出导致内存破坏 | Safe Rust 边界检查 + 借用唯一性 |
| **CVE-2019-15548** (generator 自引用) | 移动自引用结构导致悬垂 | `Pin<T>` 类型系统级解决方案 |
| **CVE-2020-36323** (regex 并发) | 跨线程共享可变状态 | `Send`/`Sync` trait 边界 |
| **CVE-2021-29941** (`VecDeque` 迭代器失效) | 迭代时修改集合 | 借用检查器阻止 `&vec` 与 `&mut vec` 共存 |

这些案例说明：所有权/借用规则不是为了「增加编译器负担」，而是把历史上高发的内存安全与并发错误转为**编译期错误**。

---

## 5. Aeneas / LLBC 与 RustBelt / Iris 视角

### 5.1 Aeneas：函数式翻译

[Aeneas](https://github.com/AeneasVerif/aeneas) 把 Safe Rust 翻译为函数式语言（Coq/HOL4/Lean/F*），用**预言变量（Prophecy Variables）**表示 `&mut T`：可变借用被翻译为 `(current_value, π)` 对，其中 `π` 预言借用结束后原变量的最终值。

核心关系 `borrow_generated_from(b, x)` 表示借用 `b` 从 `x` 生成，并满足：

- 来源唯一性：每个借用有唯一源。
- 有效性保持：`valid(b, t) → Alive(x, t)`。
- 传递性：借用链保持来源关系。

Aeneas 的优势是**自动化翻译、证明负担较低**，适合验证 Safe Rust 应用代码的功能正确性。

### 5.2 RustBelt / Iris：分离逻辑

[RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/) 使用 Iris（高阶并发分离逻辑）形式化 Safe + Unsafe Rust。它把每个类型解释为 Iris 断言，把每条语句解释为验证条件，最终证明：通过借用检查的程序在 Iris 中满足 `{True} P {Safe}`。

| 本文概念 | Iris 概念 |
| :--- | :--- |
| 所有权环境 Ω | Ghost state `Own_γ(ω)` |
| 值环境 Γ | Physical state `σ : Loc → Val` |
| 不可变借用 `&x` | 分数权限 `x ↦^q v` |
| 可变借用 `&mut x` | 独占 token `ex(x, v)` |
| 生命周期 | Time credits `$t` |

RustBelt 更适合验证 **Unsafe 核心库的安全抽象**，但手动证明负担更重。

### 5.3 两者互补

| 特性 | Aeneas | RustBelt/Iris |
| :--- | :--- | :--- |
| 方法 | 函数式翻译 | 分离逻辑 |
| 范围 | Safe Rust | Safe + Unsafe |
| 目标 | 功能正确性 | 内存安全 |
| 处理 `&mut` | 预言变量 | 独占断言 |
| 后端 | Coq/HOL4/Lean/F* | Coq (Iris) |

实际验证策略：Aeneas 验证应用层算法；RustBelt 验证 `Vec`、`Arc`、`Mutex` 等底层抽象。

---

## 6. 与概念文档的衔接

本文是更高阶的综合视图，建议与以下概念页配套阅读：

- [`concept/04_formal/03_ownership_formal.md`](../../../concept/04_formal/03_ownership_formal.md)：所有权规则、线性类型与内存安全定理的完整形式化。
- [`concept/04_formal/28_borrow_checking_decidability.md`](../../../concept/04_formal/28_borrow_checking_decidability.md)：借用检查的可判定性、NLL、Polonius 与 region inference 的复杂度边界。

如果你只想快速建立直觉，先看本章；如果要写证明或实现验证工具，再深入概念文档。

---

## 💻 可运行示例

### 示例 1：所有权链与部分移动

```rust
struct Person {
    name: String,
    age: u32,
}

fn partial_move() {
    let person = Person {
        name: String::from("Alice"),
        age: 30,
    };

    let name = person.name;   // 部分移动：name 的 token 被取走
    println!("{}", person.age); // OK：age 仍是 owned
    // println!("{:?}", person); // 错误：整体已被部分移动
    println!("{}", name);
}
```

### 示例 2：借用链与传递性

```rust
fn borrow_chain() {
    let mut data = vec![1, 2, 3];

    let r1 = &mut data;       // r1 从 data 生成
    let r2 = &mut r1[0];      // r2 从 r1 生成
    *r2 = 100;                // 借用链：r2 → r1 → data

    // r2 先结束，r1 后结束，data 最终为 [100, 2, 3]
}
```

### 示例 3：共享只读到独占写入的切换

```rust
fn shared_to_unique() {
    let mut s = String::from("hello");

    {
        let r1 = &s;
        let r2 = &s;
        println!("{} {}", r1, r2);
    } // 共享借用结束

    let r3 = &mut s;
    r3.push_str(" world");
    println!("{}", r3);
}
```

---

## 📚 权威来源索引

- [Rust Reference — Ownership](https://doc.rust-lang.org/reference/ownership.html)
- [The Rust Programming Language, Ch. 4](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
- [Rustonomicon — Ownership](https://doc.rust-lang.org/nomicon/ownership.html)
- [RustBelt: Securing the Foundations of the Rust Programming Language (POPL 2018)](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Stacked Borrows (POPL 2020)](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)
- [Tree Borrows (PLDI 2025)](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [Aeneas: Rust Verification by Functional Translation (ICFP 2022)](https://arxiv.org/abs/2206.07185)
- [Ferrocene Language Specification](https://spec.ferrocene.dev/)
- [Tofte & Talpin, Region-Based Memory Management (1997)](https://dl.acm.org/)
- [Wikipedia — Linear Logic](https://en.wikipedia.org/wiki/Linear_logic)
- [Wikipedia — Separation Logic](https://en.wikipedia.org/wiki/Separation_logic)

---

> **迁移说明**：本文件替代已归档的 `docs/research_notes/formal_methods/10_ownership_model.md` 作为面向专家读者的精炼入口；如需完整定理证明、课程对齐、Rust 1.93/1.94 扩展细节，请回查原归档文件。
