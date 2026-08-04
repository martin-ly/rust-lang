> **内容分级**: [专家级]

# RustBelt 所有权逻辑：作为计算模型的内存安全证明（RustBelt Ownership Logic: Memory Safety Proof as a Computational Model）

> **EN**: RustBelt Ownership Logic: Memory Safety Proof as a Computational Model
> **Summary**: Treats RustBelt's Iris-based ownership logic as a computational model for Rust's safe and unsafe abstractions, mapping lifetime fractional permissions, ownership predicates, invariant protocols, and the λRust operational semantics to Rust's borrow checker, unsafe boundaries, and verified standard-library primitives.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **Bloom 层级**: L4-L7
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: 从**计算模型**视角把 RustBelt 当作 Rust 安全性的**逻辑证明机器**：不重复介绍 Iris 分离逻辑的完整规则，而是说明 RustBelt 如何把 Rust 程序翻译成 λRust 操作语义，并用 Iris 断言证明 safe Rust 的内存安全与无数据竞争，以及 unsafe 抽象如何以「协议契约」形式被纳入证明。
> **前置概念**:
> [RustBelt](../02_separation_logic/01_rustbelt.md) ·
> [Separation Logic for Rust](08_separation_logic_for_rust.md) ·
> [Linear Logic and Ownership](12_linear_logic_and_ownership.md) ·
> [Modal Logic and Rust Effects](11_modal_logic_and_rust_effects.md)
> **后置概念**:
> [Aeneas Verification Pipeline](17_aeneas_verification_pipeline.md) ·
> [Unsafe Contracts Formal](../01_ownership_logic/07_unsafe_contracts_formal.md) ·
> [Formal Verification Tools](../../06_ecosystem/08_formal_verification/02_formal_verification_tools.md) ·
> [Unsafe Rust](../../03_advanced/02_unsafe/01_unsafe.md) ·
> [Concurrency](../../03_advanced/00_concurrency/01_concurrency.md)

---

## 📑 目录

- [RustBelt 所有权逻辑：作为计算模型的内存安全证明（RustBelt Ownership Logic: Memory Safety Proof as a Computational Model）](#rustbelt-所有权逻辑作为计算模型的内存安全证明rustbelt-ownership-logic-memory-safety-proof-as-a-computational-model)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 RustBelt 作为计算模型](#11-rustbelt-作为计算模型)
    - [1.2 λRust：Rust 的核心演算](#12-λrustrust-的核心演算)
    - [1.3 所有权谓词：own / shr / uniq](#13-所有权谓词own--shr--uniq)
    - [1.4 生命周期分数权限](#14-生命周期分数权限)
    - [1.5 借用作为临时所有权转移](#15-借用作为临时所有权转移)
    - [1.6 不变量协议与内部可变性](#16-不变量协议与内部可变性)
    - [1.7 unsafe 抽象的语义模型](#17-unsafe-抽象的语义模型)
    - [1.8 RustBelt 的健全性定理](#18-rustbelt-的健全性定理)
  - [二、形式化属性矩阵](#二形式化属性矩阵)
  - [三、正向示例](#三正向示例)
    - [示例 1：move 的 own 谓词推理](#示例-1move-的-own-谓词推理)
    - [示例 2：\&mut 借用的临时转移](#示例-2mut-借用的临时转移)
    - [示例 3：Mutex 的不变量协议](#示例-3mutex-的不变量协议)
  - [四、反例与边界测试](#四反例与边界测试)
    - [反例 1：返回悬垂引用破坏 own 谓词](#反例-1返回悬垂引用破坏-own-谓词)
    - [反例 2：\&mut 与 \& 共存破坏 uniq](#反例-2mut-与--共存破坏-uniq)
    - [反例 3：unsafe 抽象违反协议](#反例-3unsafe-抽象违反协议)
  - [五、反命题决策树](#五反命题决策树)
    - [命题：「RustBelt 证明了所有 Rust 程序安全」](#命题rustbelt-证明了所有-rust-程序安全)
    - [命题：「unsafe 代码只要通过借用检查就安全」](#命题unsafe-代码只要通过借用检查就安全)
  - [六、嵌入式测验（Embedded Quiz）](#六嵌入式测验embedded-quiz)
    - [测验 1：RustBelt 使用什么逻辑框架？](#测验-1rustbelt-使用什么逻辑框架)
    - [测验 2：`own(x, τ)` 表示什么？](#测验-2ownx-τ-表示什么)
    - [测验 3：unsafe 代码在 RustBelt 中如何被验证？](#测验-3unsafe-代码在-rustbelt-中如何被验证)
  - [七、权威来源 / International Authority References](#七权威来源--international-authority-references)
  - [八、🧭 思维导图（Mindmap）](#八-思维导图mindmap)
  - [来源与延伸阅读](#来源与延伸阅读)

---

## 一、核心概念

### 1.1 RustBelt 作为计算模型

RustBelt（Jung et al., POPL 2018）是 Rust 安全性的首个**机械验证证明**。从计算模型视角看，它把 Rust 程序的安全性验证转化为一个**形式化的资源推理过程**：

```text
RustBelt 作为计算模型
├── 源语言: Rust (safe + 满足规约的 unsafe)
├── 核心演算: λRust — 保留所有权、借用、生命周期、内部可变性的最小语言
├── 证明框架: Iris — 高阶并发分离逻辑
├── 断言语言: own / shr / uniq / inv 等所有权谓词
├── 证明目标: 良类型 λRust 程序无未定义行为、无数据竞争
└── 关键创新: unsafe 库通过语义模型和协议契约被纳入证明
```

RustBelt 不直接证明真实 rustc 编译出的代码，而是证明一个理想化的核心演算 λRust。其重要性在于：它首次把 Rust 的安全性保证建立在可机械检验的数学基础之上。

> **来源**: [Jung et al., RustBelt POPL 2018](https://doi.org/10.1145/3158154) · [Jung et al., Iris from the Ground Up](https://iris-project.org/pdfs/2018-jfp-iris-ground-up.pdf)

---

### 1.2 λRust：Rust 的核心演算

λRust 是 RustBelt 为形式化证明而设计的**核心演算**（core calculus）。它保留了 Rust 最关键的语言特性，同时去掉了不影响安全性证明的语法糖：

```text
λRust 关键构造
├── 值: 整数、布尔、单元、指针、闭包
├── 类型: τ ::= i32 | bool | () | Box τ | &{α} τ | &mut{α} τ | τ × τ | τ + τ
├── 表达式: let、函数调用、match、引用创建/解引用
├── 所有权: move、borrow、drop
├── 生命周期: α（区域变量，用于约束引用的有效范围）
└── unsafe 原语: 原始指针操作、未初始化内存、类型转换
```

λRust 的操作语义精确规定了每个构造的内存行为。RustBelt 证明：如果 Rust 程序能被翻译成良类型的 λRust 程序，并且 unsafe 库满足其 Iris 协议，则该程序满足内存安全。

---

### 1.3 所有权谓词：own / shr / uniq

RustBelt 使用 Iris 断言来表达 Rust 的所有权状态。最核心的谓词包括：

| 谓词 | 含义 | Rust 直觉 |
|---|---|---|
| `own(x, τ)` | x 独占拥有类型为 τ 的资源 | `let x = Box::new(v)` |
| `shr{α}(x, τ)` | x 拥有 τ 的只读共享引用，生命周期为 α | `let r = &x;` |
| `uniq{α}(x, τ)` | x 拥有 τ 的独占可变引用，生命周期为 α | `let r = &mut x;` |
| `x ↦ v` | 位置 x 存储值 v | 指针指向的具体内存 |
| `□P` | P 是持久断言，可任意复制 | 共享引用、`'static` 数据 |

```text
所有权推理示例
  own(s, String)            // s 独占拥有一个 String
  let t = s;                // own(s, String) ⊢ own(t, String)
  // s 不再拥有资源
```

```rust
fn main() {
    let s = String::from("owned");
    let t = s; // own(s, String) ⊢ own(t, String)
    println!("{}", t);
    // println!("{}", s); // ❌ own(s, String) 已空
}
```

---

### 1.4 生命周期分数权限

RustBelt 的一个核心创新是**生命周期分数权限**（lifetime fractional permissions）。传统分离逻辑中，独占权限是 1.0，共享权限是 0<π<1。RustBelt 把生命周期也看作一种可分割的权限：

```text
生命周期分数权限
  &{α} T   ⇔  shr{α}(x, T)   持有 α 的 0<π<1 份只读权限
  &mut{α} T ⇔ uniq{α}(x, T)  持有 α 的 1.0 份独占权限
  'a: 'b   ⇔  α 包含 β       α 的权限范围覆盖 β
```

这种建模使 RustBelt 能够精确刻画两条规则——多个只读引用可以共存，而可变引用必须独占：

- 多个 `&{α} T` 的分数可以相加，但总和必须 ≤1。
- `&mut{α} T` 必须持有完整的 1.0 权限，因此不能与其他 `&` 或 `&mut` 共存。

```rust
fn main() {
    let mut v = vec![1, 2, 3];
    {
        let r1 = &v; // shr 0.5
        let r2 = &v; // shr 0.5
        println!("{:?} {:?}", r1, r2);
    }              // shr 归还
    v.push(4);     // 重新获得 own
    println!("{:?}", v);
}
```

---

### 1.5 借用作为临时所有权转移

在 RustBelt 中，借用不是「创建新引用」那么简单，而是**临时转移权限**并附带归还义务：

```text
可变借用规则（教学类比）
  Σ ⊢ own(x, τ)
  ───────────────────────────────
  Σ ⊢ uniq{α}(r, τ) * loan(x, α, r, τ)

含义: 把 x 的独占权限临时转移给 r，x 进入 loan 状态；
      当 α 结束时，权限归还 x。
```

```rust
fn main() {
    let mut x = 5;
    {
        let r = &mut x; // uniq(r, i32) * loan(x, α, r, i32)
        *r += 1;
    }                  // α 结束，权限归还 x
    assert_eq!(x, 6);
}
```

> **关键洞察**: 借用检查器在 RustBelt 中对应一个**权限会计系统**：每次借用都要记录 loan，归还时要检查 loan 是否清偿。

---

### 1.6 不变量协议与内部可变性

Rust 的**内部可变性**（Interior Mutability）是借用规则的重要例外：`Cell<T>`、`RefCell<T>`、`Mutex<T>`、`RwLock<T>` 允许在共享引用下修改数据。RustBelt 通过**不变量协议**（invariant protocols）形式化这些抽象：

```text
不变量协议
  inv(P): 资源 P 在所有执行点都成立
  Mutex<T>:  inv(own(guard, T))  — 锁保护着 T 的独占权限
  Cell<T>:   inv(T 的合法值)      — 共享可变但无并发别名
```

`Mutex<T>` 的语义可以读作：存在一个不变量「锁内部持有一个 `T`」，任何线程只有获得 `MutexGuard` 后才能临时拥有这个 `T`。

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let data = Arc::new(Mutex::new(0));
    let data2 = Arc::clone(&data);

    let handle = thread::spawn(move || {
        let mut guard = data2.lock().unwrap();
        *guard += 1;
    });

    {
        let mut guard = data.lock().unwrap();
        *guard += 1;
    }

    handle.join().unwrap();
    assert_eq!(*data.lock().unwrap(), 2);
}
```

> **来源**: [Iris Project — Invariants](https://iris-project.org/) · [RustBelt POPL 2018](https://doi.org/10.1145/3158154)

---

### 1.7 unsafe 抽象的语义模型

RustBelt 最重要的贡献之一是：**unsafe 代码不是被忽略的，而是被赋予语义模型并验证其满足规约**。例如：

- `Cell<T>`：允许共享可变，因为 `Cell` 的方法保证不会出现重叠的可变引用（通过运行时或 API 设计）。
- `Mutex<T>`：通过锁协议保证任意时刻只有一个线程能访问内部数据。
- `Rc<T>`：通过引用计数提供共享所有权，但不可变。

每个 unsafe 抽象都要给出**Iris 语义模型**和**规约**：只要 unsafe 实现满足这些规约，safe 用户就可以把它们当作黑箱使用。

```rust
use std::cell::Cell;

fn main() {
    let c = Cell::new(5);
    let r1 = &c;
    let r2 = &c;
    r1.set(r1.get() + 1);
    r2.set(r2.get() + 1);
    assert_eq!(c.get(), 7);
}
```

> **关键洞察**: `Cell<T>` 的 unsafe 内部通过「禁止获取内部值的引用」来避免别名冲突。RustBelt 证明：只要遵守 `Cell` API，就不会出现数据竞争。

---

### 1.8 RustBelt 的健全性定理

RustBelt 的核心定理可以非正式表述为：

```text
RustBelt 健全性定理（教学类比）
  如果程序 e 在 λRust 中良类型，
  并且 e 中使用的所有 unsafe 库都满足其 Iris 协议规约，
  那么 e 的执行不会触发未定义行为（use-after-free、double-free、
  悬垂指针、数据竞争等）。
```

需要注意这个定理的边界：

1. 它不证明真实 rustc 编译器正确，只证明 λRust 模型。
2. 它不自动验证任意 unsafe 代码；unsafe 库的规约需要人工给出并证明。
3. 它不涵盖 I/O、FFI 语义等超出 λRust 范围的行为。

> **来源**: [Jung et al., RustBelt POPL 2018](https://doi.org/10.1145/3158154)

---

## 二、形式化属性矩阵

| RustBelt 概念 | Rust 工程机制 | 形式化含义 | 权威来源 |
|:---|:---|:---|:---|
| `own(x, τ)` | `let x = ...` | 独占资源 | RustBelt 2018 |
| `shr{α}(x, τ)` | `&x` | 生命周期 α 的只读共享 | RustBelt 2018 |
| `uniq{α}(x, τ)` | `&mut x` | 生命周期 α 的独占可变 | RustBelt 2018 |
| `x ↦ v` | 指针解引用 | 具体内存内容 | Separation Logic |
| `□P` | `&T`、`'static` | 持久断言 | Iris |
| `inv(P)` | `Mutex<T>` 保护的数据 | 全局不变量 | Iris |
| 生命周期子类型 `'a: 'b` | 区域包含 | 权限范围覆盖 | RustBelt 2018 |
| `loan` | 借用期间原变量冻结 | 临时权限转移 | RustBelt 2018 |
| unsafe 规约 | `unsafe impl` / `unsafe fn` | Iris 协议契约 | RustBelt 2018 |
| 健全性定理 | 编译通过 + unsafe 规约满足 | 无 UB / 无数据竞争 | RustBelt 2018 |

---

## 三、正向示例

### 示例 1：move 的 own 谓词推理

```rust
fn main() {
    let s = String::from("RustBelt");
    let t = s; // own(s, String) ⊢ own(t, String)
    println!("{}", t);
}
```

### 示例 2：&mut 借用的临时转移

```rust
fn add_one(r: &mut i32) {
    *r += 1;
}

fn main() {
    let mut x = 5;
    add_one(&mut x);
    assert_eq!(x, 6);
}
```

### 示例 3：Mutex 的不变量协议

```rust
use std::sync::{Arc, Mutex};
use std::thread;

fn main() {
    let data = Arc::new(Mutex::new(0));
    let data2 = Arc::clone(&data);

    let handle = thread::spawn(move || {
        let mut guard = data2.lock().unwrap();
        *guard += 1;
    });

    {
        let mut guard = data.lock().unwrap();
        *guard += 1;
    }

    handle.join().unwrap();
    assert_eq!(*data.lock().unwrap(), 2);
}
```

---

## 四、反例与边界测试

### 反例 1：返回悬垂引用破坏 own 谓词

```rust,compile_fail,E0106
fn dangling() -> &i32 {
    let x = 42;
    &x // x 在函数返回后失效，返回的引用失去 own 支持
}

fn main() {
    let r = dangling();
    println!("{}", r);
}
```

> **错误诊断**: `error[E0106]: missing lifetime specifier`。借用检查器无法构造 `own` 谓词支持返回的引用：引用的生命周期不能长于局部变量 `x`。
> **修正**: 返回 owned 值，或将生命周期与输入参数绑定。

### 反例 2：&mut 与 & 共存破坏 uniq

```rust,compile_fail,E0502
fn main() {
    let mut v = vec![1, 2, 3];
    let r1 = &v;
    let r2 = &mut v; // ❌ uniq 与 shr 共存
    println!("{:?} {:?}", r1, r2);
}
```

> **错误诊断**: `error[E0502]: cannot borrow`v`as mutable because it is also borrowed as immutable`。`uniq{α}(r2, Vec)` 要求完整 1.0 权限，但 `shr(r1, Vec)` 已经占用了部分权限。
> **修正**: 确保只读引用在可变借用之前结束作用域。

### 反例 3：unsafe 抽象违反协议

```rust
use std::cell::Cell;

fn main() {
    let c = Cell::new(5);
    let raw = c.as_ptr();
    unsafe {
        // 绕过 Cell API，直接通过原始指针写入
        *raw = 42;
    }
    assert_eq!(c.get(), 42);
}
```

> **错误诊断**: 代码可能编译并通过测试，但**违反 Cell 的协议假设**。如果多个线程同时执行类似操作，可能出现数据竞争。RustBelt 只验证遵守 Cell API 的代码。
> **修正**: 只在单线程上下文使用 `Cell`，或通过 `Mutex` 等并发安全抽象共享可变状态。

---

## 五、反命题决策树

### 命题：「RustBelt 证明了所有 Rust 程序安全」

```text
该命题成立吗？
├── 是 → 错误。RustBelt 证明的是：
│   ├── λRust 核心演算中的良类型程序
│   └── 使用的 unsafe 库满足 Iris 规约
└── 否 → 正确。它不证明：
    ├── 真实 rustc 编译器正确
    ├── 任意 unsafe 代码安全
    └── I/O、FFI 等超出 λRust 的行为
```

### 命题：「unsafe 代码只要通过借用检查就安全」

```text
该命题成立吗？
├── 是 → 错误。借用检查器在 unsafe 块内放宽很多检查：
│   ├── 原始指针可以别名
│   ├── 可以解引用裸指针
│   └── 可以调用 unsafe 函数
└── 否 → 正确。unsafe 代码安全需要：
    ├── 程序员手动维护不变量
    ├── 必要时用 Miri、Kani、RustBelt 等工具验证
    └── 提供 safe 抽象时给出并满足 Iris 协议规约
```

---

## 六、嵌入式测验（Embedded Quiz）

### 测验 1：RustBelt 使用什么逻辑框架？

A. Z3
B. Iris 分离逻辑
C. 霍尔逻辑
D. 模态逻辑 K

<details>
<summary>✅ 答案</summary>

**B. Iris 分离逻辑**。RustBelt 在 Iris 高阶并发分离逻辑中形式化 Rust 的所有权和借用。

</details>

### 测验 2：`own(x, τ)` 表示什么？

A. x 是 τ 的共享引用
B. x 独占拥有类型为 τ 的资源
C. x 可以任意复制
D. x 是 τ 的可变引用

<details>
<summary>✅ 答案</summary>

**B. x 独占拥有类型为 τ 的资源**。`own(x, τ)` 是 RustBelt 中的独占所有权谓词。

</details>

### 测验 3：unsafe 代码在 RustBelt 中如何被验证？

A. 自动通过
B. 需要给出 Iris 语义模型和协议规约
C. 不能被验证
D. 通过借用检查器

<details>
<summary>✅ 答案</summary>

**B. 需要给出 Iris 语义模型和协议规约**。RustBelt 要求 unsafe 抽象提供形式化规约，并证明其实现满足这些规约。

</details>

---

## 七、权威来源 / International Authority References

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Jung et al., RustBelt POPL 2018](https://doi.org/10.1145/3158154) | ✅ 一级 | RustBelt 奠基论文 |
| [Jung et al., Iris from the Ground Up](https://iris-project.org/pdfs/2018-jfp-iris-ground-up.pdf) | ✅ 一级 | Iris 高阶并发分离逻辑教程 |
| [Iris Project](https://iris-project.org/) | ✅ 一级 | Iris 官方项目主页 |
| [Reynolds 2002, *Separation Logic*](https://www.cs.cmu.edu/~jcr/seplogic.pdf) | ✅ 一级 | 分离逻辑奠基论文 |
| [O'Hearn 2007, *Resources, Concurrency and Local Reasoning*](https://doi.org/10.1016/j.tcs.2006.12.035) | ✅ 一级 | 并发分离逻辑 |
| [Rust Reference — Unsafe Rust](https://doc.rust-lang.org/reference/unsafe-keyword.html) | ✅ P0 | Rust 官方 unsafe 语义 |
| [Rust Reference — Interior Mutability](https://doc.rust-lang.org/reference/interior-mutability.html) | ✅ P0 | 内部可变性官方说明 |

---

## 八、🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((RustBelt 所有权逻辑))
    RustBelt 作为计算模型
      λRust 核心演算
      Iris 分离逻辑
      机械验证
    所有权谓词
      own(x, τ)
      shr{α}(x, τ)
      uniq{α}(x, τ)
      x ↦ v
      □P / inv(P)
    生命周期分数权限
      & = shr 0<π<1
      &mut = uniq 1.0
      'a: 'b = 区域包含
    借用
      临时权限转移
      loan 状态
      归还后恢复 own
    内部可变性
      Mutex / Cell / RefCell
      不变量协议
    unsafe 抽象
      语义模型
      协议规约
      safe 边界
    健全性定理
      无 UB
      无数据竞争
      限于 λRust + 规约
    权威来源
      RustBelt POPL 2018
      Iris Project
      Reynolds / O'Hearn
```

## 来源与延伸阅读

- [RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Aeneas Project](https://aeneasverif.github.io/)
- [Flux Refinement Types](https://flux-rs.github.io/)
- [arXiv](https://arxiv.org/)
- [ACM Digital Library](https://dl.acm.org/)
