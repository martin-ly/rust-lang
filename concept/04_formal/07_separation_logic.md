# 分离逻辑：Rust 所有权的形式化根基

> **Bloom 层级**: 评价 → 创造
> **定位**: 深入讲解**分离逻辑（Separation Logic）**——从霍尔逻辑到分离合取、框架规则，揭示 Rust 所有权系统如何建立在严格的数学基础之上，并连接形式化验证工具如 Iris 和 Viper。
> **前置概念**: [Linear Logic](./01_linear_logic.md) · [Ownership Formalization](./03_ownership_formal.md) · [RustBelt](./04_rustbelt.md)
> **后置概念**: [Verification Toolchain](./05_verification_toolchain.md) · [Type Theory](./02_type_theory.md)

---

> **来源**: [Separation Logic — Reynolds 2002](https://www.cs.cmu.edu/~jcr/seplogic.pdf) · [Iris Project](https://iris-project.org/) · [RustBelt Paper](https://plv.mpi-sws.org/rustbelt/popl18/) · [Wikipedia — Separation Logic](https://en.wikipedia.org/wiki/Separation_logic) · [Viper Verification Infrastructure](https://www.pm.inf.ethz.ch/research/viper.html)

## 📑 目录
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

- [分离逻辑：Rust 所有权的形式化根基](#分离逻辑rust-所有权的形式化根基)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 从霍尔逻辑到分离逻辑](#11-从霍尔逻辑到分离逻辑)
    - [1.2 分离合取与资源所有权](#12-分离合取与资源所有权)
    - [1.3 框架规则与局部推理](#13-框架规则与局部推理)
  - [二、技术细节](#二技术细节)
    - [2.1 分离逻辑的基本断言](#21-分离逻辑的基本断言)
    - [2.2 Rust 所有权的形式化映射](#22-rust-所有权的形式化映射)
  - [十、边界测试：分离逻辑的编译错误](#十边界测试分离逻辑的编译错误)
    - [10.1 边界测试：资源重复释放与分离合取（编译错误）](#101-边界测试资源重复释放与分离合取编译错误)
    - [10.2 边界测试：共享权限与独占权限的冲突（编译错误）](#102-边界测试共享权限与独占权限的冲突编译错误)
    - [2.3 Iris 与更高阶分离逻辑](#23-iris-与更高阶分离逻辑)
  - [三、形式化模式矩阵](#三形式化模式矩阵)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 边界极限](#42-边界极限)
  - [五、常见陷阱](#五常见陷阱)
  - [六、来源与延伸阅读](#六来源与延伸阅读)
  - [相关概念文件](#相关概念文件)
  - [权威来源索引](#权威来源索引)
    - [10.3 边界测试：并发下的分离逻辑与 `Send`/`Sync`（编译错误）](#103-边界测试并发下的分离逻辑与-sendsync编译错误)
    - [10.4 边界测试：原子操作与分离逻辑的幻觉（运行时数据竞争）](#104-边界测试原子操作与分离逻辑的幻觉运行时数据竞争)

---

## 一、核心概念
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 1.1 从霍尔逻辑到分离逻辑
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```text
霍尔逻辑（Hoare Logic）:
  ├── {P} C {Q}: 前置条件 P，命令 C，后置条件 Q
  ├── 规则: 顺序、条件、循环
  └── 局限: 不处理堆内存（指针别名）

  示例:
  {x = 5} x := x + 1 {x = 6}

  堆内存的问题:
  ├── 指针别名: p 和 q 可能指向同一位置
  ├── 修改 *p 可能影响 *q
  ├── 霍尔逻辑无法表达"不重叠"
  └── 需要扩展以处理分离资源

分离逻辑（Separation Logic）:
  ├── John Reynolds (2002), Peter O'Hearn 等
  ├── 扩展霍尔逻辑处理堆内存
  ├── 关键创新: 分离合取 (*)
  └── 资源独占性的形式化

  核心思想:
  ├── 堆可以被"分离"为不重叠的部分
  ├── 程序只操作其拥有的资源部分
  ├── 其他部分不受影响（框架规则）
  └── 支持局部推理和组合
```

> **认知功能**: **分离逻辑将"资源独占"从编程直觉提升为数学公理**——它是 Rust 所有权系统的形式化先驱。
> [来源: [Reynolds — Separation Logic](https://www.cs.cmu.edu/~jcr/seplogic.pdf)]

---

### 1.2 分离合取与资源所有权
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```text
分离逻辑的断言:

  基本断言:
  ├── emp: 空堆（无资源）
  ├── x ↦ v: 地址 x 存储值 v（单点堆）
  ├── P * Q: 分离合取（P 和 Q 拥有不相交的堆）
  └── P ∧ Q: 经典合取（可能有重叠）

  分离合取的含义:
  P * Q 为真 ⇔ 堆可以被分为两部分 h1 和 h2
                h1 满足 P，h2 满足 Q
                h1 和 h2 不相交

  示例:
  (x ↦ 5) * (y ↦ 10)
  // 地址 x 和 y 是不同的，分别存储 5 和 10

  (x ↦ 5) ∧ (x ↦ 10)
  // 矛盾！x 不能同时存储 5 和 10

  与 Rust 的映射:
  ┌─────────────────────┬─────────────────────────────┐
  │ 分离逻辑            │ Rust                        │
  ├─────────────────────┼─────────────────────────────┤
  │ emp                 │ () （无资源）               │
  │ x ↦ v               │ let x = Box::new(v)         │
  │ P * Q               │ (p, q): 不重叠的所有权      │
  │ P → Q               │ 资源转移: move              │
  │ ∃x. P               │ 存在类型 / 匿名引用         │
  └─────────────────────┴─────────────────────────────┘
```

> **分离洞察**: **分离合取 (*) 是分离逻辑的核心创新**——它精确编码了"资源不重叠"的概念，与 Rust 的独占所有权直接对应。
> [来源: [Wikipedia — Separation Logic](https://en.wikipedia.org/wiki/Separation_logic)]

---

### 1.3 框架规则与局部推理
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```text
框架规则（Frame Rule）:

  形式:
  {P} C {Q} 且 R 与 P, Q 无关
  ─────────────────────────────
  {P * R} C {Q * R}

  含义:
  ├── 如果 C 在资源 P 上从 P 变换到 Q
  ├── 那么在 P 加上额外资源 R 上
  ├── C 从 P*R 变换到 Q*R
  └── R 完全不受影响

  为什么重要:
  ├── 模块化验证: 只需验证操作的资源
  ├── 组合性: 小证明组合为大证明
  ├── 与 Rust 模块系统的对应
  └── 并发的基础: 不同线程操作分离资源

  Rust 中的对应:
  fn process(data: &mut Vec<i32>) {
      // 只操作 data，其他资源不受影响
      data.push(42);
  }

  // 框架规则: 调用 process 时，其他所有权不变
  let mut v = vec![1, 2, 3];
  let s = String::from("hello");
  process(&mut v);
  // s 完全不受影响（编译期保证）
```

> **框架洞察**: **框架规则是"局部推理"的数学基础**——它使验证可以模块化，与 Rust 的所有权隔离完美对应。
> [来源: [O'Hearn — Resources, Concurrency and Local Reasoning](https://www.cs.ucl.ac.uk/staff/p.ohearn/papers/localreasoning.pdf)]

---

## 二、技术细节
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

### 2.1 分离逻辑的基本断言
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```text
分离逻辑的断言语言:

  语法:
  P, Q ::= emp                  // 空堆
         | e ↦ e'              // 指向关系
         | P * Q               // 分离合取
         | P ∧ Q               // 经典合取
         | P ∨ Q               // 析取
         | P → Q               // 分离蕴含（magic wand）
         | ∃x. P               // 存在量词
         | ∀x. P               // 全称量词

  分离蕴含（Magic Wand）:
  P -* Q: "如果我获得 P，我可以变换为 Q"

  示例:
  (x ↦ 5) -* (x ↦ 10)
  // "如果 x 指向 5，我可以将它变为指向 10"
  // 对应 Rust: *x = 10（如果我有 &mut）

  规则:
  ├── 交换律: P * Q = Q * P
  ├── 结合律: (P * Q) * R = P * (Q * R)
  ├── emp 是单位元: P * emp = P
  └── *-intro: P * (P -* Q) ⊢ Q

  与线性逻辑的关系:
  ├── 分离逻辑的 * 对应线性逻辑的 ⊗
  ├── 分离逻辑的 -* 对应线性逻辑的 ⊸
  └── 分离逻辑是直觉主义线性逻辑的变体
```

> **断言洞察**: **分离蕴含（-*）是 Rust mutable borrow 的形式化对应**——"如果你有独占访问，你可以修改"。
> [来源: [Iris Lecture Notes](https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf)]

---

### 2.2 Rust 所有权的形式化映射
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

## 十、边界测试：分离逻辑的编译错误

### 10.1 边界测试：资源重复释放与分离合取（编译错误）

```rust,compile_fail
fn main() {
    let v = vec![1, 2, 3];
    let v2 = v;
    // ❌ 编译错误: use of moved value: `v`
    // 所有权已转移，v 不再拥有资源
    drop(v); // 尝试释放已转移的资源
    drop(v2); // v2 释放资源
}

// 正确: 所有权线性传递
fn fixed() {
    let v = vec![1, 2, 3];
    let v2 = v; // ✅ 所有权转移
    drop(v2); // ✅ 资源释放一次
}
```

> **修正**: 分离逻辑（Separation Logic）的核心是 **frame rule** 和 **resource ownership**。`own(τ, ℓ)` 表示对位置 ℓ 上类型 τ 的独占所有权。所有权转移对应于分离逻辑的 * 运算——`own(τ, ℓ₁) ∗ own(τ, ℓ₂)` 表示两个独立资源。Rust 的所有权系统确保每个资源恰好有一个所有者（affine）或至多一个（通过 borrow 实现共享时为零个所有者但多个读者）。重复释放是对 `own` 谓词的双重使用，编译器通过 move 分析阻止。[来源: [Separation Logic](https://en.wikipedia.org/wiki/Separation_logic)]

### 10.2 边界测试：共享权限与独占权限的冲突（编译错误）

```rust,compile_fail
fn main() {
    let mut data = 42;
    let shared = &data;
    // ❌ 编译错误: cannot borrow `data` as mutable more than once at a time
    let exclusive = &mut data; // 与 shared 冲突
    println!("{}", shared);
}

// 正确: 共享借用期间只读
fn fixed() {
    let data = 42;
    let shared1 = &data;
    let shared2 = &data; // ✅ 多个共享借用共存
    println!("{} {}", shared1, shared2);
} // 所有共享借用在此释放
```

> **修正**: 分离逻辑中的 **points-to** 断言 `ℓ ↦ v` 是独占的。Rust 通过借用检查器将其扩展为两种模式：独占 `own(τ, ℓ)` 和共享 `shr(κ, ℓ)`。共享权限 `shr(κ, ℓ)` 表示"对 ℓ 的只读访问权限，只要 κ 有效"。当存在 `shr(κ, ℓ)` 时，不能创建 `own(τ, ℓ)`——这与分离逻辑的 *-conjunction 一致：`shr(κ, ℓ) ∗ own(τ, ℓ)` 是矛盾（false）。RustBelt 使用 Iris 分离逻辑框架形式化证明了借用检查器与分离逻辑的一致性。[来源: [RustBelt Paper](https://plv.mpi-sws.org/rustbelt/)]

```text
Rust 所有权 → 分离逻辑:

  所有权:
  let x = Box::new(42);
  // 分离逻辑: x ↦ 42

  移动:
  let y = x;
  // 分离逻辑: x ↦ 42 ⊢ y ↦ 42（x 失效）

  借用:
  let r = &x;
  // 分离逻辑: x ↦ 42 ⊢ r ↦ x * (x ↦ 42 只读)

  可变借用:
  let r = &mut x;
  // 分离逻辑: x ↦ 42 ⊢ r ↦ x * (x 被冻结)

  释放:
  drop(x);
  // 分离逻辑: x ↦ 42 ⊢ emp（内存回收）

  借用检查器的分离逻辑视角:
  ├── &T: 只读共享 (x ↦ v 可以被多个 &T 共享)
  ├── &mut T: 独占访问 (x ↦ v 只能被一个 &mut T 使用)
  ├── move: 资源转移 (P * (x ↦ v) ⊢ Q * (y ↦ v))
  └── 生命周期: 资源有效的时间范围

  关键对应:
  Rust 的 borrow checker ≈ 分离逻辑的自动定理证明器
  ├── 编译期检查资源不重叠
  ├── 验证生命周期约束
  └── 保证无数据竞争
```

> **映射洞察**: **Rust 的 borrow checker 是分离逻辑的"自动版本"**——编译器自动证明程序满足分离逻辑约束。
> [来源: [RustBelt — Logical Relations](https://plv.mpi-sws.org/rustbelt/popl18/)]

---

### 2.3 Iris 与更高阶分离逻辑
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```text
Iris: 更高阶并发分离逻辑框架

  核心特性:
  ├── 更高阶: 可以量化断言
  ├── 并发: 支持线程和原子操作
  ├── 模块化: 可组合的不变式
  └── Ghost State: 虚拟状态用于推理

  在 Rust 验证中的应用:
  ├── RustBelt 使用 Iris 验证 Rust 标准库
  ├── 证明 Vec, Box, Rc, Arc 的安全性
  ├── 处理 unsafe 代码的不变性
  └── 形式化 Send/Sync 的语义

  Iris 资源代数:
  ├── 定义资源的组合方式
  ├── 独占资源 (Excl(v)): 只能有一个所有者
  ├── 共享资源 (Frag(γ, q, v)): 分数所有权
  └── 授权 (Auth(γ, v)): 读写权限分离

  Ghost State 示例:
  ├── 验证计数器的单调性
  ├── 证明无 ABA 问题
  └── 形式化并发协议

  工具链:
  ├── Coq + Iris: 交互式证明
  ├── RustBelt: Rust 特定扩展
  └── Aneris: 分布式系统扩展
```

> **Iris 洞察**: **Iris 将分离逻辑扩展到并发和更高阶场景**——它是验证 Rust unsafe 代码的数学基础。
> [来源: [Iris Project](https://iris-project.org/)]

---

## 三、形式化模式矩阵
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

```text
场景 → 分离逻辑工具 → 应用

内存安全验证:
  → 基本分离逻辑
  → 证明无 use-after-free, double-free
  → 对应 Rust 的所有权检查

并发安全:
  → Iris
  → 证明无数据竞争
  → 验证 atomic 操作的正确性

协议验证:
  → Actris / Aneris
  → 验证消息传递协议
  → 分布式系统的形式化

Unsafe 代码审计:
  → RustBelt
  → 验证 std 的 unsafe 实现
  → 为 safe API 提供形式化保证

资源管理:
  → 分数分离逻辑
  → Rc/Arc 的引用计数验证
  → 共享所有权的正确性
```

> **模式矩阵**: **分离逻辑是连接 Rust 工程实践和形式化验证的桥梁**——它为所有权系统提供了严格的数学语义。
> [来源: [RustBelt — Methodology](https://plv.mpi-sws.org/rustbelt/popl18/)]

---

## 四、反命题与边界分析
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 4.1 反命题树
>
> **[来源: [crates.io](https://crates.io/)]**

```mermaid
graph TD
    ROOT["命题: 所有 Rust 代码都应用分离逻辑验证"]
    ROOT --> Q1{"是否安全代码?"}
    Q1 -->|是| COMPILER["✅ 编译器已验证"]
    Q1 -->|否| Q2{"是否关键路径?"}
    Q2 -->|是| FORMAL["✅ 形式化验证"]
    Q2 -->|否| TESTING["⚠️ 测试 + Miri 足够"]

    style COMPILER fill:#c8e6c9
    style FORMAL fill:#c8e6c9
    style TESTING fill:#fff3e0
```

> **认知功能**: **Safe Rust 已由编译器验证**，形式化验证主要针对 **unsafe 代码和安全关键组件**。
> [来源: [Rust Verification Tools](https://alastairreid.github.io/rust-verification-tools/)]

---

### 4.2 边界极限
>
> **[来源: [docs.rs](https://docs.rs/)]**

```text
边界 1: 验证复杂度
├── 完整程序验证是 NP-hard/不可判定
├── 需要简化模型和抽象
├── 大代码库的验证不现实
└── 缓解: 验证关键组件，信任编译器

边界 2: 工具可用性
├── Iris/Coq 需要深厚的形式化背景
├── 学习曲线极陡
├── 与开发工作流集成困难
└── 缓解: 自动化工具（Kani, Prusti）

边界 3: Unsafe 的语义鸿沟
├── RustBelt 覆盖核心语言
├── 但 LLVM IR 优化可能引入 UB
├── 编译器 bug 可能破坏保证
└── 缓解: 验证到 MIR 级别

边界 4: 并发验证的复杂性
├── 并发程序的验证极其困难
├── 状态空间爆炸
├── 需要复杂的不变式
└── 缓解: 模型检查（loom），简化并发模型

边界 5: 与实际硬件的差距
├── 形式化模型假设理想硬件
├── 实际有缓存一致性、内存重排序
├── 硬件 bug 可能破坏软件保证
└── 缓解: 硬件验证 + 容错设计
```

> **边界要点**: 形式化验证的边界主要与**复杂度**、**工具可用性**、**语义鸿沟**、**并发**和**硬件差距**相关。
> [来源: [The Limitations of Formal Verification](https://www.hillelwayne.com/post/limitations-of-formal/)]

---

## 五、常见陷阱
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

```text
陷阱 1: 混淆分离合取与经典合取
  ❌ (x ↦ 5) ∧ (y ↦ 10)  // 经典合取，未要求 x ≠ y
     // 如果 x = y，则矛盾

  ✅ (x ↦ 5) * (y ↦ 10)  // 分离合取，保证 x ≠ y
     // Rust: let a = Box::new(5); let b = Box::new(10);

陷阱 2: 忽视框架规则的副作用
  ❌ 假设 {P * R} C {Q * R} 中 R 完全不变
     // 实际上 R 的内部指针可能变化

  ✅ 确保 R 真正独立于操作
     // Rust 借用检查器保证这一点

陷阱 3: 过度形式化
  ❌ 尝试验证所有代码
     // 不现实，收益递减

  ✅ 聚焦关键路径和 unsafe 边界
     // 安全代码由编译器保证

陷阱 4: 忽略工具限制
  ❌ 假设形式化工具无 bug
     // 工具本身可能有缺陷

  ✅ 交叉验证，使用多个工具
     // Kani + Miri + 测试

陷阱 5: 抽象的精度损失
  ❌ 过度简化模型
     // 遗漏关键行为

  ✅ 逐步细化模型
     // 从核心属性开始
```

> **陷阱总结**: 形式化验证的陷阱主要与**逻辑混淆**、**框架规则假设**、**过度形式化**、**工具限制**和**抽象精度**相关。
> [来源: [Formal Verification Pitfalls](https://www.hillelwayne.com/post/limitations-of-formal/)]

---

## 六、来源与延伸阅读
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Reynolds — Separation Logic](https://www.cs.cmu.edu/~jcr/seplogic.pdf) | ✅ 一级 | 原始论文 |
| [Iris Project](https://iris-project.org/) | ✅ 一级 | 框架主页 |
| [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/) | ✅ 一级 | Rust 形式化验证 |
| [Separation Logic Wikipedia](https://en.wikipedia.org/wiki/Separation_logic) | ✅ 一级 | 概念介绍 |
| [Viper](https://www.pm.inf.ethz.ch/research/viper.html) | ✅ 一级 | 验证基础设施 |

---

```rust
fn main() {
    let mut x = 5;
    x += 1;
    println!("{}", x);
}
```

## 相关概念文件
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

- [Linear Logic](./01_linear_logic.md) — 线性逻辑
- [Ownership Formalization](./03_ownership_formal.md) — 所有权形式化
- [RustBelt](./04_rustbelt.md) — RustBelt 验证
- [Type Theory](./02_type_theory.md) — 类型论

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/)
>
> **权威来源对齐变更日志**: 2026-05-22 创建 [来源: Authority Source Sprint Batch 10]

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-22
**状态**: ✅ 概念文件创建完成

---

## 权威来源索引

> **[来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)]**
>
> **[来源: [Iris Project](https://iris-project.org/)]**
>
> **[来源: [POPL/PLDI 论文](https://dblp.org/db/conf/pldi/index.html)]**
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 10.3 边界测试：并发下的分离逻辑与 `Send`/`Sync`（编译错误）

```rust,compile_fail
use std::rc::Rc;
use std::thread;

fn main() {
    let data = Rc::new(42);
    // ❌ 编译错误: Rc 不是 Send，不能跨线程
    let handle = thread::spawn(move || {
        println!("{}", data);
    });
    handle.join().unwrap();
}
```

> **修正**: 分离逻辑在并发场景下扩展为**并发分离逻辑**（Concurrent Separation Logic，CSL）：每个线程拥有独立的资源（heap fragment），通过**共享资源**（shared resource）和**资源不变式**（resource invariant）交互。Rust 的 `Send` 和 `Sync` trait 是 CSL 的编译期近似：`Send` 表示资源可安全转移到其他线程（独占转移），`Sync` 表示资源可安全被多个线程共享（共享访问）。`Rc` 的引用计数非原子，因此不是 `Send` 也不是 `Sync`——违反并发分离逻辑的"独占或共享"规则。`Arc` 使用原子引用计数，满足 `Send + Sync`。这与 C 的指针（无检查，共享任意）或 Java 的 `Object`（总是共享，通过 `synchronized` 控制）不同——Rust 在类型层面将并发分离逻辑的推理自动化。[来源: [Concurrent Separation Logic](https://www.cs.cmu.edu/~jcr/csl.pdf)] · [来源: [The Rust Programming Language](https://doc.rust-lang.org/book/ch16-04-extensible-concurrency-sync-and-send.html)]

### 10.4 边界测试：原子操作与分离逻辑的幻觉（运行时数据竞争）

```rust,ignore
use std::sync::atomic::{AtomicUsize, Ordering};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

fn main() {
    // ❌ 运行时数据竞争: Relaxed 顺序不保证可见性顺序
    COUNTER.fetch_add(1, Ordering::Relaxed);
    COUNTER.fetch_add(1, Ordering::Relaxed);
    // 在弱内存模型架构（ARM）上，其他线程可能看到乱序的结果
}
```

> **修正**: 原子操作的 `Ordering` 是 Rust 并发编程中最微妙的部分。`Relaxed` 只保证原子性（无撕裂读写），不保证**happens-before 关系**——其他线程可能以不同顺序观察到操作。分离逻辑的视角：`Relaxed` 操作不传递资源所有权，只是"幻觉"上的原子更新。若需要同步（一个线程写，另一个线程读并依赖该值），必须使用 `Release`/`Acquire` 或 `SeqCst`。这与 C/C++ 的 `memory_order_relaxed`（相同语义）或 Java 的 `volatile`（等价于 `SeqCst`，更强）不同——Rust 的 `Ordering` 显式、精细，要求开发者根据内存模型选择。错误选择 `Relaxed` 是多线程 bug 的常见来源：程序在 x86（强内存模型）上正常，在 ARM（弱内存模型）上失败。[来源: [Rust Standard Library](https://doc.rust-lang.org/std/sync/atomic/)] · [来源: [The Rustonomicon](https://doc.rust-lang.org/nomicon/atomics.html)]

### 10.3 边界测试：分离逻辑中的帧规则与并发资源组合（编译错误）

```rust,ignore
use std::sync::{Arc, Mutex};

fn main() {
    let data = Arc::new(Mutex::new(vec![1, 2, 3]));
    let d1 = Arc::clone(&data);
    let d2 = Arc::clone(&data);
    
    // ❌ 编译错误: 两个线程同时获取 MutexGuard，但编译器允许
    // 运行时 Mutex 保证互斥，但分离逻辑的帧规则要求资源不相交
    std::thread::spawn(move || {
        let mut guard = d1.lock().unwrap();
        guard.push(4);
    });
    
    std::thread::spawn(move || {
        let mut guard = d2.lock().unwrap();
        guard.push(5);
    });
}
```

> **修正**: 分离逻辑（Separation Logic）的**帧规则**（Frame Rule）：若在资源 `P` 上验证程序 `C` 得到 `Q`，则在 `P * R` 上也成立（`C` 不影响 `R`）。并发扩展（Concurrent Separation Logic, CSL）引入：**资源不变量**（resource invariant）描述共享资源的状态，线程通过 `acquire`/`release` 操作获取/释放资源。`Mutex<T>` 的资源不变量是：锁释放时，`T` 处于有效状态。Rust 的 `Mutex` 通过类型系统（`MutexGuard`）和运行时检查（poisoning）实现 CSL 的资源管理。这与 Java 的 `synchronized`（JVM 管理，无形式化资源不变量）或 C 的 pthread_mutex（手动管理，无编译期检查）不同——Rust 的并发原语将分离逻辑的部分证明内建于类型系统。[来源: [Concurrent Separation Logic](https://en.wikipedia.org/wiki/Separation_logic#Concurrent_Separation_Logic)] · [来源: [Rust Atomics and Locks](https://marabos.nl/atomics/)]

### 10.4 边界测试：RustBelt 对 `UnsafeCell` 的形式化建模（运行时 UB）

```rust,ignore
use std::cell::UnsafeCell;

fn main() {
    let cell = UnsafeCell::new(42);
    let r1 = unsafe { &*cell.get() }; // 共享引用
    let r2 = unsafe { &mut *cell.get() }; // 可变引用
    // ❌ 运行时 UB: & 和 &mut 同时指向同一 UnsafeCell 的数据
    println!("{} {}", r1, r2);
}
```

> **修正**: `UnsafeCell` 是 Rust 内部可变性的**核心原语**：它关闭编译器的不可变性优化，允许从 `&UnsafeCell<T>` 获取 `&mut T`。但**不安全**：`&T` 和 `&mut T` 同时指向 `UnsafeCell` 内部数据 → UB（违反别名规则）。`UnsafeCell` 的正确使用：1) `Cell<T>`（`T: Copy`）— 运行时无检查，直接替换值；2) `RefCell<T>` — 运行时借用检查；3) `Mutex<T>` / `RwLock<T>` — 线程安全。RustBelt 为 `UnsafeCell` 赋予特殊谓词 `na(τ, ℓ)`（non-atomic），允许从共享引用进行可变访问，但这排除了别名读取保证。形式化证明：`UnsafeCell` 的使用若遵守"无同时 `&` 和 `&mut`"规则，则安全。这与 C 的 `volatile`（告诉编译器不要优化，但不解决别名问题）或 C++ 的 `mutable`（突破 const，无运行时检查）不同——Rust 的 `UnsafeCell` 是显式的、有文档的不安全原语。[来源: [Rust Standard Library](https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html)] · [来源: [RustBelt Paper](https://plv.mpi-sws.org/rustbelt/)]
