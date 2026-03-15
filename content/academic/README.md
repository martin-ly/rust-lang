# Rust 学术研究对接

> **定位**: 桥接 Rust 学术研究前沿与工程实践
> **覆盖**: RustBelt、Tree Borrows、Polonius、验证工具
> **目标**: 将学术成果转化为可理解、可应用的工程知识
> **状态**: 🔄 持续整合

---

## 📋 目录

- [Rust 学术研究对接](#rust-学术研究对接)
  - [📋 目录](#-目录)
  - [🎯 目标](#-目标)
  - [📊 学术研究覆盖矩阵](#-学术研究覆盖矩阵)
  - [🔬 RustBelt 项目](#-rustbelt-项目)
    - [核心贡献](#核心贡献)
    - [所有权形式化](#所有权形式化)
    - [分离逻辑应用](#分离逻辑应用)
  - [🌳 Tree Borrows](#-tree-borrows)
    - [与 Stacked Borrows 对比](#与-stacked-borrows-对比)
    - [实际影响](#实际影响)
  - [🔍 Polonius](#-polonius)
    - [Datalog 形式化](#datalog-形式化)
    - [与当前借用检查器对比](#与当前借用检查器对比)
  - [🛠️ 验证工具](#️-验证工具)
    - [Kani](#kani)
    - [Prusti](#prusti)
    - [Creusot](#creusot)
    - [Aeneas](#aeneas)
  - [📈 研究前沿](#-研究前沿)
    - [当前热点](#当前热点)
    - [即将发表的论文](#即将发表的论文)
  - [🔗 参考资源](#-参考资源)
    - [学术论文](#学术论文)
    - [形式化工具](#形式化工具)
    - [在线课程](#在线课程)

---

## 🎯 目标

本目录致力于：

1. **学术普及**: 将复杂的学术概念转化为工程师可理解的形式
2. **实践对接**: 说明学术研究对实际编程的影响
3. **工具指南**: 提供形式化验证工具的使用教程
4. **前沿跟踪**: 持续跟踪 Rust 相关的学术进展

---

## 📊 学术研究覆盖矩阵

| 研究领域 | 核心论文 | 工程影响 | 文档完整度 | 工具支持 |
|----------|----------|----------|------------|----------|
| **RustBelt** | POPL 2018, 2020 | 内存安全保证 | 60% | Miri |
| **Stacked Borrows** | POPL 2019 | 别名模型 | 50% | Miri |
| **Tree Borrows** | PLDI 2025 | 新别名模型 | 30% | Miri (即将) |
| **Polonius** | Ongoing | 借用分析 | 40% | 编译器 |
| **GAT** | ICFP 2021 | 泛型编程 | 70% | rustc |
| **Async/Await** | OOPSLA 2019 | 异步编程 | 60% | rustc |
| **Verification** | 多篇 | 形式化验证 | 40% | Kani/Prusti |

---

## 🔬 RustBelt 项目

### 核心贡献

RustBelt 是首个对 Rust 内存安全保证进行形式化证明的研究项目。

**关键成果**:

1. **内存安全形式化证明**: 使用 Iris 分离逻辑证明 Safe Rust 无数据竞争
2. **Unsafe 抽象验证**: 验证 unsafe 代码块的安全性条件
3. **Relaxed Memory**: 扩展 RustBelt 到弱内存模型

```
RustBelt 论文链:
├─ POPL 2018: RustBelt (基础)
├─ POPL 2019: Stacked Borrows (别名模型)
├─ POPL 2020: Relaxed Memory (弱内存)
├─ PLDI 2025: Tree Borrows (演进)
└─ 博士论文: Ralf Jung (完整理论)
```

### 所有权形式化

**Iris 分离逻辑表示**:

```coq
(* RustBelt 风格的所有权表示 *)

(* 点态所有权 *)
Definition own_loc (l: loc) (v: val) : iProp :=
  l ↦ v.

(* 独占所有权 *)
Definition own_exclusive (l: loc) : iProp :=
  ∃ v, l ↦ v ∗ (l ↦ - ∗ False).

(* 共享只读所有权 *)
Definition own_shared (l: loc) (v: val) : iProp :=
  □ (l ↦□ v).
```

**定理: 内存安全**:

```
定理 (Memory Safety):
对于任何类型安全的 Rust 程序 P，
如果 P 在 Safe Rust 子集中，
那么 P 不会产生：
- 使用已释放内存
- 数据竞争
- 悬垂指针解引用

证明概要:
1. 所有权转移保证唯一性
2. 借用规则保证无别名冲突
3. 生命周期保证引用有效性
4. Send/Sync 保证线程安全
```

### 分离逻辑应用

**关键概念**:

```rust
// 分离逻辑中的 "*" ( separating conjunction)
// 对应 Rust 的所有权分离

fn example() {
    let mut x = 5;  // 拥有 x
    let y = &mut x; // 临时转移 x 的所有权给借用
    *y += 1;        // 通过借用修改
    // y 在这里结束，所有权返回给 x
    println!("{}", x); // OK: 所有权已恢复
}

// 形式化表示:
// 初始: own(x, 5)
// 借用: own(y, &mut x) * x 被借出
// 结束: own(x, 6)
```

---

## 🌳 Tree Borrows

### 与 Stacked Borrows 对比

| 特性 | Stacked Borrows | Tree Borrows |
|------|-----------------|--------------|
| **模型** | 栈结构 | 树结构 |
| **性能** | 严格，拒绝更多代码 | 宽松，接受更多代码 |
| **兼容性** | 30K crates 测试 | 30K crates +54% 通过 |
| **形式化** | 已验证 | Rocq 形式化 (PLDI 2025) |
| **Miri 支持** | 当前默认 | 开发中 |

**核心改进**:

```rust
// Stacked Borrows 会拒绝此代码
// Tree Borrows 允许
fn tree_borrows_allows() {
    let mut x = 0;
    let y = &mut x;
    let z = &mut *y;  // 通过 y 重新借用

    // Stacked Borrows: y 被 z 弹出，之后不能使用
    // Tree Borrows: y 和 z 在树中共存

    *z = 1;
    *y = 2;  // Tree Borrows: OK, Stacked Borrows: UB
}
```

### 实际影响

**对开发者的影响**:

1. **更少的误报**: Miri 将报告更少的"假 UB"
2. **更直观的模型**: 树结构更符合直觉
3. **兼容性提升**: 更多 unsafe 代码被视为合法

**迁移建议**:

```bash
# 测试你的代码在 Tree Borrows 下的行为
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test
```

---

## 🔍 Polonius

### Datalog 形式化

Polonius 是 Rust 借用检查器的新实现，使用 Datalog 规则。

**核心思想**:

```datalog
% 输入事实
loan_origin(Loan, Point).
loan_killed(Loan, Point).
loan_invalidated(Loan, Point).
borrow_region(Region, Loan, Point).

% 规则: 借用活跃
borrow_live_at(Loan, Point) :-
    loan_origin(Loan, Point).

borrow_live_at(Loan, Point2) :-
    borrow_live_at(Loan, Point1),
    cfg_edge(Point1, Point2),
    !loan_killed(Loan, Point1).

% 规则: 错误检测
error(Loan, Point) :-
    loan_invalidated(Loan, Point),
    borrow_live_at(Loan, Point).
```

**优势**:

1. **非词法生命周期**: 支持更精确的借用范围
2. **更清晰**: 规则可独立理解和验证
3. **可扩展**: 易于添加新功能

### 与当前借用检查器对比

```rust
// 当前借用检查器: 拒绝
// Polonius: 接受
fn polonius_accepts() {
    let mut x = 5;
    let y = &x;

    if condition {
        println!("{}", y);  // y 在这里最后一次使用
    }

    // 当前: y 仍然被视为"活跃"
    // Polonius: y 不再活跃，允许可变借用
    x = 10;  // Polonius: OK
}
```

---

## 🛠️ 验证工具

### Kani

**定位**: Rust 的模型检查器

```rust
// 使用 Kani 验证属性
#[cfg(kani)]
mod verification {
    use kani::Arbitrary;

    #[kani::proof]
    fn verify_addition() {
        let a: u32 = kani::any();
        let b: u32 = kani::any();

        // 假设: 不发生溢出
        kani::assume(a <= 1000 && b <= 1000);

        let result = a + b;

        // 验证: 结果正确
        kani::assert(result >= a);
        kani::assert(result >= b);
    }
}
```

**验证 unsafe 代码**:

```rust
#[kani::proof]
fn verify_raw_ptr() {
    let mut x = 5;
    let ptr = &mut x as *mut i32;

    unsafe {
        *ptr = 10;
        kani::assert(x == 10);
    }
}
```

### Prusti

**定位**: 基于 Viper 的演绎验证器

```rust
use prusti_contracts::*;

#[requires(n >= 0)]
#[ensures(result >= 0)]
#[ensures(result >= n)]
fn factorial(n: u64) -> u64 {
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

#[requires(array.len() > 0)]
#[ensures(forall(|i: usize| (0 <= i && i < array.len())
          ==> array[i] <= result), result = array[0])]
fn find_max(array: &[i32]) -> i32 {
    let mut max = array[0];
    for &x in array {
        if x > max {
            max = x;
        }
    }
    max
}
```

### Creusot

**定位**: 使用 Why3 的 Rust 验证器

```rust
// Creusot 风格规范
extern crate creusot_contracts;
use creusot_contracts::*;

#[ensures(result@ >= 0)]
#[ensures(result@ == if n@ <= 1 { 1 } else { n@ * fac(n - 1) })]
fn fac(n: u64) -> u64 {
    if n <= 1 {
        1
    } else {
        n * fac(n - 1)
    }
}
```

### Aeneas

**定位**: 生成 Lean 4 证明义务的验证器

```rust
// Aeneas 将 Rust 代码转换为 Lean 进行验证
// 适合验证复杂算法和数据结构

#[aeneas::verify]
fn binary_search(arr: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = arr.len();

    while left < right {
        let mid = left + (right - left) / 2;
        match arr[mid].cmp(&target) {
            std::cmp::Ordering::Equal => return Some(mid),
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
        }
    }
    None
}
```

---

## 📈 研究前沿

### 当前热点

1. **类型系统扩展**:
   - Generic Associated Types 的进一步泛化
   - Const Generics 的表达式支持
   - 类型级递归

2. **异步编程形式化**:
   - Pin 的完整语义
   - async fn in traits
   - 异步 drop

3. **内存模型**:
   - C++ 内存模型兼容
   - GPU 内存模型
   - 持久内存支持

4. **验证技术**:
   - 自动化不变量推断
   - 机器学习辅助验证
   - 标准库验证

### 即将发表的论文

| 论文 | 会议 | 主题 | 预计影响 |
|------|------|------|----------|
| Tree Borrows Complete | - | 完整别名模型 | 高 |
| Rust Std Verification | - | 标准库验证 | 高 |
| Polonius Formalization | - | 借用检查器形式化 | 中 |
| Async Drop Semantics | - | 异步析构语义 | 中 |

---

## 🔗 参考资源

### 学术论文

- [RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Stacked Borrows: An Aliasing Model for Rust](https://plv.mpi-sws.org/rustbelt/stacked-borrows/)
- [Tree Borrows (PLDI 2025)](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustBelt Meets Relaxed Memory](https://plv.mpi-sws.org/rustbelt/rbrlx/)

### 形式化工具

- [Iris](https://iris-project.org/) - 分离逻辑框架
- [Coq](https://coq.inria.fr/) - 定理证明器
- [Lean 4](https://lean-lang.org/) - 现代定理证明器
- [Kani](https://model-checking.github.io/kani/) - Rust 模型检查器
- [Prusti](https://www.pm.inf.ethz.ch/research/prusti.html) - Rust 验证器
- [Creusot](https://github.com/creusot-rs/creusot) - Why3-based 验证器
- [Aeneas](https://github.com/AeneasVerif/aeneas) - Lean 4 验证器

### 在线课程

- [Programming Language Foundations in Agda](https://plfa.github.io/)
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [Type Theory Foundations](https://www.coursera.org/learn/type-theory)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-15
**状态**: 🔄 持续整合学术前沿
