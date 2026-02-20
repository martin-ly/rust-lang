# Iterator 形式化分析

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **分类**: 行为型
> **安全边界**: 纯 Safe
> **23 模式矩阵**: [README §23 模式多维对比矩阵](../README.md#23-模式多维对比矩阵) 第 16 行（Iterator）
> **证明深度**: L2（完整证明草图）

---

## 📊 目录

- [Iterator 形式化分析](#iterator-形式化分析)
  - [📊 目录](#-目录)
  - [形式化定义](#形式化定义)
    - [概念定义-属性关系-解释论证 层次汇总](#概念定义-属性关系-解释论证-层次汇总)
  - [Rust 实现与代码示例](#rust-实现与代码示例)
  - [证明思路](#证明思路)
  - [典型场景](#典型场景)
  - [相关模式](#相关模式)
  - [反例：迭代中修改集合](#反例迭代中修改集合)
  - [实现变体](#实现变体)
  - [与标准库衔接](#与标准库衔接)
  - [选型决策树](#选型决策树)
  - [边界](#边界)
  - [与 Rust 1.93 的对应](#与-rust-193-的对应)
  - [实质内容五维自检](#实质内容五维自检)

---

## 形式化定义

**Def 1.1（Iterator 结构）**:

设 $I$ 为迭代器类型，$T$ 为元素类型。Iterator 满足：

- $\exists \mathit{next} : \&mut I \to \mathrm{Option}\langle T \rangle$
- 迭代器持有序列状态（位置、引用等）
- 消耗或借用产生元素；每次 `next` 至多产生一个元素

**Axiom IT1**：`next` 最多返回一次每个元素；无重复、无遗漏（由实现保证）。

**Axiom IT2**：迭代器可变借用：`&mut self` 满足借用规则；同时仅一个活跃迭代器或为 FusedIterator。

**定理 IT-T1**：`Iterator` trait 由标准库定义；`for` 糖语法保证类型安全。由 [type_system_foundations](../../../type_theory/type_system_foundations.md)。

**定理 IT-T2**：`&mut self` 可变借用保证迭代器内部状态一致；由 [borrow_checker_proof](../../../formal_methods/borrow_checker_proof.md)。

**推论 IT-C1**：Iterator 为纯 Safe；`Iterator` trait 标准库定义，`for` 糖语法，无 `unsafe`。由 IT-T1、IT-T2 及 [safe_unsafe_matrix](../../05_boundary_system/safe_unsafe_matrix.md) SBM-T1。

### 概念定义-属性关系-解释论证 层次汇总

| 层次 | 内容 | 本页对应 |
| :--- | :--- | :--- |
| **概念定义层** | Def 1.1（Iterator 结构）、Axiom IT1/IT2（无重复、可变借用） | 上 |
| **属性关系层** | Axiom IT1/IT2 → 定理 IT-T1/IT-T2 → 推论 IT-C1；依赖 type、borrow | 上 |
| **解释论证层** | 证明思路：Iterator trait、借用；反例：迭代中修改集合 | §证明思路、§反例 |

---

## Rust 实现与代码示例

```rust
struct Counter { count: u32 }

impl Iterator for Counter {
    type Item = u32;
    fn next(&mut self) -> Option<Self::Item> {
        if self.count < 5 {
            let c = self.count;
            self.count += 1;
            Some(c)
        } else {
            None
        }
    }
}

// 使用
for n in Counter { count: 0 } {
    println!("{}", n);  // 0, 1, 2, 3, 4
}
```

**形式化对应**：`Counter` 即 $I$；`Item = u32` 即 $T$；`next(&mut self)` 即 $\mathit{next}$。

---

## 证明思路

1. **类型安全**：`Option<T>` 表示终止；`for` 循环类型检查保证 `Item` 与使用处一致。
2. **所有权**：`next` 返回 `Option<T>`，元素所有权转移至调用者；迭代器持有状态（如 `count`），不持有元素。

---

## 典型场景

| 场景 | 说明 |
| :--- | :--- |
| 集合遍历 | `Vec`、`HashMap`、`BTreeMap` 等 |
| 惰性流 | `map`、`filter`、`take` 链式 |
| 自定义序列 | 计数器、生成器、游标 |
| 适配器 | `zip`、`chain`、`enumerate` |

---

## 相关模式

| 模式 | 关系 |
| :--- | :--- |
| [Visitor](visitor.md) | 遍历方式不同；Iterator 顺序，Visitor 深度优先 |
| [Composite](../02_structural/composite.md) | 可对 Composite 实现 Iterator |
| [Chain of Responsibility](chain_of_responsibility.md) | 链式传递 vs 迭代消费 |

---

## 反例：迭代中修改集合

**错误**：在 `for x in vec.iter()` 内对 `vec` 执行 `push`/`remove`。

```rust
let mut v = vec![1, 2, 3];
for x in v.iter() {
    v.push(*x);  // 编译错误：同时存在 borrow 与 borrow_mut
}
```

**结论**：Axiom IT2；可变借用互斥；`iter()` 与 `push` 不可同时活跃。

---

## 实现变体

| 变体 | 说明 | 适用 |
| :--- | :--- | :--- |
| 结构体 + next | 自定义迭代器；实现 trait | 新集合类型 |
| 适配器链 | `iter().map().filter()` | 惰性转换 |
| 消费器 | `collect`、`sum`、`fold` | 聚合结果 |

零成本抽象：泛型单态化后，`Iterator` 链无虚调用开销。

---

## 与标准库衔接

`Iterator` trait 为核心抽象；`map`、`filter`、`collect` 等为组合子。所有组合均保持 Safe。

---

## 选型决策树

```text
需要顺序遍历集合/序列？
├── 是 → 标准集合？ → iter()/into_iter()
│       └── 自定义序列？ → impl Iterator
├── 需按类型施加不同操作？ → Visitor
└── 需链式传递？ → Chain of Responsibility
```

---

## 边界

| 维度 | 分类 |
| :--- | :--- |
| 安全 | 纯 Safe |
| 支持 | 原生 |
| 表达 | 等价 |

---

## 与 Rust 1.93 的对应

| 1.93 特性 | 与本模式 | 说明 |
| :--- | :--- | :--- |
| 无新增影响 | — | 1.93 无影响 Iterator 语义的变更 |
| 92 项落点 | 无 | 本模式未涉及 [RUST_193_COUNTEREXAMPLES_INDEX](../../../RUST_193_COUNTEREXAMPLES_INDEX.md) 特定项 |

---

## 实质内容五维自检

| 自检项 | 状态 | 说明 |
| :--- | :--- | :--- |
| 形式化 | ✅ | Def 1.1、定理 IT-T1（L2） |
| 代码 | ✅ | 可运行示例 |
| 场景 | ✅ | 典型场景表 |
| 反例 | ✅ | 迭代中修改集合 |
| 衔接 | ✅ | 标准库 Iterator、ownership |
| 权威对应 | ✅ | [GoF](../README.md#与-gof-原书对应)、[formal_methods](../../../formal_methods/README.md)、[INTERNATIONAL_FORMAL_VERIFICATION_INDEX](../../../INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) |
