# Rust 形式化验证学术导读

> **最后更新日期**: 2026-04-24  
> **预计下次复查日期**: 2026-10-24  
> **文档类型**: 学术导读 + 学习路径  
> **前置知识**: Rust 所有权系统基础、一阶逻辑基础

---

## 1. 为什么 Rust 需要形式化验证？

Rust 的核心卖点是**编译时内存安全保证**，但这个保证本身依赖于：

1. **类型系统的正确性**: 编译器的类型检查是否正确实现了 Rust 的类型规则？
2. **unsafe Rust 的边界**: `unsafe` 块是否确实遵循了编译器假设的不变式？
3. **编译器实现的正确性**: MIR → LLVM IR 的转换是否保持了语义？

形式化验证通过**数学证明**回答这些问题，而非仅依赖测试。

---

## 2. RustBelt (POPL 2017/2021)

### 2.1 论文信息

- **标题**: *"RustBelt: Securing the Foundations of the Rust Programming Language"*
- **作者**: Ralf Jung, Jacques-Henri Jourdan, Robbert Krebbers, Derek Dreyer
- **会议**: POPL 2017 (Symposium on Principles of Programming Languages)
- **扩展版本**: *"Safe Systems Programming in Rust: The Promise and the Challenge"*, CACM 2021

### 2.2 核心问题

RustBelt 回答了一个根本问题：

> **Rust 的内存安全保证是否依赖于标准库实现的正确性？**

答案：**是的**，且这些实现大量使用了 `unsafe` 代码。

Rust 标准库中约 20-30% 的代码涉及 `unsafe`（`Vec`、`HashMap`、`Rc`、`Arc` 等核心类型）。如果这些 `unsafe` 实现有 bug，整个 Rust 的安全保证就会崩溃。

### 2.3 理论基础：Iris 逻辑

RustBelt 基于 **Iris**（一种高阶并发分离逻辑，HoCAP 2015）构建：

```text
Iris 逻辑的核心概念:

┌────────────────────────────────────────────────────────┐
│  Iris: 高阶并发分离逻辑 (Higher-Order Concurrent      │
│        Separation Logic)                                │
├────────────────────────────────────────────────────────┤
│  • 资源代数 (Resource Algebra): 可组合的程序资源        │
│  • 不变式 (Invariant): 程序状态的全局约束               │
│  • 高阶幽灵状态 (Higher-Order Ghost State): 逻辑层面的  │
│    辅助状态，用于证明但不影响运行                        │
│  • 模态算子 (Modality): ▷ (later), □ (persistently)   │
└────────────────────────────────────────────────────────┘
```

#### 关键逻辑规则（直观理解）

**分离合取 (Separating Conjunction, ∗)**:

```
P ∗ Q 表示资源 P 和 Q 占据不相交的内存区域

例如:  owning(x) ∗ owning(y)  意味着 x 和 y 拥有不同的堆内存
```

**点态谓词 (Points-to Predicate)**:

```
ℓ ↦ v  表示地址 ℓ 存储了值 v，且当前上下文拥有该内存

这是所有权系统的逻辑基础:
- 如果 ℓ ↦ v 成立，那么 ℓ 的内存是有效的
- ℓ ↦ v 不能与其他 ℓ ↦ v' 同时成立（唯一所有权）
```

### 2.4 RustBelt 的方法论

RustBelt 将 Rust 类型翻译为 Iris 逻辑断言：

```text
类型解释函数 (语义解释):

┌─────────────────────────────────────────────────────────┐
│  ⟦ Vec<T> ⟧  =  ∃ ℓ, cap, len. ℓ ↦ (cap, len, array)  │
│                  ∗ own(array[0..len])                   │
│                  ∗ (cap ≥ len)                           │
│                                                         │
│  ⟦ &mut T ⟧  =  ∃ ℓ. ℓ ↦ -  ∗  (ℓ ↦ v ▷ ⟦T⟧(v))       │
│                  (可恢复的所有权)                        │
│                                                         │
│  ⟦ &T ⟧     =  ∃ ℓ. readonly(ℓ)  (共享只读访问)         │
└─────────────────────────────────────────────────────────┘
```

### 2.5 RustBelt 的关键结论

| 结论 | 含义 |
|------|------|
| **类型安全性** | 如果 Rust 程序通过类型检查且不使用 `unsafe`，则程序没有内存安全问题 |
| ** unsafe 契约 ** | `unsafe` 代码的编写者必须手动维持 Iris 不变式，这是编译器无法检查的 |
| **库正确性** | 标准库的核心 `unsafe` 代码已被 RustBelt 框架形式化验证（部分） |

### 2.6 RustBelt 的影响

- 直接催生了 **Miri**（Rust 的未定义行为检测器）
- 为 **Stacked Borrows / Tree Borrows** 内存模型提供了理论基础
- 启发了后续的 RefinedRust 项目

---

## 3. RefinedRust (PLDI 2024)

### 3.1 论文信息

- **标题**: *"RefinedRust: A Type System for High-Assurance Verification of Rust Programs"*
- **作者**: Lennard Gäher, et al.
- **会议**: PLDI 2024 (ACM SIGPLAN Conference on Programming Language Design and Implementation)
- **项目地址**: <https://gitlab.mpi-sws.org/lgaeher/refinedrust>

### 3.2 核心目标

RefinedRust 解决的是 RustBelt 的**实践局限性**：

> RustBelt 证明了 Rust 类型系统的理论安全性，但没有提供**验证具体程序功能正确性**的工具。

RefinedRust 的设计目标是：

1. **高保证验证**: 验证程序不仅内存安全，而且功能正确
2. **自动化**: 尽可能多的验证步骤自动完成
3. **与 Rust 集成**: 直接处理 Rust 源代码，而非中间表示

### 3.3 架构

```text
RefinedRust 工作流程:

┌─────────────────────────────────────────────────────────┐
│  Rust Source Code                                       │
│  + 用户提供的规格说明 (refinement annotations)           │
└─────────────┬───────────────────────────────────────────┘
              │
┌─────────────▼───────────────────────────────────────────┐
│  1. Rust Compiler Frontend (rustc)                      │
│     - 解析、类型检查、生成 THIR                         │
└─────────────┬───────────────────────────────────────────┘
              │
┌─────────────▼───────────────────────────────────────────┐
│  2. RefinedRust 转换器                                   │
│     - THIR → 形式化中间表示 (Caesium IR)                │
│     - 提取所有权和生命周期信息                            │
└─────────────┬───────────────────────────────────────────┘
              │
┌─────────────▼───────────────────────────────────────────┐
│  3. 验证条件生成 (VCG)                                   │
│     - 生成 Isabelle/HOL 证明义务                         │
│     - 或调用 SMT solver (Z3, CVC5)                      │
└─────────────┬───────────────────────────────────────────┘
              │
┌─────────────▼───────────────────────────────────────────┐
│  4. 自动/交互式证明                                       │
│     - SMT: 完全自动化 (简单性质)                          │
│     - Isabelle: 交互式 (复杂不变式)                       │
└─────────────────────────────────────────────────────────┘
```

### 3.4 精炼类型 (Refinement Types) 示例

RefinedRust 允许在 Rust 类型上附加**逻辑谓词**：

```rust
// RefinedRust 注释语法 (概念性示例)
#[refined("len >= 0 && len <= cap")]
struct Vec<T> {
    buf: RawVec<T>,
    len: usize,    // 精炼: len >= 0
}

impl<T> Vec<T> {
    // 前置条件: idx < self.len
    // 后置条件: 返回值是 self 的第 idx 个元素
    #[refined("requires: idx < self.len; ensures: result == self[idx]")]
    fn get(&self, idx: usize) -> &T {
        &self.buf[idx]
    }
}
```

### 3.5 RefinedRust vs RustBelt 对比

| 维度 | RustBelt | RefinedRust |
|------|---------|-------------|
| **目标** | 类型系统安全性证明 | 具体程序功能正确性验证 |
| **验证对象** | 类型规则本身 | 带有精炼类型的 Rust 程序 |
| **自动化程度** | 手动 Coq 证明 | 半自动 (SMT + 交互式) |
| **工具链** | Coq + Iris | Isabelle/HOL + Rust 编译器 |
| **学习曲线** | 陡峭 (需掌握 Coq/Iris) | 较陡 (需掌握 Isabelle) |
| **实际应用** | 理论验证标准库 | 验证安全关键系统 |

---

## 4. 面向学习者的阅读路径

### 4.1 基础阶段 (1-2 周)

**目标**: 理解形式化验证的基本思想和 Rust 为什么需要它

| 资源 | 时间 | 产出 |
|------|------|------|
| 阅读本导读文档 | 30 min | 了解整体图景 |
| Ralf Jung 的博客: *"The RustBelt Paper"* | 1h | 理解核心问题 |
| Rust 官方 Unsafe Rust Guidelines | 2h | 了解 unsafe 边界 |
| Miri 使用教程 | 1h | 实际操作 UB 检测 |

### 4.2 进阶阶段 (2-4 周)

**目标**: 理解分离逻辑和 Iris 的基础概念

| 资源 | 时间 | 产出 |
|------|------|------|
| *"Separation Logic: A Logic for Shared Mutable Data Structures"* (John Reynolds, 2002) | 3h | 分离逻辑基础 |
| Iris 教程: <https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf> | 5h | Iris 逻辑入门 |
| RustBelt 论文 (POPL 2017) | 4h | 理解类型解释方法 |
| Ralf Jung 的博士论文 (2020) | 6h | 深入理解并发验证 |

### 4.3 高级阶段 (4-8 周)

**目标**: 能够阅读/编写形式化证明

| 资源 | 时间 | 产出 |
|------|------|------|
| Coq 基础教程 (<https://softwarefoundations.cis.upenn.edu/>) | 10h | 掌握证明助手 |
| Iris 基础项目练习 | 10h | 编写简单分离逻辑证明 |
| RustBelt Coq 代码阅读 | 10h | 理解实际证明结构 |
| RefinedRust 论文 (PLDI 2024) | 5h | 了解最新进展 |

### 4.4 学习路径图

```text
                    ┌──────────────────┐
                    │  Rust 所有权基础  │
                    └────────┬─────────┘
                             │
              ┌──────────────┼──────────────┐
              ▼              ▼              ▼
        ┌─────────┐   ┌──────────┐   ┌──────────┐
        │ Miri 实践 │   │ 分离逻辑  │   │ Unsafe  │
        │         │   │ 基础      │   │ 指南     │
        └────┬────┘   └────┬─────┘   └────┬─────┘
             │             │              │
             └─────────────┼──────────────┘
                           ▼
                    ┌──────────────┐
                    │ RustBelt 论文 │
                    │ (POPL 2017)   │
                    └──────┬───────┘
                           │
              ┌────────────┼────────────┐
              ▼            ▼            ▼
        ┌─────────┐  ┌─────────┐  ┌──────────┐
        │ Iris    │  │ Tree    │  │ Refined  │
        │ 深入    │  │ Borrows │  │ Rust     │
        │         │  │ 模型    │  │ (PLDI'24)│
        └─────────┘  └─────────┘  └──────────┘
```

---

## 5. 与项目已有形式化证明内容的衔接

### 5.1 现有内容盘点

本项目在 `archive/docs/research_notes` 中已有的形式化相关内容：

- 线性类型理论基础
- 所有权与借用的逻辑建模
- 生命周期分析框架

### 5.2 衔接建议

| 现有内容 | RustBelt 对应 | 扩展方向 |
|---------|--------------|---------|
| 线性类型理论 | RustBelt 的 owning(x) 谓词 | 引入 Iris 具体编码 |
| 所有权转移分析 | ⟦ move semantics ⟧ | 分离逻辑规则化 |
| 借用生命周期 | lifetime logic | 区域与分离逻辑的结合 |
| 并发安全模型 | RustBelt + Iris 并发 | Sync/Send 的形式化语义 |

### 5.3 新增研究方向建议

1. **Tree Borrows 模型**: 作为 Stacked Borrows 的替代，更精确地描述 Rust 的别名规则
2. **Miri 的交互使用**: 将 Miri 作为 "半形式化" 验证工具引入教学流程
3. **Kani 验证器**: AWS 开发的 Rust 模型检查器，比 RefinedRust 更易用

---

## 6. 关键概念速查表

| 术语 | 解释 |
|------|------|
| **分离逻辑 (Separation Logic)** | 扩展霍尔逻辑，支持对堆内存的局部推理 |
| **Iris** | 高阶并发分离逻辑框架，RustBelt 的基础 |
| **Points-to (↦)** | "地址 ℓ 存储值 v" 的逻辑谓词，所有权的逻辑表达 |
| **Refinement Type** | 带逻辑谓词约束的类型，如 `{x: i32 | x > 0}` |
| **VCG (Verification Condition Generator)** | 将程序转换为逻辑证明义务的工具 |
| **MIR (Mid-level IR)** | Rust 编译器的中级中间表示，分析和优化的基础 |
| **THIR** | Typed HIR，MIR 之前的类型化表示 |
| **Ghost State** | 仅在逻辑层面存在、不影响程序执行的辅助状态 |

---

## 7. 参考文献

1. **Jung, R., Jourdan, J.-H., Krebbers, R., & Dreyer, D.** *"RustBelt: Securing the Foundations of the Rust Programming Language"*. POPL 2017.  
   ACM, 2017. <https://doi.org/10.1145/3009837.3009844>

2. **Jung, R., et al.** *"Safe Systems Programming in Rust: The Promise and the Challenge"*. Communications of the ACM, 64(4), 2021.  
   <https://doi.org/10.1145/3418295>

3. **Gäher, L., et al.** *"RefinedRust: A Type System for High-Assurance Verification of Rust Programs"*. PLDI 2024.  
   ACM, 2024.

4. **Krebbers, R., Timany, A., & Birkedal, L.** *"Interactive Proofs in Higher-Order Concurrent Separation Logic"*. POPL 2017.  
   (Iris 逻辑核心论文)

5. **Jung, R.** *"Understanding and Evolving the Rust Programming Language"*. PhD Thesis, Saarland University, 2020.

6. **Reynolds, J. C.** *"Separation Logic: A Logic for Shared Mutable Data Structures"*. LICS 2002.  
   IEEE, 2002.

7. **Ralf Jung's Blog**. "The RustBelt Paper and What It Means for Rust".  
   <https://ralfj.de/blog/2017/01/20/the-rustbelt-paper.html>

8. **Tree Borrows**. "Tree Borrows: A New Aliasing Model for Rust".  
   <https://www.ralfj.de/blog/2023/06/02/tree-borrows.html>

---

> 📌 **复查记录**
> - 2026-04-24: 初始创建，综合 POPL 2017 和 PLDI 2024 核心成果
> - 下次复查: 2026-10-24 (跟踪 RefinedRust 工具链成熟度和新论文)
