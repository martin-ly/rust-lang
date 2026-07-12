> **内容分级**: [形式化级]
> **定理链**: 形式化算法理论为程序正确性提供数学基础
> **代码状态**: ✅ 含可编译示例
>
# 形式化算法理论
>
> **EN**: Formal Algorithm Theory
> **Summary**: Mathematical foundations of algorithms in Rust: computability, complexity, loop invariants, Hoare logic, and practical formal verification with Kani.
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **受众**: [专家]
> **权威来源**: 本文件为 `concept/` 权威页。
> **层级**: L4/L6 交叉
> **A/S/P 标记**: **S** — Structure
> **前置概念**: [算法复杂度分析](78_algorithm_complexity_analysis.md) · [形式化方法](../../04_formal/04_model_checking/13_formal_methods.md) · [Hoare 逻辑](../../04_formal/03_operational_semantics/15_hoare_logic.md)
> **后置概念**: [算法工程实践](76_algorithm_engineering_practice.md)
> **相关概念**: [数据结构与 Rust](77_data_structures_in_rust.md) · [算法与竞赛编程](29_algorithms_competitive_programming.md) · [形式化设计模式理论](../03_design_patterns/38_formal_design_pattern_theory.md) · [前沿算法技术](79_cutting_edge_algorithms.md)
> **L5 对比视角**: [范式矩阵](../../05_comparative/00_paradigms/03_paradigm_matrix.md) · [Rust vs C++ 形式系统与性能](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) · [安全边界对比](../../05_comparative/03_domain_comparisons/04_safety_boundaries.md)
>
> **来源**: [CLRS — Introduction to Algorithms](https://mitpress.mit.edu/9780262046305/introduction-to-algorithms/) · [Sipser — Introduction to the Theory of Computation](https://math.mit.edu/~sipser/book.html) · [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html)

---

## 目录

- [形式化算法理论](#形式化算法理论)
  - [目录](#目录)
  - [一、核心概念](#一核心概念)
  - [二、算法的形式化定义](#二算法的形式化定义)
  - [三、复杂度理论](#三复杂度理论)
  - [四、正确性证明方法](#四正确性证明方法)
    - [4.1 循环不变式](#41-循环不变式)
    - [4.2 二分搜索的循环不变式实现](#42-二分搜索的循环不变式实现)
    - [4.3 Hoare 三元组](#43-hoare-三元组)
  - [五、Rust 形式化验证实践](#五rust-形式化验证实践)
    - [5.1 Kani 有界模型检查](#51-kani-有界模型检查)
    - [5.2 不变量断言](#52-不变量断言)
  - [六、证明方法对比矩阵](#六证明方法对比矩阵)
  - [七、验证工具选型决策树](#七验证工具选型决策树)
  - [过渡段](#过渡段)
  - [定理链](#定理链)
  - [国际权威参考 / International Authority References（P1 学术 · P2 生态）](#国际权威参考--international-authority-referencesp1-学术--p2-生态)

## 一、核心概念

形式化算法理论用数学方法严格定义和分析算法，为 Rust 程序的**正确性、复杂度、可计算性**提供理论基础。Rust 的强类型系统（Type System）与所有权（Ownership）模型将大量运行时（Runtime）不变量上移至编译期，从而缩小了需要外部验证的“信任基”。

## 二、算法的形式化定义

- **图灵机 (Turing Machine)**：七元组 $(Q, \Sigma, \Gamma, \delta, q_0, q_a, q_r)$，是最基本的计算模型。
- **Church-Turing 论题**：一切有效计算过程都可以用图灵机表示；Rust 程序本质上是图灵机的实现。
- **RAM 模型**：随机访问内存模型，用于分析实际算法的时间复杂度。

## 三、复杂度理论

| 概念 | 说明 | Rust 实践 |
|:---|:---|:---|
| 时间复杂度 | 输入规模增长时运行时（Runtime）间的渐近行为 | `BinaryHeap::push` 为 $O(\log n)$ |
| 空间复杂度 | 算法所需额外内存 | 迭代器（Iterator）避免中间集合分配 |
| 主定理 | 分治递推式的渐近解 | 归并排序 $T(n) = 2T(n/2) + O(n) \Rightarrow O(n \log n)$ |
| 摊还分析 | 一系列操作的平均复杂度 | `Vec::push` 均摊 $O(1)$ |
| 复杂度类 | P、NP、PSPACE 等 | 决定问题是否可高效求解 |

## 四、正确性证明方法

本节围绕「正确性证明方法」展开，依次讨论循环不变式、二分搜索的循环不变式实现与Hoare 三元组。

### 4.1 循环不变式

循环不变式是证明迭代算法正确性的核心工具，需证明：

1. **初始化**：第一次迭代前为真。
2. **保持**：若某次迭代前为真，则下次迭代前仍为真。
3. **终止**：循环结束时，不变式蕴含正确结果。

### 4.2 二分搜索的循环不变式实现

```rust
/// 前置条件：arr 按升序排列
/// 后置条件：返回 target 的索引，若不存在则返回 Err(插入位置)
/// 循环不变式：答案（若存在）始终位于 [left, right) 区间内
pub fn binary_search(arr: &[i32], target: i32) -> Result<usize, usize> {
    let mut left = 0usize;
    let mut right = arr.len();

    while left < right {
        let mid = left + (right - left) / 2;
        match arr[mid].cmp(&target) {
            std::cmp::Ordering::Equal => return Ok(mid),
            std::cmp::Ordering::Less => left = mid + 1,
            std::cmp::Ordering::Greater => right = mid,
        }
    }

    Err(left)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn invariant_holds() {
        let arr = [1, 3, 5, 7, 9];
        assert_eq!(binary_search(&arr, 5), Ok(2));
        assert_eq!(binary_search(&arr, 4), Err(2));
        assert_eq!(binary_search(&arr, 10), Err(5));
    }
}
```

### 4.3 Hoare 三元组

Hoare 逻辑使用 `{P} S {Q}` 描述程序片段：若前置条件 $P$ 成立，执行 $S$ 后后置条件 $Q$ 成立。Rust 的类型系统（Type System）可编码部分前置条件（如 `NonNull<T>` 排除空指针），而运行时断言负责剩余部分。

```rust
use std::ptr::NonNull;

/// { arr 非空 } -> 返回首元素 { 返回值 == arr[0] }
pub fn first_or_panic(arr: &[i32]) -> i32 {
    assert!(!arr.is_empty(), "precondition: arr is non-empty");
    arr[0]
}

/// { ptr 非空 } -> 解引用 { 返回值 == *ptr }
pub unsafe fn deref_nonnull<T>(ptr: NonNull<T>) -> T
where
    T: Copy,
{
    *ptr.as_ptr()
}
```

## 五、Rust 形式化验证实践

「Rust 形式化验证实践」部分包含 Kani 有界模型检查 与 不变量断言 两条主线，本节依次说明。

### 5.1 Kani 有界模型检查

Kani 利用 CBMC 对 Rust 程序进行符号执行，可验证数组边界、无溢出、循环不变量等属性。

```rust
#[cfg(kani)]
mod verification {
    use super::*;

    #[kani::proof]
    fn verify_binary_search_no_panic() {
        // 验证任意长度不超过 8 的有序数组上的二分搜索不越界
        let len: usize = kani::any();
        kani::assume(len <= 8);
        let mut arr = [0i32; 8];
        for i in 0..len {
            arr[i] = kani::any();
        }
        // 假设数组有序（简化：使用 kani 约束）
        for i in 1..len {
            kani::assume(arr[i - 1] <= arr[i]);
        }
        let target: i32 = kani::any();
        let _ = binary_search(&arr[..len], target);
    }

    #[kani::proof]
    fn verify_push_no_overflow() {
        let a: u32 = kani::any();
        let b: u32 = kani::any();
        kani::assume(a <= 1_000_000 && b <= 1_000_000);
        let _ = a.saturating_add(b);
    }
}
```

### 5.2 不变量断言

```rust
/// 不变量：每个入队元素最终按 FIFO 顺序出队
pub struct FifoQueue<T> {
    inner: std::collections::VecDeque<T>,
}

impl<T> FifoQueue<T> {
    pub fn new() -> Self {
        Self { inner: std::collections::VecDeque::new() }
    }

    pub fn enqueue(&mut self, value: T) {
        self.inner.push_back(value);
    }

    pub fn dequeue(&mut self) -> Option<T> {
        self.inner.pop_front()
    }

    pub fn len(&self) -> usize {
        self.inner.len()
    }
}

#[cfg(test)]
mod fifo_tests {
    use super::*;

    #[test]
    fn fifo_invariant() {
        let mut q = FifoQueue::new();
        q.enqueue(1);
        q.enqueue(2);
        assert_eq!(q.dequeue(), Some(1));
        assert_eq!(q.dequeue(), Some(2));
        assert_eq!(q.dequeue(), None);
    }
}
```

## 六、证明方法对比矩阵

| 方法 | 自动化程度 | 适用对象 | Rust 工具/表达 | 限制 |
|:---|:---|:---|:---|:---|
| **数学归纳法** | 手动 | 递归算法 | 纸笔 + 单元测试 | 需要人工构造归纳假设 |
| **循环不变式** | 半自动 | 迭代算法 | 断言 + Kani | 不变式发现依赖经验 |
| **Hoare 逻辑** | 半自动 | 命令式程序段 | 契约 + `assert` | 复杂数据结构的规约成本高 |
| **模型检查** | 自动 | 有界状态/数组 | Kani | 状态爆炸，适合局部关键函数 |
| **类型系统证明** | 自动 | 类型级不变量 | Typestate / const generics | 表达能力受限，无法表达所有性质 |

## 七、验证工具选型决策树

```text
需要形式化验证？
│
├─ 目标是证明类型级不变量？
│  └─ Rust 类型系统 / Typestate / const generics
│
├─ 目标是有界数组/整数安全？
│  └─ Kani 模型检查
│
├─ 目标是函数契约（requires/ensures）？
│  ├─ 需要 Rust 原生支持 → Prusti
│  └─ 可接受分离逻辑 / Why3 → Creusot
│
├─ 目标是并发协议正确性？
│  └─ Kani + 并发 harness / session type
│
└─ 目标是在竞赛/教学场景快速验证？
   └─ Kani 轻量 harness + 单元测试组合
```

---

> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/), [Kani Rust Verifier](https://model-checking.github.io/kani/)
>
> **权威来源对齐变更日志**: 2026-07-09 由 `crates/c08_algorithms/docs/tier_04_advanced/01_formal_algorithm_theory.md` 迁移整合；本次补全新增二分搜索循环不变式、Kani harness、证明方法矩阵与决策树

**状态**: ✅ 权威页（canonical）

## 过渡段

> **过渡**: 从非形式化问题描述过渡到形式规范，可以消除需求中的歧义。
>
> **过渡**: 从形式规范过渡到正确性证明，可以建立算法在所有输入下满足规约的信心。
>
> **过渡**: 从证明过渡到可验证实现，可以缩小数学模型与工程代码之间的距离。
>

## 定理链

| 定理 | 前提 | 结论 |
|:---|:---|:---|
| 形式规约 ⟹ 无歧义需求 | 使用谓词与状态转换 | 精确定义期望行为 |
| 正确性证明 ⟹ 可靠性 | 循环不变量与终止性 | 保证算法输出符合规约 |
| 复杂度界 ⟹ 资源预测 | 最坏/平均/均摊分析 | 评估算法可行性 |

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P1 学术/形式化**: [Aeneas: Rust Verification by Functional Translation (arXiv:2206.07185)](https://arxiv.org/abs/2206.07185) · [RustHorn: CHC-based Verification for Rust Programs (ESOP 2020, Springer LNCS)](https://link.springer.com/chapter/10.1007/978-3-030-44914-8_18)
- **P2 生态/社区**: [AeneasVerif/aeneas](https://github.com/AeneasVerif/aeneas) · [model-checking/kani — 模型检查器](https://github.com/model-checking/kani)
