> **内容分级**:
>
> [专家级]
> **代码状态**: 📋 预览/研究 — AutoVerus 为 OOPSLA 2025 论文，Verus 活跃开发中
> **定理链**: N/A — 形式化验证工具/AI 辅助证明研究跟踪
>
# AutoVerus / Verus 预览
>
> **EN**: AutoVerus / Verus
> **Summary**: Verus 是用 Rust 本身编写规格与证明的 SMT 验证器；AutoVerus 是基于 LLM 的自动化证明生成系统，已在 Verus-Bench 上达到 >90% 成功率。
> **受众**: [进阶] 形式化方法、系统软件验证研究者
> **Bloom 层级**: 分析 → 评价
> **A/S/P 标记**: **A+S** — Application + Structure
> **双维定位**: C×Eva
> **前置依赖**: [形式化验证](../04_formal/05_verification_toolchain.md) · [形式化验证工具生态](../06_ecosystem/47_formal_verification_tools.md)
> **后置延伸**: [Safety Tags](./31_safety_tags_preview.md) · [BorrowSanitizer](./32_borrow_sanitizer_preview.md)
>
> **来源**: [Verus GitHub](https://github.com/verus-lang/verus) · [Verus 文档](https://verus-lang.github.io/verus/) · [AutoVerus 论文 (OOPSLA 2025)](https://doi.org/10.1145/3763174) · [arXiv 版本](https://arxiv.org/abs/2409.13082)

> **前置概念**: N/A
> **后置概念**: N/A
---

## 一、权威定义

> Verus is a tool for verifying the correctness of Rust code using proofs and specifications also written in Rust.
> —— AutoVerus 论文

**Verus** 允许开发者用 Rust 语法编写程序、规格（specifications）和证明（proofs），然后调用 SMT 求解器（Z3）自动验证。它充分利用 Rust 类型系统（Type System）已经保证的内存安全（Memory Safety）与线程安全， thus the verifier only needs to reason about functional correctness.

**AutoVerus** 则进一步利用大语言模型（LLM）自动为 Verus 程序生成证明，降低形式化验证的专家门槛。

---

## 二、Verus 核心机制

### 2.1 三段式程序结构

```rust,ignore
// 规格函数（spec function），编译时擦除
pub closed spec fn sorted(seq: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] <= seq[j]
}

// 可执行函数 + 规格注释
fn binary_search(v: &Vec<i32>, x: i32) -> (r: usize)
    requires
        sorted(v@),           // 前置条件：输入有序
        exists|i: int| 0 <= i < v.len() && v[i] == x,  // x 存在
    ensures
        r < v.len(),
        v[r as int] == x,     // 后置条件：返回正确索引
{
    // 实现 + loop invariants + proof hints
    // ...
}
```

关键元素：

- `spec fn`：纯函数规格，用于表达数学性质。
- `requires`：前置条件。
- `ensures`：后置条件。
- `v@`：将执行期 `Vec` 提升为规格期 `Seq`。
- `forall` / `exists`：一阶逻辑量词。

### 2.2 与 Rust 借用检查器的关系

Verus 的证明语言是 Rust 的超集，但验证时：

1. Rust 借用（Borrowing）检查器保证内存安全（Memory Safety）、线程安全；
2. Verus 验证器在此基础上证明功能正确性。

这种分层显著减少了验证器需要处理的复杂度。

---

## 三、AutoVerus：LLM 驱动的自动化证明

### 3.1 设计原则

AutoVerus 论文提出五个核心原则：

1. **不依赖大量训练数据**：直接使用通用 LLM（如 GPT-4o），无需针对 Verus 微调。
2. **用专家知识弥补数据不足**：将 Verus 专家常见证明策略编码为 prompt。
3. **释放 LLM 创造力**：高温采样生成多样化证明候选。
4. **用形式化方法约束创造力**：通过静态分析和 Verus 反馈快速过滤无效候选、拼接证明片段。
5. **三阶段工作流**：生成 → 精炼 → 调试。

### 3.2 三阶段工作流

```text
┌─────────────────┐    ┌─────────────────┐    ┌─────────────────┐
│ 1. Generation   │ -> │ 2. Refinement   │ -> │ 3. Debugging    │
│ 生成 loop inv   │    │ 常见错误修复     │    │ 针对 Verus 错误 │
│ 多候选输出      │    │ 常量传播、数组长度│   │ 迭代修复        │
└─────────────────┘    └─────────────────┘    └─────────────────┘
```

### 3.3 评估结果

- 在 **Verus-Bench**（150 个非平凡证明任务）上，AutoVerus 成功率 **>90%**。
- 超过一半任务在 **30 秒或 3 次 LLM 调用内**完成。

---

## 四、Verus / AutoVerus 在 Rust 生态中的位置

| 工具 | 方法 | 自动化程度 | 适用场景 |
|:---|:---|:---|:---|
| Kani | 模型检查 | 高（无需求规格） | 有界状态空间、单测 |
| Prusti | 分离逻辑 + Viper | 中（需写规格） | 复杂数据结构和不变量 |
| Creusot | Why3/WhyML | 中（需写规格） | 函数式风格证明 |
| **Verus** | SMT + Rust 语法 | 中（需写规格） | 系统级代码功能正确性 |
| **AutoVerus** | LLM + Verus | 高（自动生成证明） | 降低 Verus 入门门槛 |

---

## 五、当前状态与时间表

| 时间 | 里程碑 |
|:---|:---|
| 2023 | Verus 论文发表于 OOPSLA |
| 2024 | Verus 在 SOSP 展示系统代码验证案例；vstd 标准库规格不断丰富 |
| 2025 | AutoVerus 论文发表于 OOPSLA；Verus-Bench 发布 |
| 2026 | Verus 持续活跃开发；社区探索与 Safety Tags、Kani、BorrowSanitizer 的集成 |

---

## 六、反命题与边界

- **规格仍由人写**：AutoVerus 自动生成的是**证明**，不是规格。规格是否表达真实意图仍需人工判断。
- **LLM 不可解释性**：当 AutoVerus 失败时，调试成本可能高于手写证明。
- **仅限 Verus 子集**：复杂所有权（Ownership）、unsafe 代码、异步（Async）代码的自动证明仍具挑战。
- **工具链演进**：Verus 语言和标准库规格仍在快速迭代，AutoVerus 需要持续适配。

---

## 七、嵌入式测验

**测验 1**: Verus 使用哪种后端求解器验证 Rust 程序？

- A. Coq
- B. Z3（SMT）
- C. Isabelle/HOL
- D. LLVM

<details>
<summary>答案</summary>
B
</details>

**测验 2**: AutoVerus 自动生成的是程序的哪个部分？

- A. 规格（specifications）
- B. 证明（proofs）
- C. 可执行代码
- D. 测试用例

<details>
<summary>答案</summary>
B
</details>

---

## 相关概念

- [形式化验证](../04_formal/05_verification_toolchain.md)
- [形式化验证工具生态](../06_ecosystem/47_formal_verification_tools.md)
- [AutoVerus/Verus 深度](../04_formal/24_autoverus.md)
- [Safety Tags 预览](./31_safety_tags_preview.md) · [深度](../04_formal/22_safety_tags.md)
- [BorrowSanitizer 预览](./32_borrow_sanitizer_preview.md) · [深度](../04_formal/23_borrow_sanitizer.md)
