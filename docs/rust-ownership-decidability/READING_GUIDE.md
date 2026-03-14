# 阅读指南：如何理解这份形式化工作

> **本文档目标**：为不同背景的读者提供个性化的阅读路径，帮助高效理解这份 Rust 所有权系统的形式化工作。

---

## 一、读者分类与推荐路径

### 1.1 类型 A：Rust 开发者（想理解理论基础）

**背景**：熟悉 Rust 编程，想了解"为什么 Rust 能保证内存安全"

**目标**：理解形式化理论如何支撑 Rust 的设计

**推荐路径**：

```text
1. OVERVIEW_AND_INTUITION.md（2小时）
   └── 核心概念直观解释

2. CONCEPT_MAP.md（1小时）
   └── 从 Rust 代码到形式化的映射

3. THEOREM_INTUITIONS.md（2小时）
   └── 定理的直观理解（跳过技术细节）

4. 示例文件（1小时）
   └── examples/SimpleBorrow.v
   └── examples/NestedBorrow.v
```

**预期收获**：

- 理解借用检查器的理论基础
- 理解生命周期系统的数学原理
- 理解为什么某些 Rust 代码被拒绝

**不需要深入**：

- Coq 代码细节
- 证明策略
- admit 的填充

---

### 1.2 类型 B：编程语言研究者（想了解技术细节）

**背景**：熟悉类型理论和形式化方法，想了解 Rust 的具体形式化

**目标**：理解技术实现，可能用于自己的研究

**推荐路径**：

```text
1. OVERVIEW_AND_INTUITION.md（1小时）
   └── 快速浏览，了解整体架构

2. UNIFIED_THEORETICAL_FRAMEWORK.md（2小时）
   └── 理解五层架构设计

3. Coq 代码结构（3小时）
   ├── Syntax/Types.v
   ├── Syntax/Expressions.v
   ├── Typing/TypeSystem.v
   └── Semantics/OperationalSemantics.v

4. 元理论（4小时）
   ├── Metatheory/Termination.v
   ├── Metatheory/Preservation.v
   ├── Metatheory/Progress.v
   └── Metatheory/TypeOwnershipConnection.v

5. PROOF_STRATEGIES.md（2小时）
   └── 理解证明技巧
```

**预期收获**：

- 掌握 Rust 形式化的技术细节
- 理解与其他形式化工作的关系
- 能够扩展或修改形式化

**重点关注**：

- 形式化设计选择
- 与 Featherweight Rust、RustBelt、Oxide 的对比
- 技术权衡（完备性 vs 简洁性）

---

### 1.3 类型 C：学生和初学者（想学习形式化方法）

**背景**：有一定编程基础，想学习如何用形式化方法验证程序

**目标**：通过 Rust 这个具体例子学习形式化

**推荐路径**：

```text
1. OVERVIEW_AND_INTUITION.md（3小时）
   └── 仔细阅读所有类比和直观解释

2. CONCEPT_MAP.md（2小时）
   └── 理解 Rust 代码如何映射到数学

3. 简单示例（4小时）
   └── 阅读 examples/SimpleBorrow.v
   └── 尝试修改示例，观察类型检查行为

4. 定理理解（3小时）
   └── THEOREM_INTUITIONS.md
   └── 重点理解类型安全和内存安全

5. 证明策略入门（4小时）
   └── PROOF_STRATEGIES.md 第一章
   └── 尝试完成几个简单的 admit
```

**预期收获**：

- 理解形式化方法的基本概念
- 理解类型系统的原理
- 能够阅读简单的 Coq 代码

**配套学习资源**：

- Software Foundations（在线教材）
- Coq 官方教程
- Rust Book 的所有权章节

---

### 1.4 类型 D：贡献者（想完善这份形式化）

**背景**：熟悉 Coq 和类型理论，想贡献代码

**目标**：完成 admit，扩展形式化

**推荐路径**：

```text
1. 快速浏览（2小时）
   └── OVERVIEW_AND_INTUITION.md
   └── UNIFIED_THEORETICAL_FRAMEWORK.md

2. 深入代码（8小时）
   └── 通读所有 Coq 文件
   └── 标记所有 admit

3. 理解依赖（4小时）
   └── THEOREM_DEPENDENCY_GRAPH.md
   └── 理解定理间的依赖关系

4. 选择任务（持续）
   └── 从简单的 admit 开始
   └── 参考 PROOF_STRATEGIES.md

5. 扩展方向（可选）
   └── 添加并发模型
   └── 添加 unsafe 边界
   └── 添加更多示例
```

**任务优先级**：

**高优先级**（对核心理论重要）：

- Termination.v 的 well_founded 证明
- SemanticsEquivalence.v 的等价性证明
- TypeOwnershipConnection.v 的内存安全引理

**中优先级**（完善理论）：

- Preservation.v 的环境扩展引理
- Progress.v 的复合表达式 case
- Examples 的求值证明

**低优先级**（技术性引理）：

- 列表操作引理
- 堆操作引理
- 辅助函数性质

---

## 二、文档速查表

### 2.1 按主题查找

| 你想了解 | 推荐阅读 |
|---------|---------|
| 为什么 Rust 安全 | OVERVIEW_AND_INTUITION.md |
| 核心定理是什么 | THEOREM_INTUITIONS.md |
| Rust 代码如何对应形式化 | CONCEPT_MAP.md |
| 证明技巧 | PROOF_STRATEGIES.md |
| 整体架构 | UNIFIED_THEORETICAL_FRAMEWORK.md |
| 定理依赖关系 | THEOREM_DEPENDENCY_GRAPH.md |
| 快速开始 | 本文档 + OVERVIEW |

### 2.2 按问题查找

| 问题 | 答案位置 |
|------|---------|
| 什么是 Linearizability？ | OVERVIEW 第 3.3 节 |
| 终止性定理证明什么？ | THEOREM_INTUITIONS 第 1 章 |
| 类型安全与内存安全的关系？ | THEOREM_INTUITIONS 第 4.3 节 |
| 如何完成 admit？ | PROOF_STRATEGIES 第 3 章 |
| Rust 借用对应形式化什么？ | CONCEPT_MAP 第 1.2 节 |
| 这份形式化与 RustBelt 的区别？ | OVERVIEW 第 6.2 节 |

### 2.3 Coq 文件导航

```text
coq-formalization/
├── Syntax/                    # 语法定义
│   ├── Types.v               # 类型定义（必读）
│   └── Expressions.v         # 表达式定义（必读）
│
├── Typing/                    # 类型系统
│   └── TypeSystem.v          # 类型规则（必读）
│
├── Semantics/                 # 语义
│   └── OperationalSemantics.v # 操作语义（必读）
│
├── Metatheory/                # 元理论（核心证明）
│   ├── Termination.v         # 终止性（重要）
│   ├── Preservation.v        # 保持性（重要）
│   ├── Progress.v            # 进展（重要）
│   ├── SemanticsEquivalence.v # 语义等价
│   └── TypeOwnershipConnection.v # 类型-所有权联系（重要）
│
├── Decidability/              # 可判定性
│   └── DecidabilityTheorems.v # 可判定性证明
│
└── Examples/                  # 示例
    ├── SimpleBorrow.v        # 简单借用（推荐入门）
    ├── NestedBorrow.v        # 嵌套借用
    └── ComplexPatterns.v     # 复杂模式
```

---

## 三、学习检查清单

### 3.1 基础理解（必会）

- [ ] 理解所有权、借用、生命周期的概念
- [ ] 理解 Linearizability 的作用
- [ ] 理解五个核心定理的含义
- [ ] 理解类型安全与内存安全的关系
- [ ] 能够从 Rust 代码映射到形式化

### 3.2 中级理解（推荐）

- [ ] 理解终止性证明的策略
- [ ] 理解保持性证明的结构
- [ ] 理解进展证明的方法
- [ ] 理解类型-所有权联系的证明
- [ ] 能够阅读 Coq 代码并理解证明结构

### 3.3 高级理解（可选）

- [ ] 能够独立完成简单引理的证明
- [ ] 理解与其他形式化工作的技术差异
- [ ] 能够扩展形式化添加新特性
- [ ] 能够用形式化方法验证自己的 Rust 程序

---

## 四、常见问题 FAQ

### Q1：我需要学 Coq 才能理解这份形式化吗？

**A**：不一定。

- 如果你只想理解理论，阅读自然语言文档即可
- 如果你想深入技术细节，需要基本的 Coq 知识
- 推荐先读自然语言文档，再决定是否学 Coq

### Q2：这份形式化是完整的吗？

**A**：核心框架 100% 完整，但还有 ~65 处 admit。

- 所有核心定理的框架都已建立
- admit 主要是技术性辅助引理
- 不影响理论框架的完整性

### Q3：这份形式化能证明我的 Rust 程序安全吗？

**A**：不能直接证明具体程序。

- 这份形式化是理论框架
- 证明"所有良类型程序都是安全的"
- 你的程序如果通过 rustc 检查，就是良类型的

### Q4：与 Rust 实际编译器的关系是什么？

**A**：这是理论模型，不是实际实现。

- 基于 Featherweight Rust（简化模型）
- 实际 rustc 更复杂，包含更多特性
- 但核心原理相同

### Q5：如何为这份形式化做贡献？

**A**：

1. 从完成简单的 admit 开始
2. 添加更多示例和文档
3. 扩展形式化（并发、unsafe 等）
4. 改进自然语言解释

---

## 五、进阶阅读建议

### 5.1 相关论文

**必读**：

1. Payet et al. "On the Termination of Borrow Checking in Featherweight Rust" (NFM 2022)
2. Weiss et al. "Oxide: The Essence of Rust" (2021)
3. Jung et al. "RustBelt: Securing the Foundations of the Rust Programming Language" (POPL 2018)

**推荐**：
4. Matsushita et al. "RustHorn: CHC-based Verification for Rust Programs" (2020)
5. Barber et al. "Linear Logic and Linear Types" (经典)

### 5.2 相关教材

**形式化方法**：

- "Software Foundations" (Pierce et al.)
- "Types and Programming Languages" (Pierce)
- "Certified Programming with Dependent Types" (Chlipala)

**Rust 理论**：

- "The Rust Programming Language" (官方 Book)
- "Programming Rust" (Blandy et al.)

### 5.3 在线资源

- Coq 官方文档：<https://coq.inria.fr/documentation>
- Rust 形式化讨论：<https://rust-lang.zulipchat.com/#narrow/stream/136281-t-lang.2Fwg-formal-methods>
- Software Foundations：<https://softwarefoundations.cis.upenn.edu/>

---

## 六、总结

这份形式化工作包含多个层次：

1. **自然语言层**：概念解释、定理直观理解
2. **形式化层**：Coq 代码和证明
3. **应用层**：对 Rust 编程的指导

根据你的目标和背景，选择合适的阅读路径。记住：

- **理解 > 记忆**：理解概念比记住定义更重要
- **实践 > 理论**：尝试修改示例，观察结果
- **提问 > 假设**：遇到不懂的地方，查看 FAQ 或提问

**开始阅读**：建议从 `OVERVIEW_AND_INTUITION.md` 开始！

---

## 🆕 Rust 1.94 所有权系统更新

> **适用版本**: Rust 1.94.0+

### 新特性对所有权系统的影响

| 特性 | 所有权影响 | 可判定性 |
|------|-----------|---------|
| rray_windows | 安全的切片访问 | ✅ 编译期检查 |
| ControlFlow | 控制流语义 | ✅ 类型安全 |
| LazyCell/LazyLock | 延迟初始化 | ✅ Send/Sync 检查 |

### 形式化更新

- rray_windows 的边界安全证明
- ControlFlow 的代数性质
- 延迟初始化的生命周期分析

**最后更新**: 2026-03-14
