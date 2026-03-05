# 自然语言论证文档总览

> **本文档**：汇总所有自然语言论证文档，提供完整的导航和索引。

---

## 文档清单

### 🎯 核心理解文档

| 文档 | 目标读者 | 内容 | 阅读时间 |
|------|---------|------|---------|
| **OVERVIEW_AND_INTUITION.md** | 所有人 | 总览与直观理解 | 2-3 小时 |
| **THEOREM_INTUITIONS.md** | 所有人 | 定理的直观解释 | 2-3 小时 |
| **CONCEPT_MAP.md** | Rust 开发者 | 从 Rust 到形式化的映射 | 1-2 小时 |
| **READING_GUIDE.md** | 所有人 | 个性化阅读路径 | 30 分钟 |

### 🔧 技术文档

| 文档 | 目标读者 | 内容 | 阅读时间 |
|------|---------|------|---------|
| **PROOF_STRATEGIES.md** | 研究者/贡献者 | 证明策略详解 | 2-3 小时 |
| **UNIFIED_THEORETICAL_FRAMEWORK.md** | 研究者 | 五层架构框架 | 2 小时 |
| **THEOREM_DEPENDENCY_GRAPH.md** | 研究者 | 定理依赖网络 | 1 小时 |

---

## 按主题组织的阅读路径

### 主题 1：为什么 Rust 安全？（2 小时）

**目标**：理解 Rust 内存安全的理论基础

**阅读顺序**：

1. OVERVIEW_AND_INTUITION.md
   - 第 1 章：为什么要形式化
   - 第 2 章：核心概念直观解释
   - 第 7 章：内存安全定理

2. THEOREM_INTUITIONS.md
   - 第 7 章：内存安全定理
   - 第 6 章：借用检查等价性

**关键收获**：

- 类型正确 ⟹ 所有权安全 ⟹ 内存安全
- 借用检查器的正确性证明
- 生命周期系统的数学原理

---

### 主题 2：核心定理理解（3 小时）

**目标**：理解五个核心定理的含义和重要性

**阅读顺序**：

1. THEOREM_INTUITIONS.md（完整阅读）
   - 第 1 章：终止性
   - 第 2 章：保持性
   - 第 3 章：进展
   - 第 4 章：类型安全
   - 第 5 章：可判定性

2. OVERVIEW_AND_INTUITION.md
   - 第 3 章：核心理论的五个层次

**关键收获**：

- 终止性：借用检查会结束
- 保持性：类型在求值中保持
- 进展：程序不会卡住
- 类型安全 = 保持性 + 进展
- 可判定性：类型检查可自动化

---

### 主题 3：从 Rust 代码到形式化（2 小时）

**目标**：建立 Rust 代码与数学形式化之间的联系

**阅读顺序**：

1. CONCEPT_MAP.md（完整阅读）
   - 第 1 章：核心概念的三层映射
   - 第 2 章：类型系统的映射
   - 第 3 章：表达式映射
   - 第 5 章：从 Rust 程序到形式化证明

2. OVERVIEW_AND_INTUITION.md
   - 第 2 章：核心概念直观解释

**关键收获**：

- 所有权 = 环境中的类型绑定
- 借用 = 引用类型 + 可变性
- 生命周期 = 类型参数
- 类型检查 = has_type 判断

---

### 主题 4：证明技术（3 小时）

**目标**：理解形式化证明的技术细节

**阅读顺序**：

1. PROOF_STRATEGIES.md（完整阅读）
   - 第 1 章：通用证明技巧
   - 第 2 章：特定定理的证明策略
   - 第 3 章：完成 admit 的实用指南

2. THEOREM_DEPENDENCY_GRAPH.md
   - 理解定理间的依赖关系

**关键收获**：

- 结构归纳法
- 良基归纳法
- 反证法
- 构造性证明
- 完成 admit 的步骤

---

### 主题 5：完整掌握（10+ 小时）

**目标**：全面理解这份形式化工作

**阅读顺序**：

1. 所有自然语言文档（按上述顺序）
2. Coq 代码（按 READING_GUIDE 推荐）
3. 尝试完成 admit
4. 尝试添加新示例

---

## 概念索引

### A

**Ownership（所有权）**

- 直观解释：OVERVIEW 第 2.1 节
- 形式化定义：CONCEPT_MAP 第 1.1 节
- 与 Rust 对应：CONCEPT_MAP 第 1.1 节表

**Admit（未完成证明）**

- 如何完成：PROOF_STRATEGIES 第 3 章
- 分布：各 Coq 文件

### B

**Borrowing（借用）**

- 直观解释：OVERVIEW 第 2.1 节
- 形式化定义：CONCEPT_MAP 第 1.2 节
- 借用检查器：OVERVIEW 第 2.3 节

**Borrow Checker（借用检查器）**

- 正确性证明：THEOREM_INTUITIONS 第 6 章
- 等价性定理：THEOREM_INTUITIONS 第 6 章

### C

**概念映射**

- 完整映射：CONCEPT_MAP
- 三层映射：CONCEPT_MAP 第 1 章

### D

**Decidability（可判定性）**

- 直观解释：THEOREM_INTUITIONS 第 5 章
- 证明策略：PROOF_STRATEGIES 第 2.4 节

### E

**Eval（求值）**

- 大步语义：OVERVIEW 第 3.3 节
- 小步语义：OVERVIEW 第 3.3 节
- 语义等价：THEOREM_INTUITIONS 第 8 章

### H

**Has_type（类型判断）**

- 定义：CONCEPT_MAP 第 4.1 节
- 规则：TypeSystem.v

### I

**Intuition（直观理解）**

- 总览：OVERVIEW_AND_INTUITION.md
- 定理：THEOREM_INTUITIONS.md

### L

**Lifetime（生命周期）**

- 直观解释：OVERVIEW 第 2.2 节
- 形式化定义：CONCEPT_MAP 第 1.3 节
- 与 Rust 对应：CONCEPT_MAP 第 1.3 节表

**Linearizability**

- 直观解释：OVERVIEW 第 3.3 节
- 与终止性：THEOREM_INTUITIONS 第 1 章

### M

**Memory Safety（内存安全）**

- 定义：THEOREM_INTUITIONS 第 7.2 节
- 三个支柱：THEOREM_INTUITIONS 第 7.3 节
- 定理：THEOREM_INTUITIONS 第 7 章

### O

**Overview（总览）**

- 文档：OVERVIEW_AND_INTUITION.md
- 架构：UNIFIED_THEORETICAL_FRAMEWORK.md

### P

**Preservation（保持性）**

- 直观解释：THEOREM_INTUITIONS 第 2 章
- 证明策略：PROOF_STRATEGIES 第 2.2 节

**Progress（进展）**

- 直观解释：THEOREM_INTUITIONS 第 3 章
- 证明策略：PROOF_STRATEGIES 第 2.3 节

**Proof Strategies（证明策略）**

- 文档：PROOF_STRATEGIES.md

### R

**Reading Guide（阅读指南）**

- 文档：READING_GUIDE.md
- 个性化路径：READING_GUIDE 第 1 章

### S

**Semantics（语义）**

- 操作语义：OVERVIEW 第 3.3 节
- 大步/小步：THEOREM_INTUITIONS 第 8 章
- 等价性：THEOREM_INTUITIONS 第 8 章

**Structure（结构）**

- 五层架构：OVERVIEW 第 3 章
- 依赖图：THEOREM_DEPENDENCY_GRAPH.md

### T

**Termination（终止性）**

- 直观解释：THEOREM_INTUITIONS 第 1 章
- 证明策略：PROOF_STRATEGIES 第 2.1 节

**Theorem（定理）**

- 直观解释：THEOREM_INTUITIONS.md
- 依赖图：THEOREM_DEPENDENCY_GRAPH.md

**Type Safety（类型安全）**

- 直观解释：THEOREM_INTUITIONS 第 4 章
- 与内存安全：THEOREM_INTUITIONS 第 4.4 节

**Type Rank（类型秩）**

- 定义：OVERVIEW 第 3.3 节
- 作用：THEOREM_INTUITIONS 第 1 章

### U

**Unified Framework（统一框架）**

- 文档：UNIFIED_THEORETICAL_FRAMEWORK.md

### V

**Verification（验证）**

- 示例：Examples/ 目录

---

## 快速参考卡片

### 核心定理速查

| 定理 | 一句话总结 | 详细位置 |
|------|-----------|---------|
| 终止性 | 借用检查会结束 | THEOREM_INTUITIONS 第 1 章 |
| 保持性 | 类型不改变 | THEOREM_INTUITIONS 第 2 章 |
| 进展 | 程序不会卡住 | THEOREM_INTUITIONS 第 3 章 |
| 类型安全 | 类型 + 进展 | THEOREM_INTUITIONS 第 4 章 |
| 可判定性 | 类型检查可自动化 | THEOREM_INTUITIONS 第 5 章 |
| 借用检查等价性 | 编译时 = 运行时 | THEOREM_INTUITIONS 第 6 章 |
| 内存安全 | 无内存错误 | THEOREM_INTUITIONS 第 7 章 |

### 核心概念速查

| 概念 | 一句话解释 | 详细位置 |
|------|-----------|---------|
| 所有权 | 独占访问权 | OVERVIEW 第 2.1 节 |
| 借用 | 临时访问权 | OVERVIEW 第 2.1 节 |
| 生命周期 | 访问有效期 | OVERVIEW 第 2.2 节 |
| Linearizability | 类型依赖无环 | OVERVIEW 第 3.3 节 |
| 类型秩 | 类型复杂度 | OVERVIEW 第 3.3 节 |

### 证明技巧速查

| 技巧 | 适用场景 | 详细位置 |
|------|---------|---------|
| 结构归纳 | 语法结构 | PROOF_STRATEGIES 第 1.1 节 |
| 良基归纳 | 需要度量 | PROOF_STRATEGIES 第 1.2 节 |
| 反证法 | 证明不可能 | PROOF_STRATEGIES 第 1.3 节 |
| 构造性证明 | 展示存在 | PROOF_STRATEGIES 第 1.4 节 |

---

## 贡献指南

### 如何改进自然语言文档

1. **发现错误**：提交 issue 或 PR
2. **内容不清**：指出具体段落，建议改进
3. **缺少内容**：建议添加新章节
4. **翻译**：翻译成其他语言

### 文档维护原则

- **准确性**：数学内容必须准确
- **可理解性**：使用类比和例子
- **完整性**：覆盖所有核心概念
- **一致性**：术语使用一致

---

## 版本历史

### v1.0（2026-03-11）

- 初始版本
- 创建 7 个自然语言文档
- 完成核心理论论证

---

## 联系与反馈

如果你：

- 发现文档中的错误
- 对某些概念仍不理解
- 希望添加新内容
- 想参与贡献

请通过项目的 issue 系统提交反馈。

---

**开始探索**：建议从 `OVERVIEW_AND_INTUITION.md` 开始阅读！
