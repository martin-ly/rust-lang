# 验证工具对比矩阵

> **创建日期**: 2026-03-10
> **版本**: v1.0
> **描述**: Rust 形式化验证工具全面对比矩阵
> **状态**: ✅ 已完成

---

## 📋 目录

- [验证工具对比矩阵](#验证工具对比矩阵)
  - [📋 目录](#-目录)
  - [一、概述](#一概述)
  - [二、工具总览](#二工具总览)
    - [2.1 工具分类](#21-工具分类)
  - [三、详细对比矩阵](#三详细对比矩阵)
    - [3.1 核心能力矩阵](#31-核心能力矩阵)
    - [3.2 技术特性矩阵](#32-技术特性矩阵)
    - [3.3 性能与可扩展性](#33-性能与可扩展性)
  - [四、能力评估](#四能力评估)
    - [4.1 验证深度评估](#41-验证深度评估)
    - [4.2 适用场景矩阵](#42-适用场景矩阵)
  - [五、选型建议](#五选型建议)
    - [5.1 决策流程图](#51-决策流程图)
    - [5.2 组合使用策略](#52-组合使用策略)
  - [六、相关资源](#六相关资源)
    - [6.1 内部文档](#61-内部文档)
    - [6.2 外部资源](#62-外部资源)
    - [6.3 工具生态图](#63-工具生态图)

---

## 一、概述

本文档提供 Rust 形式化验证工具的全面对比，包括交互式定理证明器、自动化验证工具、模型检查器等。
帮助开发者根据项目需求选择合适的验证工具。

---

## 二、工具总览

### 2.1 工具分类

| 类别 | 代表工具 | 自动化程度 | 学习曲线 |
|------|----------|------------|----------|
| **交互式定理证明** | Coq, Isabelle, Lean | 低 | 陡峭 |
| **半自动化验证** | Aeneas, F*, Creusot | 中 | 中等 |
| **模型检查** | Kani, Prusti, MIRAI | 高 | 平缓 |
| **类型系统验证** | RustBelt, RustHorn | 中 | 陡峭 |
| **符号执行** | KLEE (Rust), SMACK | 高 | 中等 |

---

## 三、详细对比矩阵

### 3.1 核心能力矩阵

| 工具 | 所有权验证 | 并发验证 | 终止性 | 安全性 | 活性 | Rust原生 |
|------|:----------:|:--------:|:------:|:------:|:----:|:--------:|
| **Coq** | ✅ | ✅ | ✅ | ✅ | ✅ | ❌ |
| **Isabelle** | ✅ | ✅ | ✅ | ✅ | ✅ | ❌ |
| **Lean** | ✅ | ✅ | ✅ | ✅ | ✅ | ❌ |
| **Aeneas** | ✅ | ⚠️ | ✅ | ✅ | ❌ | ✅ |
| **Creusot** | ✅ | ⚠️ | ✅ | ✅ | ⚠️ | ✅ |
| **Prusti** | ✅ | ⚠️ | ✅ | ✅ | ❌ | ✅ |
| **Kani** | ✅ | ✅ | ✅ | ✅ | ❌ | ✅ |
| **MIRAI** | ✅ | ❌ | ❌ | ✅ | ❌ | ✅ |
| **RustBelt** | ✅ | ✅ | ✅ | ✅ | ✅ | ⚠️ |
| **F*** | ✅ | ✅ | ✅ | ✅ | ✅ | ⚠️ |

*✅ 完全支持 | ⚠️ 部分支持 | ❌ 不支持*:

### 3.2 技术特性矩阵

| 工具 | 基础理论 | 验证方式 | 输出保证 | 工具链集成 |
|------|----------|----------|----------|------------|
| **Coq** | 归纳构造演算 | 交互式 | 数学证明 | 一般 |
| **Isabelle** | 高阶逻辑 | 交互式 | 数学证明 | 一般 |
| **Lean** | 依赖类型 | 交互式 | 数学证明 | 良好 |
| **Aeneas** | 特征语言 | 半自动 | 等价转换 | 优秀 |
| **Creusot** | 谓词变换 | 契约驱动 | 模块化证明 | 优秀 |
| **Prusti** | Viper框架 | 契约驱动 | 自动验证 | 优秀 |
| **Kani** | CBMC | 模型检查 | 反例/成功 | 优秀 |
| **MIRAI** | 抽象解释 | 静态分析 | 警告/确认 | 优秀 |
| **RustBelt** | Iris逻辑 | 交互式 | 逻辑关系 | 一般 |
| **F*** | 依赖类型 | 混合式 | 数学证明 | 良好 |

### 3.3 性能与可扩展性

| 工具 | 验证速度 | 代码覆盖 | 大型项目 | 学习资源 |
|------|----------|----------|----------|----------|
| **Coq** | 慢 | 完整 | 困难 | 丰富 |
| **Isabelle** | 慢 | 完整 | 困难 | 丰富 |
| **Lean** | 中等 | 完整 | 中等 | 增长中 |
| **Aeneas** | 快 | 高 | 良好 | 有限 |
| **Creusot** | 快 | 高 | 良好 | 有限 |
| **Prusti** | 中等 | 高 | 中等 | 中等 |
| **Kani** | 中等 | 中等 | 中等 | 增长中 |
| **MIRAI** | 很快 | 中等 | 优秀 | 有限 |
| **RustBelt** | 慢 | 完整 | 困难 | 学术 |
| **F*** | 中等 | 完整 | 中等 | 中等 |

---

## 四、能力评估

### 4.1 验证深度评估

```text
验证深度
│
├─ 数学级保证
│  ├─ Coq (Gallina + SSReflect)
│  ├─ Isabelle/HOL
│  ├─ Lean 4
│  └─ RustBelt (Iris)
│
├─ 程序逻辑级
│  ├─ Creusot (Why3)
│  ├─ Prusti (Viper)
│  └─ F* (低层次)
│
├─ 模型检查级
│  ├─ Kani (CBMC)
│  └─ Aeneas (特征提取)
│
└─ 静态分析级
   └─ MIRAI
```

### 4.2 适用场景矩阵

| 场景 | 推荐工具 | 替代方案 |
|------|----------|----------|
| 学术研究 | Coq, Isabelle | Lean |
| 工业验证 | Creusot, Prusti | Kani |
| 快速检查 | MIRAI | Kani |
| 并发验证 | RustBelt | Kani |
| 教学使用 | Aeneas | Lean |
| 安全关键 | Coq + RustBelt | Isabelle |

---

## 五、选型建议

### 5.1 决策流程图

```text
项目需求分析
│
├─ 需要数学级保证？
│  ├─ 是 → 团队有形式化经验？
│  │     ├─ 是 → Coq / Isabelle / Lean
│  │     └─ 否 → 培训或外包
│  └─ 否 → 继续
│
├─ 需要Rust原生集成？
│  ├─ 是 → 验证深度要求？
│  │     ├─ 高 → Creusot / Prusti
│  │     ├─ 中 → Kani
│  │     └─ 低 → MIRAI
│  └─ 否 → 通用工具如Coq
│
└─ 时间和资源限制？
   ├─ 紧张 → MIRAI / Kani
   └─ 充裕 → Creusot / Coq
```

### 5.2 组合使用策略

| 层级 | 工具 | 目的 |
|------|------|------|
| L1 (快速检查) | MIRAI | 日常开发快速验证 |
| L2 (深度验证) | Kani / Creusot | 关键代码验证 |
| L3 (形式证明) | Coq / Isabelle | 核心库数学保证 |

---

## 六、相关资源

### 6.1 内部文档

- [AENEAS_INTEGRATION_PLAN](./AENEAS_INTEGRATION_PLAN.md) — Aeneas集成
- [COQ_ISABELLE_PROOF_SCAFFOLDING](./COQ_ISABELLE_PROOF_SCAFFOLDING.md) — Coq/Isabelle脚手架
- [VERIFICATION_TOOLS_DECISION_TREE](./VERIFICATION_TOOLS_DECISION_TREE.md) — 选型决策树

### 6.2 外部资源

| 工具 | 官方链接 | 文档 |
|------|----------|------|
| Coq | <https://coq.inria.fr> | 优秀 |
| Isabelle | <https://isabelle.in.tum.de> | 优秀 |
| Lean | <https://lean-lang.org> | 良好 |
| Aeneas | <https://github.com/AeneasVerif/aeneas> | 中等 |
| Creusot | <https://github.com/creusot-rs/creusot> | 中等 |
| Prusti | <https://www.pm.inf.ethz.ch/research/prusti.html> | 良好 |
| Kani | <https://model-checking.github.io/kani/> | 良好 |
| MIRAI | <https://github.com/facebookexperimental/MIRAI> | 有限 |

### 6.3 工具生态图

```text
Rust 验证生态系统
│
├─ 学术工具链
│  ├─ RustBelt (Iris逻辑)
│  ├─ RustHorn (CHC求解)
│  └─ Oxide (别名类型)
│
├─ 工业工具链
│  ├─ Creusot (Why3)
│  ├─ Prusti (Viper)
│  └─ Kani (CBMC)
│
├─ 分析工具
│  ├─ MIRAI (抽象解释)
│  ├─ Rudra (Unsafe分析)
│  └─ Lockbud (死锁检测)
│
└─ 转换工具
   ├─ Aeneas (LLBC)
   ├─ hacspec (规范语言)
   └─ coq-of-rust (Coq转换)
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-03-10
