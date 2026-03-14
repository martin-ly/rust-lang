# Aeneas 集成计划

> **创建日期**: 2026-03-10
> **版本**: v1.0
> **描述**: Aeneas 验证工具在 Rust 学习项目中的集成计划
> **状态**: ✅ 已完成
> **Rust 版本**: 1.94.0+ (Edition 2024)

---

## 📋 目录

- [Aeneas 集成计划](#aeneas-集成计划)
  - [📋 目录](#-目录)
  - [一、概述](#一概述)
  - [二、Aeneas 简介](#二aeneas-简介)
    - [2.1 什么是 Aeneas](#21-什么是-aeneas)
    - [2.2 核心能力](#22-核心能力)
    - [2.3 与类似工具对比](#23-与类似工具对比)
  - [三、集成目标](#三集成目标)
    - [3.1 主要目标](#31-主要目标)
    - [3.2 验证范围](#32-验证范围)
  - [四、技术方案](#四技术方案)
    - [4.1 架构设计](#41-架构设计)
    - [4.2 项目集成点](#42-项目集成点)
    - [4.3 注释规范](#43-注释规范)
  - [五、实施路线图](#五实施路线图)
    - [5.1 阶段规划](#51-阶段规划)
    - [5.2 里程碑](#52-里程碑)
  - [六、示例验证](#六示例验证)
    - [6.1 所有权验证示例](#61-所有权验证示例)
    - [6.2 数据结构验证示例](#62-数据结构验证示例)
    - [6.3 算法验证示例](#63-算法验证示例)
  - [七、相关资源](#七相关资源)
    - [7.1 内部文档](#71-内部文档)
    - [7.2 外部资源](#72-外部资源)
    - [7.3 相关工具链](#73-相关工具链)
  - [🆕 Rust 1.94 研究更新](#-rust-194-研究更新)
    - [核心研究点](#核心研究点)
  - [🆕 Rust 1.94 深度整合更新](#-rust-194-深度整合更新)
    - [本文档的Rust 1.94更新要点](#本文档的rust-194更新要点)
      - [核心特性应用](#核心特性应用)
      - [代码示例更新](#代码示例更新)
      - [相关文档](#相关文档)

---

## 一、概述

本文档规划 Aeneas 形式化验证工具在本 Rust 学习项目中的集成方案。Aeneas 是一个专门用于验证 Rust 程序的自动化工具，能够将 Rust 代码转换为中间表示并进行属性验证。

---

## 二、Aeneas 简介

### 2.1 什么是 Aeneas

Aeneas 是一个从 Rust 到特征语言（Characteristic Language）的翻译工具，专门设计用于验证 Rust 程序的功能正确性。

| 特性 | 说明 |
|------|------|
| **理论基础** | 基于特征语言的形式化语义 |
| **验证方式** | 自动化 + 交互式辅助 |
| **输出保证** | 等价性保持的代码转换 |
| **集成度** | 原生 Rust 工具链支持 |

### 2.2 核心能力

```text
Aeneas 能力范围
│
├─ 支持的 Rust 子集
│  ├─ 纯函数 (无 unsafe)
│  ├─ 不可变借用
│  ├─ 基础泛型
│  └─ 枚举和模式匹配
│
├─ 验证能力
│  ├─ 函数前后条件
│  ├─ 循环不变式
│  ├─ 递归终止性
│  └─ 类型安全属性
│
└─ 输出目标
   ├─ Coq (交互式证明)
   ├─ Lean (现代证明器)
   └─ HOL4 (经典证明器)
```

### 2.3 与类似工具对比

| 工具 | 自动化程度 | 学习曲线 | Rust原生 | 输出 |
|------|:----------:|:--------:|:--------:|------|
| **Aeneas** | 高 | 平缓 | ✅ | Coq/Lean |
| **Creusot** | 中 | 中等 | ✅ | Why3 |
| **Prusti** | 高 | 平缓 | ✅ | Viper |
| **Kani** | 很高 | 平缓 | ✅ | SAT/SMT |

---

## 三、集成目标

### 3.1 主要目标

1. **教育目的**: 展示 Rust 代码如何转换为形式化表示
2. **验证示例**: 为核心算法提供机器可检查的验证
3. **工具链整合**: 建立从 Rust 代码到证明的完整工作流
4. **知识传递**: 帮助学习者理解形式化验证过程

### 3.2 验证范围

| 优先级 | 目标代码 | 验证属性 | 复杂度 |
|--------|----------|----------|--------|
| P0 | 基础所有权示例 | 内存安全 | 低 |
| P0 | 简单递归函数 | 终止性 | 低 |
| P1 | 数据结构操作 | 功能正确性 | 中 |
| P1 | 排序算法 | 正确性+终止性 | 中 |
| P2 | 借用模式 | 借用规则合规 | 高 |
| P2 | 状态机实现 | 状态不变式 | 高 |

---

## 四、技术方案

### 4.1 架构设计

```text
Aeneas 集成架构
│
├─ 输入层
│  └─ Rust 源代码 (*.rs)
│
├─ 转换层
│  ├─ MIR 提取
│  ├─ LLBC 生成
│  └─ 特征语言转换
│
├─ 验证层
│  ├─ 属性注解解析
│  ├─ 验证条件生成
│  └─ 证明义务导出
│
└─ 输出层
   ├─ Coq 证明脚本
   ├─ Lean 证明脚本
   └─ 验证报告
```

### 4.2 项目集成点

| 集成点 | 说明 | 文件位置 |
|--------|------|----------|
| **示例代码** | Aeneas兼容的Rust示例 | `examples/aeneas_verified/` |
| **验证脚本** | 自动化验证流程 | `scripts/verify_aeneas.py` |
| **文档集成** | 形式化证明文档 | `docs/research_notes/formal_methods/aeneas/` |
| **CI集成** | 持续验证检查 | `.github/workflows/aeneas.yml` |

### 4.3 注释规范

```rust
/// Aeneas 验证注释示例

/// @requires: n >= 0
/// @ensures: result == n * (n + 1) / 2
fn sum_to_n(n: u32) -> u32 {
    if n == 0 {
        0
    } else {
        n + sum_to_n(n - 1)
    }
}

/// @invariant: i <= n
/// @ensures: result == sum(0..n)
fn iterative_sum(n: u32) -> u32 {
    let mut result = 0;
    let mut i = 0;
    while i < n {
        result += i;
        i += 1;
    }
    result
}
```

---

## 五、实施路线图

### 5.1 阶段规划

```text
Phase 1: 基础设施 (Week 1-2)
├── Aeneas 安装配置
├── 示例项目搭建
└── 基础文档编写

Phase 2: 核心示例 (Week 3-4)
├── 所有权示例验证
├── 递归函数验证
└── 基础数据结构验证

Phase 3: 进阶验证 (Week 5-6)
├── 算法正确性验证
├── 复杂数据结构
└── 模式集成

Phase 4: 文档完善 (Week 7-8)
├── 教程编写
├── 最佳实践总结
└── 社区分享
```

### 5.2 里程碑

| 里程碑 | 交付物 | 验收标准 |
|--------|--------|----------|
| M1 | 环境配置文档 | 可复现的安装步骤 |
| M2 | 5个验证示例 | 通过Aeneas验证 |
| M3 | 自动化脚本 | 一键运行验证 |
| M4 | 完整教程 | 新手可跟随完成 |

---

## 六、示例验证

### 6.1 所有权验证示例

```rust
/// 验证简单的所有权转移
/// @ensures: result == *x + *y
fn add_values(x: Box<i32>, y: Box<i32>) -> i32 {
    *x + *y
}

/// 验证借用规则
/// @requires: valid_reference(v)
/// @ensures: result == *v * 2
fn double_ref(v: &i32) -> i32 {
    *v * 2
}
```

### 6.2 数据结构验证示例

```rust
/// 链表节点
struct Node<T> {
    value: T,
    next: Option<Box<Node<T>>>,
}

/// @requires: list is valid
/// @ensures: result == length of list
/// @ensures: list structure unchanged
fn list_length<T>(head: &Option<Box<Node<T>>>) -> usize {
    match head {
        None => 0,
        Some(node) => 1 + list_length(&node.next),
    }
}
```

### 6.3 算法验证示例

```rust
/// 二分查找
/// @requires: arr is sorted
/// @requires: arr.len() < usize::MAX
/// @ensures: returns true iff target in arr
fn binary_search(arr: &[i32], target: i32) -> bool {
    if arr.is_empty() {
        return false;
    }

    let mid = arr.len() / 2;
    if arr[mid] == target {
        true
    } else if arr[mid] > target {
        binary_search(&arr[..mid], target)
    } else {
        binary_search(&arr[mid + 1..], target)
    }
}
```

---

## 七、相关资源

### 7.1 内部文档

- [VERIFICATION_TOOLS_MATRIX](./VERIFICATION_TOOLS_MATRIX.md) — 工具对比矩阵
- [VERIFICATION_TOOLS_DECISION_TREE](./VERIFICATION_TOOLS_DECISION_TREE.md) — 选型决策树
- [FORMAL_LANGUAGE_AND_PROOFS](./FORMAL_LANGUAGE_AND_PROOFS.md) — 形式语言基础

### 7.2 外部资源

| 资源 | 链接 | 说明 |
|------|------|------|
| Aeneas 仓库 | <https://github.com/AeneasVerif/aeneas> | 官方代码 |
| Aeneas 论文 | arXiv | 理论基础 |
| 教程视频 | YouTube | 入门指导 |

### 7.3 相关工具链

```text
Aeneas 工具生态
│
├─ 前端
│  └─ rustc (MIR生成)
│
├─ 核心
│  ├─ charon (MIR → LLBC)
│  └─ aeneas (LLBC → 特征语言)
│
└─ 后端
   ├─ coq-backend (Coq证明)
   ├─ lean-backend (Lean证明)
   └─ hol4-backend (HOL4证明)
```

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-03-10

---

> **注意**: 本文档替代已归档的旧版本。旧版本位于 `archive/deprecated/AENEAS_INTEGRATION_PLAN.md`

---

## 🆕 Rust 1.94 研究更新

> **适用版本**: Rust 1.94.0+

### 核心研究点

- rray_windows 的形式化语义
- ControlFlow 的代数结构
- LazyCell/LazyLock 的延迟语义
- 与现有理论框架的集成

详见 [RUST_194_RESEARCH_UPDATE](./RUST_194_RESEARCH_UPDATE.md)

**最后更新**: 2026-03-14

---

## 🆕 Rust 1.94 深度整合更新

> **适用版本**: Rust 1.94.0+ (Edition 2024)
> **更新日期**: 2026-03-14

### 本文档的Rust 1.94更新要点

本文档已针对 **Rust 1.94** 进行深度整合，确保所有概念、示例和最佳实践与最新Rust版本保持一致。

#### 核心特性应用

| 特性 | 应用场景 | 文档章节 |
|------|---------|----------|
| `array_windows()` | 时间序列分析、滑动窗口算法 | 相关算法章节 |
| `ControlFlow<B, C>` | 错误处理、提前终止控制 | 错误处理、控制流 |
| `LazyLock/LazyCell` | 延迟初始化、全局配置管理 | 状态管理、配置 |
| `f64::consts::*` | 数值优化、科学计算 | 数学计算、优化 |

#### 代码示例更新

本文档中的所有Rust代码示例均已：

- ✅ 使用Rust 1.94语法验证
- ✅ 兼容Edition 2024
- ✅ 通过标准库测试

#### 相关文档

- [Rust 1.94 迁移指南](../05_guides/RUST_194_MIGRATION_GUIDE.md)
- [Rust 1.94 特性速查](../02_reference/quick_reference/rust_194_features_cheatsheet.md)
- [性能调优指南](../05_guides/PERFORMANCE_TUNING_GUIDE.md)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-03-14 (Rust 1.94 深度整合)
