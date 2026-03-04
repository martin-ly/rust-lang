# Rust形式化验证工具全景

> **综合参考**: 2024年Rust形式化验证工具生态综述

## 目录

- [Rust形式化验证工具全景](#rust形式化验证工具全景)
  - [目录](#目录)
  - [1. 验证工具谱系图](#1-验证工具谱系图)
  - [2. 工具对比矩阵](#2-工具对比矩阵)
  - [3. 各工具核心特性](#3-各工具核心特性)
    - [3.1 Creusot](#31-creusot)
    - [3.2 Prusti](#32-prusti)
    - [3.3 RustHorn](#33-rusthorn)
    - [3.4 Verus](#34-verus)
    - [3.5 Kani](#35-kani)
  - [4. 方法学对比](#4-方法学对比)
    - [4.1 内存建模方法](#41-内存建模方法)
    - [4.2 证明自动化](#42-证明自动化)
  - [5. 实践选择指南](#5-实践选择指南)
    - [5.1 场景匹配](#51-场景匹配)
    - [5.2 成熟度评估](#52-成熟度评估)
  - [6. 验证工具与编译器集成](#6-验证工具与编译器集成)
  - [参考文献](#参考文献)

## 1. 验证工具谱系图

```text
┌─────────────────────────────────────────────────────────────────────────────┐
│                      Rust形式化验证工具分类                                   │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                             │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                    演绎验证 (Deductive Verification)                 │   │
│  │  基于Hoare逻辑，生成证明义务，需要用户指导证明                        │   │
│  ├─────────────────────────────────────────────────────────────────────┤   │
│  │  Creusot (Why3)  │  Prusti (Viper)  │  RustHorn (CHC)  │  Aeneas    │   │
│  │  Paris-Saclay    │  ETH Zurich      │  东京大学        │  Inria     │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    │                                        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                    模型检测 (Model Checking)                         │   │
│  │  状态空间遍历，自动化程度高，但有状态爆炸限制                        │   │
│  ├─────────────────────────────────────────────────────────────────────┤   │
│  │  Kani (CBMC)     │  MIRAI           │  SMACK           │            │   │
│  │  Amazon          │  Meta            │  UT Austin       │            │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                    │                                        │
│  ┌─────────────────────────────────────────────────────────────────────┐   │
│  │                    基础形式化 (Foundational)                         │   │
│  │  机器检查证明，最高保证级别                                          │   │
│  ├─────────────────────────────────────────────────────────────────────┤   │
│  │  RustBelt (Coq)  │  Verus           │  RefinedC        │            │   │
│  │  MPI-SWS         │  CMU/VMware      │  MPI-SWS         │            │   │
│  └─────────────────────────────────────────────────────────────────────┘   │
│                                                                             │
└─────────────────────────────────────────────────────────────────────────────┘
```

## 2. 工具对比矩阵

| 工具 | 机构 | 方法 | 自动化 | 覆盖范围 | 成熟度 |
|------|------|------|--------|----------|--------|
| **Creusot** | LMF, Paris-Saclay | Why3, 预言变量 | 高 | Safe Rust | ⭐⭐⭐⭐ |
| **Prusti** | ETH Zurich | Viper, 分离逻辑 | 高 | Safe Rust | ⭐⭐⭐⭐ |
| **RustHorn** | 东京大学 | CHC编码 | 高 | Safe Rust子集 | ⭐⭐⭐ |
| **Aeneas** | Inria | 函数式提取 | 中 | Safe Rust | ⭐⭐⭐ |
| **Verus** | CMU/VMware | Z3, 资源代数 | 高 | Safe + 部分Unsafe | ⭐⭐⭐⭐ |
| **Kani** | Amazon | CBMC | 自动 | Unsafe支持 | ⭐⭐⭐⭐ |
| **RustBelt** | MPI-SWS | Coq, Iris | 手动 | 核心语言 | ⭐⭐⭐⭐⭐ |

## 3. 各工具核心特性

### 3.1 Creusot

```rust
// Creusot示例: 预言变量
#[requires(true)]
#[ensures(result >= 0)]
fn abs(x: i32) -> i32 {
    if x >= 0 { x } else { -x }
}

// 规格说明使用Why3的逻辑
// 预言变量处理可变借用
```

**特点**:

- 基于**预言变量** (Prophecy Variables) 建模可变借用
- 利用Rust traits进行抽象
- 生成Why3证明义务

### 3.2 Prusti

```rust
// Prusti示例: 前置/后置条件
#[requires(x >= 0)]
#[ensures(result >= x)]
fn increment(x: i32) -> i32 {
    x + 1
}

// 支持loop invariants
#[invariant(i >= 0)]
while i < n {
    // ...
}
```

**特点**:

- 基于**Viper**验证基础设施
- 使用**分离逻辑**处理内存
- 支持纯函数和可变状态

### 3.3 RustHorn

```rust
// RustHorn: 自动生成CHC
fn max(x: i32, y: i32) -> i32 {
    if x > y { x } else { y }
}

// 验证条件:
// (x > y => result = x) ∧ (x ≤ y => result = y)
```

**特点**:

- 将Rust程序转换为**约束Horn子句** (CHC)
- 利用所有权简化内存建模
- 完全自动化验证

### 3.4 Verus

```rust
// Verus示例: 系统验证
use vstd::prelude::*;

verus! {
    fn binary_search(v: &Vec<u64>, x: u64) -> (r: usize)
        requires
            forall|i: int, j: int| 0 <= i <= j < v.len()
                ==> v[i] <= v[j],  // 已排序
        ensures
            r < v.len() ==> v[r] == x,
    {
        // 实现
    }
}
```

**特点**:

- 针对**系统代码**设计
- **资源代数**支持并发
- Z3后端自动化证明

### 3.5 Kani

```rust
// Kani: 有界模型检测
#[kani::proof]
fn check_abs() {
    let x: i32 = kani::any();  // 非确定性输入
    let r = abs(x);
    assert!(r >= 0);
}
```

**特点**:

- 基于**CBMC** (C Bounded Model Checker)
- 支持**Unsafe Rust**
- 适合检查特定属性

## 4. 方法学对比

### 4.1 内存建模方法

| 工具 | 内存模型 | 可变借用处理 |
|------|---------|-------------|
| Creusot | 预言变量 | 预言编码 |
| Prusti | 分离逻辑 | 分数权限 |
| RustHorn | CHC编码 | 预言编码 |
| Aeneas | 函数式提取 | 纯函数 |
| Verus | SMT数组 | 资源代数 |

### 4.2 证明自动化

```text
自动化程度谱系:

手动 ←────────────────────────────────→ 全自动
│                                      │
├─ RustBelt (Coq)                      │
│  完全手动，机器检查                  │
├─ Aeneas (Lean)                       │
│  提取后手动证明                      │
├─ Verus                               │
│  SMT自动化，可能需要辅助             │
├─ Prusti/Creusot/RustHorn             │
│  高度自动化                          │
└─ Kani                                │
   全自动但有界                        │
```

## 5. 实践选择指南

### 5.1 场景匹配

```text
┌────────────────────────────────────────────────────────────────┐
│                      工具选择决策树                             │
├────────────────────────────────────────────────────────────────┤
│                                                                │
│  需要机器检查证明？                                             │
│       ├── 是 → RustBelt / Aeneas / RefinedC                   │
│       └── 否 →                                                 │
│             使用Unsafe代码？                                   │
│             ├── 是 → Kani / RustBelt                          │
│             └── 否 →                                           │
│                   验证并发？                                   │
│                   ├── 是 → Verus / RustBelt                   │
│                   └── 否 →                                     │
│                         全自动优先？                           │
│                         ├── 是 → Creusot / RustHorn           │
│                         └── 否 → Prusti / Verus               │
│                                                                │
└────────────────────────────────────────────────────────────────┘
```

### 5.2 成熟度评估

| 工具 | 标准库覆盖率 | 文档 | 社区 | 持续维护 |
|------|-------------|------|------|---------|
| Creusot | 良好 | 优秀 | 活跃 | 是 |
| Prusti | 良好 | 优秀 | 活跃 | 是 |
| RustHorn | 有限 | 一般 | 较少 | 是 |
| Verus | 良好 | 优秀 | 活跃 | 是 |
| Kani | 良好 | 优秀 | 活跃 | 是 |
| RustBelt | 核心语言 | 研究级 | 学术 | 是 |

## 6. 验证工具与编译器集成

```text
集成架构:

Rust源码
    ↓
rustc 解析/类型检查
    ↓
HIR (高级IR)
    ↓    ┌─────────────┬─────────────┬─────────────┐
    ↓    │             │             │             │
    ↓    ▼             ▼             ▼             ▼
   MIR ──────▶ Creusot  Prusti   RustHorn   Verus
    │         (Why3)   (Viper)   (CHC)      (Z3)
    │
    └─────────▶ Kani (CBMC)

    HIR ──────▶ Aeneas (LLBC提取)
```

---

## 参考文献

1. Denis, X., et al. (2022). Creusot: A Foundry for the Deductive Verification of Rust Programs. *ICFEM*.
2. Astrauskas, V., et al. (2022). The Prusti Project: Formal Verification for Rust. *NSV*.
3. Matsushita, Y., et al. (2021). RustHorn: CHC-based Verification for Rust Programs. *TOPLAS*.
4. Lattuada, A., et al. (2024). Aeneas: Rust Verification by Functional Translation. *ICFP*.
5. Lorch, J.R., et al. (2024). Verus: A Practical Foundation for Systems Verification. *SOSP*.
