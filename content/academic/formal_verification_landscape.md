# Rust 形式化验证工具全景

> **定位**: Rust 生态中主要形式化验证工具的系统性对比与选型指南
> **覆盖**: Prusti、Kani、Miri、RustBelt 及其理论基础
> **适用**: 安全关键系统开发、算法正确性证明、学术研究
> **前置阅读**: [Prusti 验证教程](./prusti_verification_tutorial.md)

---

## 📋 目录

- [Rust 形式化验证工具全景](#rust-形式化验证工具全景)
  - [📋 目录](#-目录)
  - [🎯 概述](#-概述)
  - [🔬 工具深度解析](#-工具深度解析)
    - [Prusti (ETH Zürich / Viper)](#prusti-eth-zürich--viper)
    - [Kani (AWS / CBMC)](#kani-aws--cbmc)
    - [Miri (Rust 官方 / 内存模型)](#miri-rust-官方--内存模型)
    - [RustBelt (MPI-SWS / Iris)](#rustbelt-mpi-sws--iris)
  - [📊 适用场景对比矩阵](#-适用场景对比矩阵)
  - [🔄 工具协作工作流](#-工具协作工作流)
  - [🎓 学术研究路径推荐](#-学术研究路径推荐)
    - [工程师入门路径](#工程师入门路径)
    - [研究者深入路径](#研究者深入路径)
  - [🔗 参考资源](#-参考资源)
    - [官方文档](#官方文档)
    - [学术论文](#学术论文)
    - [教程与课程](#教程与课程)
  - [**状态**: ✅ 已完善](#状态--已完善)

---

## 🎯 概述

Rust 的所有权和类型系统已经排除了大量运行时错误，但**逻辑错误**（如越界索引、算术溢出、算法缺陷）仍需额外验证。形式化验证工具在 Rust 编译器的保证之上，提供数学级别的正确性证明：

```text
验证层级金字塔:
                    ┌─────────┐
                    │ 逻辑正确 │ ← Prusti / Kani 证明
                    ├─────────┤
                    │ 内存安全 │ ← Rust 编译器保证
                    ├─────────┤
                    │ 类型安全 │ ← Rust 类型系统
                    ├─────────┤
                    │ UB 自由  │ ← Miri 检测
                    └─────────┘

基础理论支撑:
├─ Prusti → Viper 中间语言 → Z3 SMT 求解器
├─ Kani → CBMC → SAT/SMT 模型检测
├─ Miri → Stacked/Tree Borrows → 操作语义解释器
└─ RustBelt → Iris 分离逻辑 → Rocq 证明助手
```

---

## 🔬 工具深度解析

### Prusti (ETH Zürich / Viper)

**核心定位**: 基于契约的演绎验证器（Deductive Verifier）

```rust
use prusti_contracts::*;

/// 二分查找 — 附带完整规范
#[requires(array.len() <= 1000)]
#[requires(
    forall(|i: usize, j: usize|
        (0 <= i && i < j && j < array.len())
        ==> array[i] <= array[j]
    )
)]
#[ensures(
    result == None
    ==> forall(|i: usize|
        (0 <= i && i < array.len())
        ==> array[i] != target
    )
)]
#[ensures(
    result == Some(idx)
    ==> (0 <= idx && idx < array.len() && array[idx] == target)
)]
pub fn binary_search(array: &[i32], target: i32) -> Option<usize> {
    let mut left = 0;
    let mut right = array.len();

    while left < right {
        body_invariant!(left <= right);
        body_invariant!(right <= array.len());
        body_invariant!(
            forall(|i: usize|
                (0 <= i && i < left) ==> array[i] < target
            )
        );

        let mid = left + (right - left) / 2;

        if array[mid] == target {
            return Some(mid);
        } else if array[mid] < target {
            left = mid + 1;
        } else {
            right = mid;
        }
    }

    None
}
```

**技术栈**:

| 组件 | 作用 |
|------|------|
| Rust 源码 | 输入程序 + `prusti_contracts` 规范 |
| VIR | Viper 中间表示（简化 Rust 语义） |
| Silver | Viper 验证语言 |
| Z3 | SMT 求解器（自动证明） |

**优势**: 可证明功能正确性、支持复杂不变量、生成数学级保证
**限制**: 需手写规范、不支持 `unsafe`、并发支持有限

### Kani (AWS / CBMC)

**核心定位**: 基于模型检测的自动化验证器（Model Checker）

```rust
// 无需规范注解，使用任意输入遍历所有路径
#[cfg(kani)]
mod verification {
    #[kani::proof]
    fn verify_abs_correctness() {
        let x: i32 = kani::any();  // 符号化任意值

        let result = super::abs(x);

        // 验证后置条件对所有输入成立
        kani::assert(result >= 0);
        if x != i32::MIN {
            kani::assert(result == x || result == -x);
        }
    }
}

fn abs(x: i32) -> i32 {
    if x < 0 { -x } else { x }
}
```

**技术栈**:

| 组件 | 作用 |
|------|------|
| Rust MIR | 编译器中间表示 |
| CBMC | C 模型检测器后端 |
| SAT/SMT | 可满足性求解 |

**优势**: 零注解验证、自动路径遍历、支持 `unsafe` 子集
**限制**: 状态空间爆炸（需限制输入范围）、循环需展开界限

### Miri (Rust 官方 / 内存模型)

**核心定位**: 未定义行为（UB）检测的解释执行引擎

```bash
# 运行 Miri 检测 UB
cargo miri test

# 使用 Tree Borrows 别名模型
MIRIFLAGS="-Zmiri-tree-borrows" cargo miri test

# 检测数据竞争
MIRIFLAGS="-Zmiri-disable-isolation" cargo miri test
```

```rust
// Miri 可检测的 UB 示例
fn dangling_pointer() {
    let ptr: *const i32;
    {
        let x = 42;
        ptr = &x;  // 借用局部变量
    }            // x 在这里 drop
    // ❌ Miri 报错: 使用已释放内存
    unsafe { println!("{}", *ptr); }
}

fn aliasing_violation() {
    let mut x = 5;
    let r1 = &mut x;
    let r2 = &mut x;  // ❌ Miri 报错: 重叠可变引用
    *r1 = 1;
    *r2 = 2;
}
```

**技术栈**:

| 组件 | 作用 |
|------|------|
| Miri 引擎 | Rust MIR 解释器 |
| Stacked Borrows | 默认别名模型 |
| Tree Borrows | 实验性宽松别名模型 |
| Data Race Detector | 线程间数据竞争检测 |

**优势**: 零配置、检测真实 UB、集成测试工作流
**限制**: 仅覆盖单条执行路径、极慢（解释执行）、不证明正确性

### RustBelt (MPI-SWS / Iris)

**核心定位**: Rust 内存安全保证的**数学证明**（非工具）

```text
RustBelt 理论框架:
┌─────────────────────────────────────────┐
│  Iris 分离逻辑 (Higher-Order)           │
│    ├─ 点态断言: l ↦ v                    │
│    ├─ 独占所有权: ∃v. l ↦ v ∗ (l ↦ - ∗ ⊥)│
│    └─ 共享借用: □(l ↦□ v)                │
├─────────────────────────────────────────┤
│  Rust 类型 → 逻辑断言映射                  │
│    ├─ &mut T → 独占权限                   │
│    ├─ &T     → 共享/只读权限              │
│    └─ Box<T> → 堆所有权                   │
├─────────────────────────────────────────┤
│  定理: 类型安全 ⇒ 无数据竞争               │
│    ├─ 所有权唯一性 → 无别名写入            │
│    ├─ 借用规则   → 无悬垂引用             │
│    └─ Send/Sync  → 线程安全              │
└─────────────────────────────────────────┘
```

**关键论文链**:

| 论文 | 会议 | 贡献 |
|------|------|------|
| RustBelt | POPL 2018 | Safe Rust 内存安全形式化证明 |
| Stacked Borrows | POPL 2019 | 别名模型形式化 |
| RustBelt Relaxed | POPL 2020 | 弱内存模型扩展 |
| Tree Borrows | PLDI 2025 | 更实用的别名模型 |

**优势**: 提供 Rust 安全性的根本信任根基
**限制**: 纯理论研究、无直接工程工具、学习曲线陡峭

---

## 📊 适用场景对比矩阵

| 维度 | **Prusti** | **Kani** | **Miri** | **RustBelt** |
|------|-----------|----------|----------|-------------|
| **验证类型** | 演绎证明 | 模型检测 | 动态执行检查 | 形式化理论 |
| **自动化程度** | ⭐⭐ 需写规范 | ⭐⭐⭐ 高（限范围） | ⭐⭐⭐ 全自动 | ⭐ 纯手动证明 |
| **覆盖范围** | 所有输入路径 | 有界状态空间 | 单条执行路径 | 所有程序 |
| **unsafe 支持** | ❌ 不支持 | ⚠️ 有限支持 | ✅ 支持 | ✅ 可证明 |
| **并发支持** | ⭐ 有限 | ⭐⭐ 部分 | ✅ 数据竞争检测 | ✅ 分离逻辑 |
| **性能开销** | 慢（SMT 求解） | 极慢（状态爆炸） | 极慢（解释执行） | N/A（理论） |
| **学习曲线** | ⭐⭐ 中等 | ⭐⭐⭐ 平缓 | ⭐⭐⭐ 最平缓 | ⭐ 极陡峭 |
| **最佳场景** | 关键算法正确性 | `unsafe` 边界检查 | UB 回归测试 | 学术理解 |

**选型决策树**:

```text
开始选择验证工具
│
├─ 目标是理解 Rust 为什么安全?
│   └─ 是 → RustBelt / Iris 分离逻辑
│
├─ 需要自动发现运行时 UB?
│   └─ 是 → Miri (集成到 CI)
│
├─ 需要证明关键算法对所有输入正确?
│   ├─ 愿意写规范 → Prusti (功能正确性)
│   └─ 零规范 → Kani (有界验证)
│
├─ 涉及 unsafe 代码验证?
│   ├─ 需要证明 → Kani (+ 有界假设)
│   └─ 需要检测 UB → Miri
│
└─ 推荐组合: Miri (CI) + Kani (unsafe) + Prusti (核心算法)
```

---

## 🔄 工具协作工作流

生产环境中的推荐验证流水线：

```text
开发阶段:
├─ 1. cargo test          (功能正确)
├─ 2. cargo clippy        (代码质量)
├─ 3. cargo miri test     (UB 检测)
└─ 4. cargo audit         (安全审计)

关键模块验证:
├─ 5. Kani proof          (unsafe 边界、状态机)
└─ 6. Prusti verify       (核心算法规范)

发布前:
└─ 7. 人工审计 + 模糊测试  (补充覆盖)
```

**与 Prusti 教程的呼应**:

本项目 [Prusti 验证教程](./prusti_verification_tutorial.md) 提供了从入门到二分查找完整规范的实践路径。本全景文档则帮助读者理解：

- **何时选择 Prusti**（需数学级保证、愿意投入规范成本）
- **何时搭配 Kani**（`unsafe` 代码、无需手写规范）
- **何时运行 Miri**（作为基线 UB 检测，零成本集成）

---

## 🎓 学术研究路径推荐

### 工程师入门路径

```text
阶段 1: 工具使用 (2-4 周)
├─ Miri 集成到 CI 流程
├─ Kani 验证简单属性 (溢出、边界)
└─ 阅读 [Prusti 验证教程](./prusti_verification_tutorial.md)

阶段 2: 规范编写 (1-2 月)
├─ 为核心数据结构写 Prusti 规范
├─ 学习循环不变量设计
└─ 对比 "测试覆盖" vs "形式化证明覆盖"

阶段 3: 深度整合 (持续)
├─ 将验证纳入代码审查流程
├─ 维护规范与实现同步
└─ 贡献工具生态 (bug 报告、文档改进)
```

### 研究者深入路径

```text
阶段 1: 理论基础 (3-6 月)
├─ 分离逻辑 (Iris 教程)
├─ 操作语义与类型系统
└─ RustBelt 论文精读

阶段 2: 工具实现 (3-6 月)
├─ MIR 表示学习
├─ Viper / CBMC 后端理解
└─ 为现有工具贡献功能

阶段 3: 前沿研究 (持续)
├─ 异步形式化 (Pin, async drop)
├─ 并发验证 (GhostCell, 区间逻辑)
└─ 自动化不变量推断 (ML + 验证)
```

**推荐学习资源分层**:

| 层级 | 资源 | 目标 |
|------|------|------|
| **工程实践** | Miri 文档、Kani 教程、Prusti 用户指南 | 工具使用 |
| **理论理解** | RustBelt 论文、Stacked/Tree Borrows | 为什么安全 |
| **形式化方法** | Software Foundations (Vol 1-2) | 通用验证理论 |
| **前沿研究** | PLDI/POPL 近 5 年 Rust 相关论文 | 研究入口 |

---

## 🔗 参考资源

### 官方文档

- [Prusti 用户指南](https://viperproject.github.io/prusti-dev/user-guide/)
- [Kani 文档](https://model-checking.github.io/kani/)
- [Miri 文档](https://github.com/rust-lang/miri)
- [RustBelt 项目](https://plv.mpi-sws.org/rustbelt/)

### 学术论文

- [RustBelt: Securing the Foundations of the Rust Programming Language](https://plv.mpi-sws.org/rustbelt/popl18/) (POPL 2018)
- [Stacked Borrows: An Aliasing Model for Rust](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) (POPL 2019)
- [Tree Borrows](https://hal.science/hal-04196935/document) (PLDI 2025)
- [Kani: A Rust Verification Tool](https://github.com/model-checking/kani)

### 教程与课程

- [项目 Prusti 验证教程](./prusti_verification_tutorial.md)
- [Iris 教程](https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf)
- [Software Foundations](https://softwarefoundations.cis.upenn.edu/)
- [The Formal Semantics of Rust](https://doc.rust-lang.org/nightly/nightly-rustc/rustc_middle/mir/)

---

**维护者**: Rust 学习项目团队
**最后更新**: 2026-05-08
**状态**: ✅ 已完善
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)
