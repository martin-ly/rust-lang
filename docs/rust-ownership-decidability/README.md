# Rust所有权与可判定性：全面深度研究

> **研究范围**：本系列文档系统性地探讨Rust编程语言的所有权系统及其与可判定性理论的深层联系，整合国际权威学术资源、形式化验证研究成果及类型理论经典文献。

## 项目索引

```text
rust-ownership-decidability/
├── README.md                          # 本文件 - 项目导航
├── 00-foundations/                    # 理论基础与形式化定义
│   ├── 00-01-linear-logic.md          # 线性逻辑基础 (Girard 1987)
│   ├── 00-02-affine-types.md          # 仿射类型系统 (Kopylov 2001)
│   ├── 00-03-ownership-semantics.md   # 所有权语义学 (RustBelt)
│   └── 00-04-decidability-theory.md   # 可判定性理论基础
├── 01-core-concepts/                  # Rust核心概念体系
│   ├── 01-01-ownership-rules.md       # 所有权三大规则
│   ├── 01-02-borrowing-system.md      # 借用系统深度分析
│   ├── 01-03-lifetimes.md             # 生命周期理论
│   └── 01-04-nll-analysis.md          # 非词法生命周期
├── 02-formal-models/                  # 形式化模型
│   ├── 02-01-rustbelt-lambda-rust.md  # RustBelt & λRust
│   ├── 02-02-corus-calc.md            # COR演算
│   ├── 02-03-oxide.md                 # Oxide形式化
│   └── 02-04-polonius.md              # Polonius Datalog模型
├── 03-verification-tools/             # 验证工具链
│   ├── 03-01-creusot.md               # Creusot验证器
│   ├── 03-02-prusti.md                # Prusti验证器
│   ├── 03-03-rusthorn.md              # RustHorn CHC验证
│   └── 03-04-verus.md                 # Verus系统验证
├── 04-decidability-analysis/          # 可判定性分析
│   ├── 04-01-type-inference.md        # 类型推断可判定性
│   ├── 04-02-borrow-checking.md       # 借用检查可判定性
│   ├── 04-03-lifetime-inference.md    # 生命周期推断
│   └── 04-04-undecidable-fragments.md # 不可判定片段
├── 05-comparative-study/              # 比较研究
│   ├── 05-01-linear-vs-affine.md      # 线性vs仿射类型
│   ├── 05-02-ownership-vs-seplogic.md # 所有权vs分离逻辑
│   └── 05-03-rust-vs-other-langs.md   # 多语言对比
├── 06-visualizations/                 # 思维表征可视化
│   ├── 06-01-concept-matrix.md        # 概念多维矩阵
│   ├── 06-02-decision-trees.md        # 决策树图
│   └── 06-03-architecture-diagrams.md # 架构设计树图
└── 07-references/                     # 参考文献
    └── bibliography.md                # 完整文献列表
```

## 核心研究主题

### 1. 理论基础三角

```
                    ┌─────────────────┐
                    │   线性逻辑      │  ← Girard (1987)
                    │  Linear Logic   │    Proof-Nets
                    └────────┬────────┘
                             │
            ┌────────────────┼────────────────┐
            │                │                │
            ▼                ▼                ▼
    ┌───────────────┐ ┌───────────────┐ ┌───────────────┐
    │   分离逻辑    │ │   仿射逻辑    │ │   类型理论    │
    │  Separation   │ │ Affine Logic  │ │  Type Theory  │
    │    Logic      │ │  (Decidable)  │ │               │
    │  (Reynolds)   │ │  (Kopylov)    │ │  (Pierce)     │
    └───────┬───────┘ └───────┬───────┘ └───────┬───────┘
            │                │                │
            └────────────────┼────────────────┘
                             │
                    ┌────────▼────────┐
                    │   Rust所有权    │
                    │    Ownership    │
                    │     System      │
                    └─────────────────┘
```

### 2. 形式化验证工具链映射

| 工具 | 机构 | 核心方法 | 形式化基础 |
|------|------|----------|-----------|
| **RustBelt** | MPI-SWS | 逻辑关系 + Iris | λRust in Coq |
| **Creusot** | LMF, Paris-Saclay | 预言变量 | Why3 |
| **Prusti** | ETH Zurich | Viper | 分离逻辑 |
| **RustHorn** | 东京大学 | CHC编码 | COR演算 |
| **Aeneas** | Inria | 函数式提取 | LLBC |
| **Verus** | CMU/VMware | 资源代数 | Z3 |

### 3. 可判定性边界

```
┌─────────────────────────────────────────────────────────────────┐
│                     可判定性谱系                                 │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  DECIDABLE ←────────────────────────────────────→ UNDECIDABLE  │
│                                                                 │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  ┌─────────┐ │
│  │ 简单类型λ  │  │  仿射逻辑   │  │ 多态类型λ  │  │ 线性逻辑│ │
│  │  STLC      │  │  Affine     │  │ System F    │  │ Linear  │ │
│  │            │  │  Logic      │  │             │  │ Logic   │ │
│  └─────────────┘  └─────────────┘  └─────────────┘  └─────────┘ │
│        │                │                │              │       │
│        ▼                ▼                ▼              ▼       │
│     P-complete     PSPACE-complete   不可判定      不可判定     │
│                                                                 │
│  Rust借用检查: 在实践中可判定 (基于数据流分析)                   │
│  Rust类型推断: 全局可判定 (基于Hindley-Milner扩展)               │
│  Rust泛型约束: 图灵完备 (存在不可判定情况)                       │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

## 关键学术资源

### 基础文献

1. **Girard, J.-Y.** (1987). *Linear Logic*. Theoretical Computer Science.
2. **Pierce, B.C.** (2002). *Types and Programming Languages*. MIT Press.
3. **Pierce, B.C.** (2004). *Advanced Topics in Types and Programming Languages*. MIT Press.

### Rust形式化核心

1. **Jung, R., et al.** (2018). *RustBelt: Securing the Foundations of the Rust Programming Language*. POPL.
2. **Matsushita, Y., et al.** (2021). *RustHorn: CHC-based Verification for Rust Programs*. ACM TOPLAS.
3. **Denis, X., et al.** (2022). *Creusot: A Foundry for the Deductive Verification of Rust Programs*. ICFEM.

### 可判定性理论

1. **Kopylov, A.P.** (2001). *Decidability of Linear Affine Logic*. Information and Computation.
2. **Lincoln, P., et al.** (1992). *Decision Problems for Second-Order Linear Logic*. LICS.

### 大学课程资源

1. **Stanford CS242**: Programming Languages (Will Crichton)
2. **CMU 15-411**: Compiler Design
3. **MIT 6.822**: Formal Reasoning About Programs

## 阅读路线图

### 路径A：理论优先

```
00-foundations/ → 05-comparative-study/ → 02-formal-models/
```

### 路径B：实践优先

```
01-core-concepts/ → 03-verification-tools/ → 04-decidability-analysis/
```

### 路径C：全面深入

```
按目录顺序阅读，配合06-visualizations/中的图解
```

## 思维表征导航

| 表征类型 | 位置 | 用途 |
|---------|------|------|
| **概念多维矩阵** | 06-01-concept-matrix.md | 快速对比与概念关联 |
| **决策树图** | 06-02-decision-trees.md | 推理路径与证明决策 |
| **架构树图** | 06-03-architecture-diagrams.md | 系统结构与层次关系 |
| **类型推导流程** | 01-core-concepts/ | 算法执行可视化 |

---

**最后更新**: 2026-03-04
**研究状态**: 持续深化中
