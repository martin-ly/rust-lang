# Rust 所有权系统可判定性 - 严格形式化研究

## 项目概述

本项目致力于构建 Rust 所有权系统的**完整、严格、可机械化的形式化理论**，解决现有形式化模型中元模型和元形式语言说明不完整的问题。

## 核心问题

> "很多形式模型并没有完整的说明元模型和元形式语言，因为我们需要严格形式化证明。"

Rust 所有权系统需要严格的可判定性证明，以确保：

1. Borrow checking 算法总是终止
2. 类型系统是可靠的（sound）
3. 形式化模型与真实 Rust 编译器一致

## 研究成果

### 1. 文献调研总结

识别出 8 个关键形式化工作：

| 工作 | 年份 | 核心贡献 | 与可判定性关系 |
|------|------|----------|----------------|
| **Oxide** | 2021 | 接近表面 Rust 的形式语义 | 基础类型系统 |
| **Featherweight Rust** | 2022 | 轻量级子集；发现终止性问题 | ⭐ 直接相关 |
| **FR 终止性论文** | 2022 | 证明 borrow checking 终止条件 | ⭐⭐ 核心参考 |
| **RustBelt** | 2018 | λ_Rust 演算；unsafe 代码验证 | 分离逻辑基础 |
| **Stacked Borrows** | 2020 | 别名模型操作语义 | Coq 机械化 |
| **AENEAS** | 2022 | LLBC 演算；符号执行 | 验证路径 |
| **Prusti/Creusot/Verus** | 2022-2023 | 实用验证工具 | 验证技术 |

### 2. 关键理论发现

#### 问题：Borrow Checking 可能不终止

```
Featherweight Rust 发现：
- 类型左值 (typing places) 的过程可能无限循环
- 原因：借用包含其他左值，递归无界
```

#### 解决方案：Linearizability 条件

```
Payet et al. 证明：
- 定义类型环境的 linearizability 条件
- 证明良类型程序满足此条件
- 此条件保证 borrow checking 终止
```

### 3. 已创建文档

```
docs/rust-ownership-decidability/
│
├── README.md                          # 本文件
├── RUST_OWNERSHIP_DECIDABILITY_RESEARCH_PLAN.md  # 详细研究计划
│
├── meta-model/                        # 元模型定义
│   ├── 01_abstract_syntax.md          # 抽象语法
│   ├── 02_semantic_domains.md         # 语义域
│   └── 03_judgments.md                # 判断形式
│
├── theorems/                          # 定理证明
│   └── decidability_theorems.md       # 核心定理草拟
│
├── coq-formalization/                 # Coq 形式化
│   └── README.md                      # 项目结构
│
└── progress/                          # 进度跟踪
    └── 2026-03-05_initial_setup.md    # 初始设置报告
```

## 核心定义

### 1. 类型的秩 (Type Rank)

```
rank: Type → ℕ

rank(B) = 0                    (基础类型)
rank(&ρ ω τ) = 1 + rank(τ)     (引用)
rank(Box τ) = 1 + rank(τ)      (Box)
```

### 2. 线性化条件 (Linearizability)

```
Linearizable(Γ) ≜
  ∀x ∈ dom(Γ). rank(Γ(x)) > max{ rank(y) | y ∈ fv(Γ(x)) }

直观: 类型依赖关系构成有向无环图 (DAG)
```

### 3. 核心定理

#### 定理 1: Borrow Checking 终止性

```
∀Γ: TypeEnv, Linearizable(Γ) → Terminates(borrow_check(Γ))
```

#### 定理 2: 类型保持

```
Δ; Γ; Θ ⊢ e : τ → σ; h ⊢ e ⇓ σ'; h'; v →
∃Γ', Θ', Δ; Γ'; Θ' ⊢ v : τ
```

#### 定理 3: 类型安全

```
Type Safety = Preservation + Progress
```

## 12 个月研究计划概览

| 阶段 | 时间 | 目标 | 交付物 |
|------|------|------|--------|
| 1 | M1-3 | 基础构建 | 元模型、L0-L2 Coq 形式化 |
| 2 | M4-6 | 可判定性证明 | 终止性定理证明 |
| 3 | M7-9 | 扩展与完善 | NLL、trait 系统 |
| 4 | M10-12 | 验证与发布 | 全部机械化、论文 |

## 后续行动

### 立即行动 (本周)

1. 深度精读 Oxide 和 FR 论文
2. 提取完整的类型规则
3. 开始 Coq 项目搭建

### 短期目标 (本月)

1. 完成核心语法的 Coq 形式化
2. 证明终止性引理
3. 建立与 rustc 的对比测试

### 长期目标 (3-12 月)

1. 完整的形式化理论
2. 全部定理的机械化证明
3. 学术论文发表

## 参考资源

### 核心论文

- [Oxide](https://arxiv.org/abs/1903.00982) - Rust 本质形式化
- [FR Termination](https://whileydave.com/publications/PPS22_NFM_preprint.pdf) - 终止性证明
- [RustBelt](https://plv.mpi-sws.org/rustbelt/) - 分离逻辑基础
- [Stacked Borrows](https://plv.mpi-sws.org/rustbelt/stacked-borrows/) - 别名模型

### 工具与代码

- [AENEAS](https://github.com/AeneasVerif/aeneas)
- [Creusot](https://github.com/creusot-rs/creusot)
- [Verus](https://github.com/verus-lang/verus)
- [Miri](https://github.com/rust-lang/miri)

## 贡献指南

本项目采用严格的数学形式化方法，所有定义和定理都需要：

1. 清晰的数学符号说明
2. 完整的推理规则
3. Coq/Isabelle 机械化证明
4. 与 rustc 的一致性验证

## 联系与跟踪

- **计划版本**: v1.0
- **最后更新**: 2026-03-05
- **下次评审**: 2026-04-05

---

*本项目致力于推进 Rust 语言的严格形式化理论基础，为系统编程语言的正确性验证树立标杆。*
