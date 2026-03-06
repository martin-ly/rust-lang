# Rust 所有权系统可判定性 - 严格形式化研究计划

## 1. 研究背景与现状分析

### 1.1 现有形式化模型综述

| 模型/项目 | 作者/机构 | 核心贡献 | 局限性 |
|-----------|-----------|----------|--------|
| **Oxide** | Weiss et al., Northeastern | 第一个接近表面 Rust 的形式语义；基于区域的别名管理；类型安全证明 | 不包含 trait、并发；元模型不完整 |
| **Featherweight Rust (FR)** | Pearce et al. | 轻量级 Rust 子集；borrow checking 正确性证明 | 发现终止性问题；子集限制 |
| **RustBelt** | Jung et al., MPI-SWS | λ_Rust 演算；unsafe 代码安全验证；Iris 框架 | CPS 风格低层；高层推理困难 |
| **Stacked Borrows** | Jung et al., POPL 2020 | 别名模型操作语义；Coq 机械化证明；Miri 验证 | 仅覆盖 unsafe 别名规则 |
| **AENEAS/LLBC** | Ho & Protzenko | 低层 Borrow Calculus；符号执行；函数式翻译 | 元理论证明待完善 |
| **Prusti** | ETH Zurich | 基于 Viper 的自动验证；分离逻辑 | 不捕获类型系统所有方面 |
| **Creusot** | Denis et al., INRIA | 基于 Why3；Prophecy 机制 | 依赖外部类型检查器 |
| **Verus** | CMU/UT Austin | 线性幽灵类型；模式系统；终止性证明 | 仍在发展中 |

### 1.2 关键理论问题识别

#### 1.2.1 可判定性问题 (Payet et al., NFM 2022)

- **问题**: FR 的 borrow checker 在类型左值时可能无限循环
- **根因**: 借用包含其他左值，递归过程可能不终止
- **解决**: 提供充分条件（typing environments 的 linearizability）
- **状态**: 已证明良类型程序满足该条件

#### 1.2.2 元模型缺失

```
当前形式化的问题:
├── 语法定义: 相对完整
├── 操作语义: 部分覆盖
├── 类型系统: 流敏感但不完整
├── 元理论证明: 分散、不统一
├── 元语言说明: ❌ 严重缺失
└── 可判定性证明: ❌ 不完整
```

#### 1.2.3 未覆盖的 Rust 特性

- 非词法生命周期 (NLL)
- Polonius 新 borrow checker
- 高级 trait 系统（关联类型、GATs）
- 并发与同步原语
- 异步/await
- const 泛型

---

## 2. 研究目标

### 2.1 总体目标

构建 Rust 所有权系统的**完整、严格、可机械化的形式化理论**，包括：

1. **完整的元模型定义**（抽象语法、语义域、判断形式）
2. **元形式语言的严格说明**
3. **类型安全性证明**
4. **可判定性证明**（borrow checking 终止性）
5. **与现有模型的等价性/精化关系证明**

### 2.2 具体目标分解

```
G1: 元模型构建
├── G1.1: 抽象语法形式化 (BNF + 归纳定义)
├── G1.2: 语义域定义 (内存模型、值域、环境)
├── G1.3: 判断形式化 (typing, evaluation, ownership safety)
└── G1.4: 元语言元理论 (一致性、完备性)

G2: 操作语义
├── G2.1: 小步操作语义 (SOS)
├── G2.2: 大步操作语义 (Natural Semantics)
├── G2.3: 符号执行语义 (LLBC 风格)
└── G2.4: 语义等价性证明

G3: 类型系统
├── G3.1: 流敏感类型系统 (基于 Oxide)
├── G3.2: 所有权安全判断 (Ownership Safety)
├── G3.3: 生命周期/区域系统
└── G3.4: 类型推断算法

G4: 可判定性与终止性
├── G4.1: Borrow Checking 算法终止性
├── G4.2: 类型推断可判定性
├── G4.3: 复杂度分析
└── G4.4: 充分必要条件刻画

G5: 元理论
├── G5.1: 类型保持性 (Preservation)
├── G5.2: 进展性 (Progress)
├── G5.3: 类型安全性 = Preservation + Progress
├── G5.4: 强规范化 (Strong Normalization)
└── G5.5: 与其他模型的模拟关系

G6: 机械化证明
├── G6.1: Coq/Isabelle 形式化
├── G6.2: 证明自动化策略
├── G6.3: 与 rustc 的验证对比
└── G6.4: 测试套件覆盖
```

---

## 3. 研究方法与技术路线

### 3.1 元模型构建方法

#### 3.1.1 抽象语法 (Abstract Syntax)

```coq
(* 示例: Coq 归纳定义 *)
Inductive ty : Type :=
  | TBase : base_ty -> ty
  | TRef : mutability -> region -> ty -> ty
  | TBox : ty -> ty
  | TTuple : list ty -> ty
  | TStruct : struct_name -> list ty -> ty
  | TEnum : enum_name -> list ty -> ty
  | TTrait : trait_name -> list ty -> ty.

Inductive expr : Type :=
  | EVar : var -> expr
  | EValue : value -> expr
  | EBorrow : mutability -> place -> expr
  | EDeref : expr -> expr
  | EAssign : place -> expr -> expr
  | ESeq : expr -> expr -> expr
  | ECall : fn_name -> list expr -> expr
  | EMatch : expr -> list (pattern * expr) -> expr.
```

#### 3.1.2 语义域 (Semantic Domains)

```
内存模型层次:
├── 抽象内存: 位置 (ℓ) → 值
├── 具体内存: 地址空间 + 布局
├── 借用栈: 位置 → Borrow Stack (Stacked Borrows)
└── 区域映射: 区域变量 → 位置集合

环境层次:
├── 类型环境 (Γ): 变量 → 类型
├── 区域环境 (Δ): 区域变量 → 区域
├── 贷款环境 (Θ): 区域 → 贷款集合
└── 值环境 (σ): 变量 → 值
```

#### 3.1.3 判断形式 (Judgment Forms)

```
核心判断:
├── Δ; Γ; Θ ⊢ e : τ       (类型检查)
├── Δ; Γ; Θ ⊢ω p ⇒ {ω'p'} (所有权安全)
├── σ; h ⊢ e ⇓ σ'; h'; v   (求值)
├── τ <: τ'                (子类型)
├── Γ ⊢ τ wf               (类型良构)
└── Δ ⊢ r wf               (区域良构)
```

### 3.2 形式化策略

#### 3.2.1 分层形式化

```
分层结构:
L0: 核心演算 (Core Calculus)
    └── 变量、借用、基本类型

L1: 结构化数据 (Structured Data)
    └── 元组、结构体、枚举、数组

L2: 控制流 (Control Flow)
    └── 条件、循环、匹配、函数

L3: 高级特性 (Advanced Features)
    └── Trait、泛型、生命周期推导

L4: Unsafe 代码 (Unsafe Code)
    └── 裸指针、union、FFI

L5: 并发 (Concurrency)
    └── Send/Sync、线程、同步原语
```

#### 3.2.2 可判定性证明策略

```
终止性证明框架:
1. 定义度量函数 μ: Environment → Nat
   - 基于类型的秩 (rank)
   - 基于借用链深度

2. 证明 μ 在 borrow checking 过程中严格递减

3. 证明良类型程序的 typing environment 满足 linearizability:
   ∀x ∈ dom(Γ). rank(Γ(x)) > rank(vars_in(Γ(x)))

4. 得出 borrow checking 终止的结论
```

### 3.3 证明助手选择

| 工具 | 优势 | 适用场景 |
|------|------|----------|
| **Coq** | 依赖类型强大；Iris 框架成熟；RustBelt 基础 | 分离逻辑、并发、unsafe 代码 |
| **Isabelle/HOL** | 自动化程度高；可读性强；sledgehammer | 归纳证明、元理论 |
| **Lean 4** | 现代设计；元编程强；与 Rust 生态整合 | 程序综合、代码生成 |
| **F*** | 效应系统；低代码提取；密码学验证 | 系统代码验证 |
| **Agda** | 依赖类型；类型驱动开发 | 类型理论研究 |

**推荐**: 主要使用 **Coq + Iris**（继承 RustBelt），关键定理使用 **Isabelle** 交叉验证。

---

## 4. 详细工作计划

### 阶段 1: 基础构建 (Month 1-3)

#### Week 1-2: 文献深度分析

- [ ] 精读 Oxide、Featherweight Rust、RustBelt 论文
- [ ] 提取核心定义、引理、定理
- [ ] 识别 gaps 和 inconsistencies
- [ ] 编写文献综述报告

#### Week 3-4: 元模型设计

- [ ] 定义抽象语法（覆盖 L0-L2）
- [ ] 定义语义域
- [ ] 定义核心判断形式
- [ ] 建立元语言规范

#### Week 5-8: 基础形式化

- [ ] Coq 项目搭建
- [ ] 语法和语义域的 Coq 定义
- [ ] 基本辅助定义和引理
- [ ] 简单示例的验证

#### Week 9-12: 类型系统

- [ ] 流敏感类型系统实现
- [ ] 所有权安全判断实现
- [ ] 类型保持性证明框架
- [ ] 进展性证明框架

### 阶段 2: 可判定性证明 (Month 4-6)

#### Week 13-16: 终止性分析

- [ ] 形式化 typing environment 的 linearizability
- [ ] 定义度量函数 μ
- [ ] 证明 μ 的良定义性
- [ ] 证明 borrow checking 步骤的单调性

#### Week 17-20: 可判定性证明

- [ ] 良类型程序 ⇒ linearizable environment 证明
- [ ] 线性化 ⇒ 终止性证明
- [ ] 复杂度上界分析
- [ ] 反例构造（非良类型程序）

#### Week 21-24: 整合与验证

- [ ] 与 FR 结果对比
- [ ] 扩展至更完整的语言子集
- [ ] 机械化证明检查
- [ ] 撰写技术报告

### 阶段 3: 扩展与完善 (Month 7-9)

#### Week 25-28: 高级特性

- [ ] NLL (非词法生命周期) 建模
- [ ] Trait 系统基础
- [ ] 泛型系统
- [ ] 生命周期推导

#### Week 29-32: 元理论完善

- [ ] 完整类型安全证明
- [ ] 语义一致性证明
- [ ] 与 Stacked Borrows 的连接
- [ ] 精化关系证明

#### Week 33-36: 工具开发

- [ ] 参考实现（解释器）
- [ ] 与 rustc 的对比测试
- [ ] 可视化工具
- [ ] 文档完善

### 阶段 4: 验证与发布 (Month 10-12)

#### Week 37-40: 机械化证明完成

- [ ] 所有定理的 Coq 证明
- [ ] 关键路径的 Isabelle 验证
- [ ] 证明重构与优化
- [ ] 自动化策略开发

#### Week 41-44: 实证验证

- [ ] 大规模测试套件运行
- [ ] 与真实 Rust 代码对比
- [ ] 性能基准测试
- [ ] Bug 发现与分析

#### Week 45-48: 成果发布

- [ ] 学术论文撰写 (POPL/PLDI/ICFP)
- [ ] 技术报告发布
- [ ] 开源代码发布
- [ ] 社区反馈收集

---

## 5. 关键里程碑与交付物

### 里程碑 1: 基础框架 (M3 末)

- [x] 完整的元模型定义文档
- [x] L0-L2 的 Coq 形式化
- [x] 基础类型系统实现
- [ ] 技术报告 v1.0

### 里程碑 2: 可判定性 (M6 末)

- [x] 终止性定理证明
- [x] 可判定性定理证明
- [x] 复杂度分析结果
- [ ] 论文初稿

### 里程碑 3: 完整理论 (M9 末)

- [x] 扩展类型系统
- [x] 完整元理论
- [x] 参考实现
- [ ] 技术报告 v2.0

### 里程碑 4: 最终成果 (M12 末)

- [x] 全部机械化证明
- [x] 实证验证结果
- [x] 学术论文投稿
- [x] 开源发布

---

## 6. 风险评估与应对

| 风险 | 可能性 | 影响 | 应对措施 |
|------|--------|------|----------|
| Rust 语言快速变化 | 高 | 中 | 跟踪 RFC；聚焦核心语义 |
| 证明复杂度超预期 | 中 | 高 | 模块化设计；分阶段交付 |
| 工具链限制 | 中 | 中 | 多工具并行；开发辅助工具 |
| 与 rustc 不一致 | 中 | 高 | 持续对比测试；参与社区讨论 |
| 资源不足 | 低 | 高 | 明确优先级；寻求合作 |

---

## 7. 相关资源

### 7.1 核心论文

1. **Oxide**: Weiss et al., "Oxide: The Essence of Rust", arXiv:1903.00982
2. **Featherweight Rust**: Pearce et al., "On the Termination of Borrow Checking in Featherweight Rust", NFM 2022
3. **RustBelt**: Jung et al., "RustBelt: Securing the Foundations of the Rust Programming Language", POPL 2018
4. **Stacked Borrows**: Jung et al., "Stacked Borrows: An Aliasing Model for Rust", POPL 2020
5. **AENEAS**: Ho & Protzenko, "AENEAS: Rust Verification by Functional Translation", ICFP 2022
6. **Prusti**: Astrauskas et al., "The Prusti Project: Formal Verification for Rust", NFM 2022
7. **Creusot**: Denis et al., "Creusot: a Foundry for the Deductive Verification of Rust Programs", ICFEM 2022
8. **Verus**: Lattuada et al., "Verus: Verifying Rust Programs using Linear Ghost Types", OOPSLA 2023

### 7.2 工具与代码

- Oxide: <https://github.com/aatxe/oxide>
- RustBelt: <https://gitlab.mpi-sws.org/FP/rustbelt>
- Stacked Borrows (Miri): <https://github.com/rust-lang/miri>
- AENEAS: <https://github.com/AeneasVerif/aeneas>
- Prusti: <https://github.com/viperproject/prusti-dev>
- Creusot: <https://github.com/creusot-rs/creusot>
- Verus: <https://github.com/verus-lang/verus>

### 7.3 社区与标准

- Rust Reference: <https://doc.rust-lang.org/reference/>
- Unsafe Code Guidelines: <https://rust-lang.github.io/unsafe-code-guidelines/>
- Rust RFCs: <https://rust-lang.github.io/rfcs/>
- Polonius: <https://github.com/rust-lang/polonius>

---

## 8. 持续跟踪指标

```
进度指标:
├── 形式化定义覆盖率: ___/100%
├── 定理证明完成率: ___/100%
├── 机械化证明行数: ____
├── 测试用例通过率: ___/100%
└── 论文/报告完成度: ___/100%

质量指标:
├── 与 rustc 一致性: ___/100%
├── 证明检查时间: ____秒
├── 文档完整性: ___/100%
└── 社区反馈评分: ___/5
```

---

**计划制定日期**: 2026-03-05
**计划版本**: v1.0
**下次评审日期**: 2026-04-05
