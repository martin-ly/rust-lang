# 形式化证明系统指南 {#形式化证明系统指南}

> **EN**: Formal Proof System Guide
> **Summary**: 形式化证明系统指南 Formal Proof System Guide.
> **概念族**: 形式化方法
> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6
> **创建日期**: 2026-01-15
> **最后更新**: 2026-06-29
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ **完成**
> **权威来源**:
>
> [Rust Reference](https://doc.rust-lang.org/reference/) |
> [Ferrocene FLS](https://spec.ferrocene.dev/) |
> [RustBelt](https://plv.mpi-sws.org/rustbelt/) |
> [Aeneas](https://github.com/AeneasVerif/aeneas)
>

---

## 📑 目录 {#目录}

>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>

- [形式化证明系统指南 {#形式化证明系统指南}](#形式化证明系统指南-形式化证明系统指南)
  - [📑 目录 {#目录}](#-目录-目录)
  - [一、证明系统总览 {#一证明系统总览}](#一证明系统总览-一证明系统总览)
    - [1.1 形式化证明的定义与目标 {#11-形式化证明的定义与目标}](#11-形式化证明的定义与目标-11-形式化证明的定义与目标)
    - [1.2 证明深度层级 L1/L2/L3 {#12-证明深度层级-l1l2l3}](#12-证明深度层级-l1l2l3-12-证明深度层级-l1l2l3)
    - [1.3 与国际权威成果的衔接 {#13-与国际权威成果的衔接}](#13-与国际权威成果的衔接-13-与国际权威成果的衔接)
  - [二、证明系统框架 {#二证明系统框架}](#二证明系统框架-二证明系统框架)
    - [2.1 公理-引理-定理-推论链 {#21-公理-引理-定理-推论链}](#21-公理-引理-定理-推论链-21-公理-引理-定理-推论链)
    - [2.2 证明义务（Proof Obligation）生成 {#22-证明义务proof-obligation生成}](#22-证明义务proof-obligation生成-22-证明义务proof-obligation生成)
    - [2.3 证明环境与会话状态 {#23-证明环境与会话状态}](#23-证明环境与会话状态-23-证明环境与会话状态)
  - [三、L1/L2/L3 定义与判定标准 {#三l1l2l3-定义与判定标准}](#三l1l2l3-定义与判定标准-三l1l2l3-定义与判定标准)
    - [3.1 L1 证明思路 {#31-l1-证明思路}](#31-l1-证明思路-31-l1-证明思路)
    - [3.2 L2 完整证明 {#32-l2-完整证明}](#32-l2-完整证明-32-l2-完整证明)
    - [3.3 L3 机器可检查证明 {#33-l3-机器可检查证明}](#33-l3-机器可检查证明-33-l3-机器可检查证明)
    - [3.4 层级提升路径 {#34-层级提升路径}](#34-层级提升路径-34-层级提升路径)
  - [四、工具链选择决策树 {#四工具链选择决策树}](#四工具链选择决策树-四工具链选择决策树)
    - [4.1 按证明目标选择 {#41-按证明目标选择}](#41-按证明目标选择-41-按证明目标选择)
    - [4.2 按代码特征选择 {#42-按代码特征选择}](#42-按代码特征选择-42-按代码特征选择)
    - [4.3 工具链能力矩阵 {#43-工具链能力矩阵}](#43-工具链能力矩阵-43-工具链能力矩阵)
  - [五、核心定理的机器证明对标 {#五核心定理的机器证明对标}](#五核心定理的机器证明对标-五核心定理的机器证明对标)
    - [5.1 所有权唯一性 T-OW2 {#51-所有权唯一性-t-ow2}](#51-所有权唯一性-t-ow2-51-所有权唯一性-t-ow2)
    - [5.2 数据竞争自由 T-BR1 {#52-数据竞争自由-t-br1}](#52-数据竞争自由-t-br1-52-数据竞争自由-t-br1)
    - [5.3 类型安全 T-TY3 {#53-类型安全-t-ty3}](#53-类型安全-t-ty3-53-类型安全-t-ty3)
  - [六、示例：从 L1 到 L3 的证明演进 {#六示例从-l1-到-l3-的证明演进}](#六示例从-l1-到-l3-的证明演进-六示例从-l1-到-l3-的证明演进)
    - [6.1 L1 证明思路 {#61-l1-证明思路}](#61-l1-证明思路-61-l1-证明思路)
    - [6.2 L2 完整证明 {#62-l2-完整证明}](#62-l2-完整证明-62-l2-完整证明)
    - [6.3 L3 Coq/Iris 草图 {#63-l3-coqiris-草图}](#63-l3-coqiris-草图-63-l3-coqiris-草图)
  - [七、权威来源与引用 {#七权威来源与引用}](#七权威来源与引用-七权威来源与引用)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

---

## 一、证明系统总览 {#一证明系统总览}

>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
>
> **来源: [Wikipedia - Formal Methods](https://en.wikipedia.org/wiki/Formal_Methods)**

### 1.1 形式化证明的定义与目标 {#11-形式化证明的定义与目标}

Rust 形式化证明系统旨在为 Rust 语言的核心安全属性建立**数学上可验证**的论证链。其目标包括：

1. **概念精确化**：将所有权、借用（Borrowing）、生命周期（Lifetimes）等直觉概念形式化为可操作的数学对象。
2. **定理体系化**：从公理出发，通过引理和推论，证明内存安全（Memory Safety）、数据竞争自由、类型安全等核心性质。
3. **机器可检查化**：最终将关键定理翻译为 Coq/Rocq、Lean4 等证明助手中的可检查证明对象。
4. **与国际权威对齐**：本项目证明体系与 RustBelt、Aeneas、Tree Borrows、RustSEM 等国际成果的定理建立逐条映射。

### 1.2 证明深度层级 L1/L2/L3 {#12-证明深度层级-l1l2l3}

| 层级 | 名称 | 内容特征 | 可验证性 | 典型载体 |
| :--- | :--- | :--- | :--- | :--- |
| **L1** | 证明思路 | 高层论证步骤、关键引理、证明结构 | 人工审阅 | Markdown、自然语言 |
| **L2** | 完整证明 | 含归纳基/步、案例分析、辅助引理编号 | 专家评审 | Markdown + 数学公式 |
| **L3** | 机器可检查 | 证明助手（Coq/Rocq、Lean4、Isabelle）可编译验证 | 机器验证 | `.v`、`.lean`、`.thy` |

### 1.3 与国际权威成果的衔接 {#13-与国际权威成果的衔接}

| 国际成果 | 机构 | 形式化方法 | 对应本项目 |
| :--- | :--- | :--- | :--- |
| **RustBelt** | MPI-SWS | Iris 分离逻辑 + Coq | `ownership_model`、`borrow_checker_proof`、L3 骨架 |
| **Aeneas** | INRIA 等 | Safe Rust → Coq/F*/HOL4/Lean | `10_aeneas_integration_plan.md` |
| **Tree Borrows** | ETH | 树结构借用（Borrowing）模型 + Rocq | `borrow_checker_proof` 演进 |
| **RustSEM** | K-Framework | 内存级可执行语义 | 可执行语义映射 |
| **Verus** | MSR/CMU/ETH | 线性 ghost 类型 + SMT | `send_sync_formalization` 扩展 |
| **Creusot** | Inria | Why3 + Pearlite | 函数合约/循环不变式 |
| **Kani** | AWS | CBMC 模型检查 | `borrow_checker_proof` 定理 1/5 |

---

## 二、证明系统框架 {#二证明系统框架}

>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
>
> **来源: [Coq Reference](https://coq.inria.fr/doc/)**

### 2.1 公理-引理-定理-推论链 {#21-公理-引理-定理-推论链}

本项目的证明编号规范：

| 前缀 | 含义 | 示例 |
| :--- | :--- | :--- |
| **A** | Axiom（公理） | A1: 未初始化内存不具合法值 |
| **L** | Lemma（引理） | L1: 读取未初始化内存是 UB |
| **T** | Theorem（定理） | T1: assume_init_drop 正确调用 drop |
| **C** | Corollary（推论） | C1: MaybeUninit 1.93 API 安全性 |

引用格式：`A1 → L1 → T1 → C1` 表示公理→引理→定理→推论链。

### 2.2 证明义务（Proof Obligation）生成 {#22-证明义务proof-obligation生成}

对任意待证命题 P，证明义务生成流程：

```text
待证定理 T

    │

    ▼

分解为子目标 {G₁, G₂, ..., Gₙ}

    │

    ▼

为每个子目标匹配公理/已证引理

    │

    ▼

生成 Proof Obligation：∀假设, 目标

    │

    ▼

选择证明策略（归纳/反证/构造/分离逻辑）

    │

    ▼

L1 文字证明 / L2 完整步骤 / L3 机器脚本
```

### 2.3 证明环境与会话状态 {#23-证明环境与会话状态}

形式化证明通常在以下环境中进行：

| 环境 | 适用层级 | 工具示例 |
| :--- | :--- | :--- |
| 文本 + 数学符号 | L1 | Markdown、LaTeX |
| 结构化证明草图 | L2 | Lean4 `calc`、Coq `Proof.`/`Qed.` |
| 交互式证明开发 | L3 | CoqIDE、VS Code + Lean4、Isabelle/jEdit |
| 自动化验证 | L3+/L4 | Aeneas、Kani、Creusot、Verus |

---

## 三、L1/L2/L3 定义与判定标准 {#三l1l2l3-定义与判定标准}

>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
>
> **来源: [ACM - Formal Verification](https://dl.acm.org/)**

### 3.1 L1 证明思路 {#31-l1-证明思路}

**判定标准**：

- 明确陈述定理与证明目标；
- 给出高层证明策略（如结构归纳、反证、分离逻辑）；
- 列出关键引理和依赖关系；
- 不强制要求完整的基例/步证明。

**示例**：`所有权唯一性定理 (T-OW2)` 的 L1 描述：通过状态转移归纳，证明 move/copy/drop 操作保持唯一所有者不变式。

### 3.2 L2 完整证明 {#32-l2-完整证明}

**判定标准**：

- 包含完整的归纳基例与归纳步骤；
- 所有案例分析穷举；
- 辅助引理有明确编号和陈述；
- 关键等式/不等式有推导说明。

**示例**：`类型安全定理 (T-TY3)` 的 L2 证明：由进展性 T-TY1 和保持性 T-TY2 组合得出，详细展开替换引理和求值规则案例。

### 3.3 L3 机器可检查证明 {#33-l3-机器可检查证明}

**判定标准**：

- 使用证明助手形式化所有定义、引理、定理；
- 所有证明脚本可被编译器/检查器通过（无 `Admitted`）；
- 语义模型、操作规则、不变式均编码为形式化对象；
- 与国际权威（如 RustBelt、Tree Borrows）的模型可对照。

**本项目 L3 现状**：

- `coq_skeleton/OWNERSHIP_UNIQUENESS.v`：T-OW2 骨架，证明 `Admitted` 待补全。
- `coq_skeleton/BORROW_DATARACE_FREE.v`：T-BR1 骨架。
- `coq_skeleton/TYPE_SAFETY.v`：T-TY3 骨架。

### 3.4 层级提升路径 {#34-层级提升路径}

```text
L1 证明思路

    │ 补全基例/步、辅助引理

    ▼

L2 完整证明

    │ 形式化语义、编码为证明助手

    ▼

L3 机器可检查证明

    │ 自动化/工具链集成

    ▼

L4 从代码自动生成证明（未来目标）
```

---

## 四、工具链选择决策树 {#四工具链选择决策树}

>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
>
> **来源: [Aeneas](https://github.com/AeneasVerif/aeneas)**
>
> **来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)**

### 4.1 按证明目标选择 {#41-按证明目标选择}

```text
证明目标

    │

    ├── 内存安全 / 数据竞争自由

    │       │

    │       ├── 需要机器可检查证明 ──→ Coq + Iris (RustBelt 路径)

    │       │

    │       └── 需要动态/有界验证 ───→ Miri / Kani

    │

    ├── 功能正确性

    │       │

    │       ├── Safe Rust 函数 ───────→ Aeneas / Creusot / Verus

    │       │

    │       └── 含 unsafe 的系统代码 ─→ Verus / Kani

    │

    └── 类型系统元理论

            │

            └── 进展/保持/类型安全 ───→ Coq/Rocq / Lean4 / Isabelle/HOL
```

### 4.2 按代码特征选择 {#42-按代码特征选择}

| 代码特征 | 推荐工具 | 理由 |
| :--- | :--- | :--- |
| 纯 Safe Rust 函数 | Aeneas、Creusot | 翻译到高阶逻辑，支持函数合约 |
| 含 `unsafe` 块 | Kani、Verus | 支持内存布局、符号执行、ghost 类型 |
| 并发原语 | RustBelt/Iris、Verus | 分离逻辑、线性 ghost 类型适合并发 |
| 标准库类型安全 | RustBelt、Tree Borrows | 已验证核心类型和借用模型 |
| 快速反例查找 | Miri、Kani | 动态/符号执行发现 UB |
| 教育教学 | Lean4、Coq | 交互式、可读性强 |

### 4.3 工具链能力矩阵 {#43-工具链能力矩阵}

| 工具 | 形式化方法 | 覆盖范围 | 输出 | 学习曲线 | 与本项目映射 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **RustBelt + Iris** | 分离逻辑 | 所有权（Ownership）、借用、核心库 | Coq 证明 | 高 | T-OW2 / T-BR1 / T-TY3 |
| **Aeneas** | 特征语言翻译 | Safe Rust | Coq/F*/HOL4/Lean | 中 | 功能正确性、所有权转移 |
| **Creusot** | Why3 / Pearlite | Safe Rust + 部分 unsafe | SMT 证明 | 中 | 函数合约、循环不变式 |
| **Verus** | 线性 ghost + SMT | 系统代码/并发 | Z3 证明 | 中 | Send/Sync、并发原语 |
| **Kani** | CBMC 模型检查 | unsafe / 属性 | 反例/有界验证 | 低-中 | 内存安全反例 |
| **Miri** | MIR 解释器 | UB 动态检测 | 运行时（Runtime）报告 | 低 | 借用规则反例 |
| **coq-of-rust** | THIR → Rocq | Safe + 部分标准库 | Rocq 脚本 | 高 | THIR 级形式化 |

---

## 五、核心定理的机器证明对标 {#五核心定理的机器证明对标}

>
> **来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)**
>
> **来源: [Aeneas](https://arxiv.org/abs/2206.07185)**
>
> **来源: [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)**

### 5.1 所有权唯一性 T-OW2 {#51-所有权唯一性-t-ow2}

| 维度 | 本项目 | RustBelt | Aeneas |
| :--- | :--- | :--- | :--- |
| 定理编号 | T-OW2 | Theorem 4.1 (λRust) | 翻译后隐式保持 |
| 方法 | 状态转移 + 归纳 | Iris 资源代数 + protocol | 纯函数式翻译消除别名 |
| 形式化 | L2 Markdown | L3 Coq/Iris | L3 Lean/Coq/F* |
| 关键不变式 | `ownership_unique(S)` | `own(b)` 资源唯一 | 线性类型 / 借用区域 |

### 5.2 数据竞争自由 T-BR1 {#52-数据竞争自由-t-br1}

| 维度 | 本项目 | RustBelt | Tree Borrows |
| :--- | :--- | :--- | :--- |
| 定理编号 | T-BR1 | Theorem 5.2 | Permission Tree 不变式 |
| 方法 | 借用规则 ⇒ 无冲突访问 | Iris 分离逻辑 | 树节点权限状态机 |
| 形式化 | L2 Markdown | L3 Coq/Iris | L3 Rocq |
| 关键不变式 | `&mut`/`&` 互斥 | `&mut` 独占资源 | 树节点 Protect/Active 状态 |

### 5.3 类型安全 T-TY3 {#53-类型安全-t-ty3}

| 维度 | 本项目 | RustBelt | Oxide |
| :--- | :--- | :--- | :--- |
| 定理编号 | T-TY3 | 类型系统（Type System）章节 | Type Safety |
| 方法 | 进展性 + 保持性 | λRust 操作语义 | 区域类型系统 |
| 形式化 | L2 Markdown | L3 Coq/Iris | 纸上形式化 |
| 关键引理 | 替换引理、求值规则 | 表达式语义、堆模型 | region/lifetime 约束 |

---

## 六、示例：从 L1 到 L3 的证明演进 {#六示例从-l1-到-l3-的证明演进}

>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
>
> **来源: [Coq Reference](https://coq.inria.fr/doc/)**

### 6.1 L1 证明思路 {#61-l1-证明思路}

**定理**：Move 操作保持所有权唯一性。

```text
策略：

1. 假设移动前状态满足 ownership_unique。

2. 将 x 拥有的值 v 移动到 y。

3. 移动后 x 变为 Moved，y 变为 Owned(v)。

4. 对于任意其他变量 z，若 z 也 Owned(v)，则移动前 z 必须等于 x；移动后 x 已 Moved，故 z 不存在。

5. 因此唯一性保持。
```

### 6.2 L2 完整证明 {#62-l2-完整证明}

**证明**：对可达状态进行归纳。

- **基例**：初始状态由语言语义保证唯一性。
- **归纳步**：假设 σ 满足唯一性，考虑 step σ σ'。
  - **Move**：设 σ(x) = (v, Owned)，σ'(x) = (v, Moved)，σ'(y) = (v, Owned)。对任意 z₁, z₂ 满足 σ'(z₁) = σ'(z₂) = (v, Owned)，由于 σ(x) 已 Moved，z₁, z₂ ≠ x；又 σ 唯一，故 z₁ = z₂。
  - **Copy**：生成新值 v'，不影响 v 的唯一性。
  - **Drop**：v 被释放，唯一性自然保持。

### 6.3 L3 Coq/Iris 草图 {#63-l3-coqiris-草图}

```coq
From iris.algebra Require Import base gmap.

From iris.proofmode Require Import tactics.

Parameter Value : Type.

Parameter Value_eq_dec : EqDecision Value.

Definition Var := nat.

Inductive OwnStatus := Owned | Moved | Dropped.

Definition State := gmap Var (Value * OwnStatus).

Definition ownership_unique (σ : State) : Prop :=

  forall v x1 x2,

    σ !! x1 = Some (v, Owned) ->

    σ !! x2 = Some (v, Owned) ->

    x1 = x2.

Inductive step : State -> State -> Prop :=

  | StepMove : forall σ x y v,

      σ !! x = Some (v, Owned) ->

      σ !! y = None ->

      step σ (<[x := (v, Moved)]> (<[y := (v, Owned)]> σ))

  | StepCopy : forall σ x y v,

      σ !! x = Some (v, Owned) ->

      σ !! y = None ->

      step σ (<[y := (v, Owned)]> σ)

  | StepDrop : forall σ x v,

      σ !! x = Some (v, Owned) ->

      step σ (<[x := (v, Dropped)]> σ).

Theorem T_OW2_move_preserves_uniqueness σ σ' :

  ownership_unique σ -> step σ σ' -> ownership_unique σ'.

Proof.

  intros Hunique Hstep.

  inversion Hstep; subst; clear Hstep;

  unfold ownership_unique; intros v z1 z2 Hz1 Hz2;

  destruct (decide (z1 = x)); destruct (decide (z2 = x));

  try (subst; rewrite lookup_insert in Hz1; rewrite lookup_insert in Hz2;

       inversion Hz1; inversion Hz2; auto; fail);

  try (rewrite lookup_insert_ne in Hz1 by auto;

       rewrite lookup_insert_ne in Hz2 by auto;

       apply Hunique with (v:=v); auto).

Qed.
```

---

## 七、权威来源与引用 {#七权威来源与引用}

>
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
>
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**

| 来源 | 作用 | 本项目使用方式 |
| :--- | :--- | :--- |
| Rust Reference | 语言规范基准 | 概念定义、规则编号 |
| Ferrocene FLS | 形式化语言规范 | 精确章节引用（如 Ch. 15/17/19/21） |
| RustBelt (POPL 2018) | 分离逻辑机器证明 | L3 目标、定理映射 |
| Aeneas (ICFP 2022/2023) | Safe Rust 翻译验证 | 工具链对接、函数式语义 |
| Tree Borrows (PLDI 2025) | 借用模型最新成果 | borrow_checker_proof 演进 |
| RustSEM (FMSD 2024) | 内存级可执行语义 | 可执行语义映射目标 |
| Miri/Kani/Creusot/Verus | 工具验证 | 反例、属性检查、合约证明 |

---

**维护者**: Rust Formal Methods Research Team

**最后更新**: 2026-06-29

**状态**: ✅ **完成**

**文档版本**: 2.0

**对应 Rust 版本**: 1.97.0+ (Edition 2024)

---

## 相关概念 {#相关概念}

>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [证明索引](10_proof_index.md)
- [定理与证明策略汇编](10_theorems_and_proof_strategies.md)
- [L3 机器可检查证明实施指南](10_l3_machine_proof_guide.md)
- [国际 Rust 形式化验证成果对标索引](10_international_formal_verification_index.md)
- [形式化证明批判性分析与计划 2026-02](10_formal_proof_critical_analysis_and_plan_2026_02.md)
- [研究笔记主索引](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Formal Methods](https://en.wikipedia.org/wiki/Formal_Methods)**
> **来源: [Coq Reference](https://coq.inria.fr/doc/)**
> **来源: [Lean 4](https://lean-lang.org/)**
> **来源: [RustBelt](https://plv.mpi-sws.org/rustbelt/)**
> **来源: [Aeneas](https://github.com/AeneasVerif/aeneas)**
> **来源: [Iris](https://iris-project.org/)**
> **来源: [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)**
> **来源: [RustSEM](https://doi.org/10.1007/s10703-024-00460-3)**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

---
