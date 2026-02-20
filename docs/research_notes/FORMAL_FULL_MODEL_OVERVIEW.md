# Rust 形式化全模型：统一形式系统入口

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 单一文档勾勒 ownership + borrow + lifetime + type + trait + async + pin 的**统一形式系统**，含公理列表、定理依赖 DAG、与各子文档的映射
> **上位文档**: [FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02](./FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md)、[THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE](./THEORETICAL_AND_ARGUMENTATION_SYSTEM_ARCHITECTURE.md)

---

## 📊 目录

- [Rust 形式化全模型：统一形式系统入口](#rust-形式化全模型统一形式系统入口)
  - [📊 目录](#-目录)
  - [一、统一形式系统总览](#一统一形式系统总览)
    - [1.1 核心机制与公理层](#11-核心机制与公理层)
    - [1.2 定理依赖 DAG（简化）](#12-定理依赖-dag简化)
    - [1.3 域间定理推导链（显式）](#13-域间定理推导链显式)
    - [1.4 公理→组合定理 DAG（支柱 1+3 衔接）](#14-公理组合定理-dag支柱-13-衔接)
  - [二、公理列表（统一编号）](#二公理列表统一编号)
    - [2.1 内存与所有权](#21-内存与所有权)
    - [2.2 生命周期与类型](#22-生命周期与类型)
    - [2.3 控制流与变量](#23-控制流与变量)
    - [2.4 异步与 Pin](#24-异步与-pin)
  - [三、与各子文档的映射](#三与各子文档的映射)
  - [四、抽象层次对应](#四抽象层次对应)
  - [五、相关文档](#五相关文档)

---

## 一、统一形式系统总览

### 1.1 核心机制与公理层

| 机制 | 公理/定义 | 子文档 |
| :--- | :--- | :--- |
| **所有权** | 规则 1–3：唯一所有者、移动转移、作用域结束释放 | [ownership_model](./formal_methods/ownership_model.md) |
| **借用** | 规则 5–8：共享借用、可变借用、互斥、作用域 | [borrow_checker_proof](./formal_methods/borrow_checker_proof.md) |
| **生命周期** | Axiom LF1–LF2、Def 1.4、$\ell \subseteq \text{lft}$ | [lifetime_formalization](./formal_methods/lifetime_formalization.md) |
| **类型系统** | 进展性、保持性、typing rules | [type_system_foundations](./type_theory/type_system_foundations.md) |
| **型变** | Def 1.1–3.1（协变、逆变、不变） | [variance_theory](./type_theory/variance_theory.md) |
| **Trait** | Axiom COH1/COH2、对象安全、impl 解析 | [trait_system_formalization](./type_theory/trait_system_formalization.md) |
| **异步** | Def 4.1–5.2（Future、Poll、Ready/Pending） | [async_state_machine](./formal_methods/async_state_machine.md) |
| **Pin** | Def 1.1–2.2（位置稳定、自引用） | [pin_self_referential](./formal_methods/pin_self_referential.md) |
| **Send/Sync** | Def SEND1/SYNC1、SYNC-L1（$T:\text{Sync} \Leftrightarrow \&T:\text{Send}$）；SEND-T1/SYNC-T1 | [send_sync_formalization](./formal_methods/send_sync_formalization.md) |
| **控制流** | A-CF1：控制流归约保持类型与所有权 | [formal_methods/README](./formal_methods/README.md#控制流形式化) |
| **变量** | Def 1.4 绑定、Def 1.5 遮蔽 | [ownership_model](./formal_methods/ownership_model.md) |

### 1.2 定理依赖 DAG（简化）

```text
                    [公理层]
                         │
    ┌────────────────────┼────────────────────┐
    │                    │                    │
[所有权规则]          [借用规则]          [类型规则]
    │                    │                    │
    ▼                    ▼                    ▼
[ownership T2]      [borrow T1]         [type T1,T2]
[ownership T3]      [borrow T2]         [type T3]
    │                    │                    │
    └────────────────────┼────────────────────┘
                         │
                    [lifetime LF-T1–T3]
                         │
    ┌────────────────────┼────────────────────┐
    │                    │                    │
[variance T1–T4]   [async T6.1–T6.3]   [pin T1–T3]
    │                    │                    │
    │              [send_sync SEND-T1/SYNC-T1] │
    └────────────────────┼────────────────────┘
                         │
                    [CE-T1–T3 组合工程]
                         │
                    [顶层 CSO-T1, USF-T1]
```

### 1.3 域间定理推导链（显式）

| 推导链 | 依赖 | 结论 |
| :--- | :--- | :--- |
| ownership T2 → borrow T1 | 所有权唯一性 ⇒ 借用互斥 | 数据竞争自由 |
| ownership T3 → CE-T1 | 内存安全框架 ⇒ 组合保持 | 组合保持内存安全 |
| borrow T1 + type T3 → CE-T2 | 数据竞争自由 + 类型安全 | 组合保持数据竞争自由 |
| lifetime LF-T2 → borrow T2 | 引用有效性 ⇒ 借用规则 | 借用规则正确性 |
| send_sync SEND-T1/SYNC-T1 → async T6.2、SPAWN-T1 | 跨线程转移/共享安全 ⇒ 并发安全 | 与 borrow T1 一致、spawn/Future 数据竞争自由 |

### 1.4 公理→组合定理 DAG（支柱 1+3 衔接）

```text
[支柱 1 公理层]
  A-OW1/2/3 (所有权)     A-BR1/2/3/4 (借用)     A-TY1/2 (类型)
         │                       │                     │
         ▼                       ▼                     ▼
  ownership T2/T3          borrow T1/T2           type T1/T2/T3
         │                       │                     │
         └───────────────────────┼─────────────────────┘
                                 │
                    [支柱 3 组合定理层]
                                 │
              ┌──────────────────┼──────────────────┐
              ▼                  ▼                  ▼
          CE-T1             CE-T2             CE-T3
     (内存安全保持)    (数据竞争自由保持)   (类型安全保持)
              │                  │                  │
              └──────────────────┴──────────────────┘
                                 │
                    CE-MAT-T1 (L1/L2 静态可判定；L3/L4 需额外验证)
```

**显式推导**：

- **CE-T1** ← ownership T3（无悬垂、无双重释放、无泄漏 ⇒ 组合保持）
- **CE-T2** ← borrow T1 + type T3（数据竞争自由 + 类型安全 ⇒ 组合保持）
- **CE-T3** ← type T3（类型安全 ⇒ 组合保持）

---

## 二、公理列表（统一编号）

### 2.1 内存与所有权

| 编号 | 内容 | 来源 |
| :--- | :--- | :--- |
| A-OW1 | 每个值至多一个所有者 | ownership 规则 1 |
| A-OW2 | 移动转移所有权 | ownership 规则 2 |
| A-OW3 | 作用域结束释放 | ownership 规则 3 |
| A-BR1 | 共享借用可多路 | borrow 规则 5 |
| A-BR2 | 可变借用独占 | borrow 规则 6 |
| A-BR3 | 共享与可变互斥 | borrow 规则 7 |
| A-BR4 | 借用作用域约束 | borrow 规则 8 |

### 2.2 生命周期与类型

| 编号 | 内容 | 来源 |
| :--- | :--- | :--- |
| A-LF1 | 生命周期为时间区间 | lifetime Axiom LF1 |
| A-LF2 | outlives 传递 | lifetime Axiom LF2 |
| A-TY1 | 进展性 $\Gamma \vdash e:\tau \rightarrow e \text{ value} \lor \exists e': e\to e'$ | type_system T1 |
| A-TY2 | 保持性 $\Gamma \vdash e:\tau \land e\to e' \rightarrow \Gamma \vdash e':\tau$ | type_system T2 |
| A-VAR1 | 协变：$S<:T \Rightarrow F[S]<:F[T]$ | variance Def 1.1 |
| A-VAR2 | 逆变：参数位置 | variance Def 2.1 |
| A-VAR3 | 不变：$F[S] \not<: F[T]$ | variance Def 3.1 |

### 2.3 控制流与变量

| 编号 | 内容 | 来源 |
| :--- | :--- | :--- |
| A-CF1 | 控制流归约保持类型与所有权 | formal_methods README |
| A-BIND1 | 变量绑定建立/更新 $\Gamma$ | ownership Def 1.4 |
| A-SHADOW1 | 变量遮蔽使旧绑定不可访问；隐式 drop | ownership Def 1.5 |

### 2.4 异步与 Pin

| 编号 | 内容 | 来源 |
| :--- | :--- | :--- |
| A-AS1 | Future 状态 Ready/Pending | async Def 4.1 |
| A-AS2 | Poll 归约 | async Def 5.2 |
| A-PIN1 | Pin 保证位置稳定 | pin Def 1.1 |
| A-PIN2 | 自引用需 Pin | pin Def 2.2 |

---

## 三、与各子文档的映射

| 子文档 | 本模型对应 | 定理编号 |
| :--- | :--- | :--- |
| [ownership_model](./formal_methods/ownership_model.md) | §2.1 内存与所有权、§2.3 A-BIND1/SHADOW1 | T2, T3, Def 1.4/1.5, RC-T1, … |
| [borrow_checker_proof](./formal_methods/borrow_checker_proof.md) | §2.1 A-BR1–4 | T1, T2, CHAN-T1, MUTEX-T1, … |
| [lifetime_formalization](./formal_methods/lifetime_formalization.md) | §2.2 A-LF1–2 | LF-T1, LF-T2, LF-T3 |
| [type_system_foundations](./type_theory/type_system_foundations.md) | §2.2 A-TY1–2 | T1–T5, LUB-T1, … |
| [variance_theory](./type_theory/variance_theory.md) | §2.2 A-VAR1–3 | T1–T4, VAR-COM-T1 |
| [trait_system_formalization](./type_theory/trait_system_formalization.md) | - | T1–T3, COH-T1, RPIT-T1, … |
| [async_state_machine](./formal_methods/async_state_machine.md) | §2.4 A-AS1–2 | T6.1–T6.3, SPAWN-T1 |
| [pin_self_referential](./formal_methods/pin_self_referential.md) | §2.4 A-PIN1–2 | T1–T3 |
| [04_compositional_engineering](./software_design_theory/04_compositional_engineering/) | 组合层 | CE-T1–T3, CE-L1, CE-C1 |
| [UNIFIED_SYSTEMATIC_FRAMEWORK](./UNIFIED_SYSTEMATIC_FRAMEWORK.md) | 顶层 | USF-T1, USF-C1 |

---

## 四、抽象层次对应

| 层次 | 本模型覆盖 | 国际对标 |
| :--- | :--- | :--- |
| **语言级** | 本模型主体 | RustBelt λ Rust、Rust Distilled |
| **MIR 级** | 未覆盖 | RustBelt MIR、coq-of-rust THIR |
| **内存级** | 未覆盖 | RustSEM (K-Framework) |

---

## 五、相关文档

- [CORE_THEOREMS_FULL_PROOFS](./CORE_THEOREMS_FULL_PROOFS.md) — 核心定理 T-OW2、T-BR1、T-TY3 完整证明（L2）
- [FORMAL_LANGUAGE_AND_PROOFS](./FORMAL_LANGUAGE_AND_PROOFS.md) — 形式语言与形式证明（推理规则、操作语义、判定形式）
- [FORMAL_FULL_MODEL_EN_SUMMARY](./FORMAL_FULL_MODEL_EN_SUMMARY.md) — 英文摘要
- [PROOF_INDEX](./PROOF_INDEX.md) — 105+ 证明索引、按深度导航
- [INTERNATIONAL_FORMAL_VERIFICATION_INDEX](./INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md) — 国际对标
- [FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02](./FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md) — 批判性分析与推进计划

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14
