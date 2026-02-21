# 类型理论完备性缺口：形式化论证不充分声明

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-20
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 📊 目录

- [类型理论完备性缺口：形式化论证不充分声明](#类型理论完备性缺口形式化论证不充分声明)
  - [📊 目录](#-目录)
  - [宗旨](#宗旨)
  - [形式化定义（完备性缺口）](#形式化定义完备性缺口)
  - [1. Rust 1.93 类型系统特性缺口](#1-rust-193-类型系统特性缺口)
  - [2. 组合法则缺口](#2-组合法则缺口)
    - [2.1 已有组合法则（形式化程度）](#21-已有组合法则形式化程度)
    - [2.2 组合法则缺口](#22-组合法则缺口)
  - [3. Trait 特性缺口](#3-trait-特性缺口)
  - [4. 类型系统特性缺口](#4-类型系统特性缺口)
  - [5. 缺口汇总与优先级](#5-缺口汇总与优先级)
  - [6. 与已有文档的衔接](#6-与已有文档的衔接)
  - [7. 补全路线图](#7-补全路线图)
  - [引用](#引用)
  - [8. 国际对标缺口（与阶段 1 交付物联动）](#8-国际对标缺口与阶段-1-交付物联动)

## 宗旨

本文档系统列出 type_theory 目录的形式化论证缺口与补全状态：

1. **Rust 1.93 类型系统特性**：高/中优先级已补全；部分低优先级已补全（offset_of!、never_type、type ascription）
2. **组合法则**：核心组合法则已形式化（coherence、VAR-COM、impl/dyn、const 求值失败）
3. **Trait 特性**：RPITIT、async fn、negative impls 等已补全；fundamental、specialization 为扩展缺口

---

## 形式化定义（完备性缺口）

**Def CGI（完备性缺口）**：设 $\mathcal{F}$ 为某领域的形式化文档集。若存在概念 $C$、规则 $R$ 或特性 $F$ 在 Rust 语言规范中存在，但 $\mathcal{F}$ 中无对应 Def/Axiom/Theorem 或证明，则称 $\mathcal{F}$ 对 $C/R/F$ 存在**完备性缺口**。

**Axiom CGI1**：Rust 类型系统与 Trait 系统处于持续演进；形式化文档滞后于语言实现；本目录不声称覆盖全部。

**定理 CGI-T1（不完备性）**：$\mathcal{T} = \{\text{type\_system},\, \text{trait},\, \text{lifetime},\, \text{advanced},\, \text{variance}\}$ 对 Rust 1.93 类型系统**不完备**；存在下述缺口。

*证明*：由下列各节所列缺口；每项缺口均为 Def CGI 的实例。∎

---

## 1. Rust 1.93 类型系统特性缺口

| 特性 | 状态 | 缺口说明 | 应补充文档 |
| :--- | :--- | :--- | :--- |
| **LUB coercion** | ✅ 已补全 | Def LUB1、定理 LUB-T1；[type_system_foundations](type_system_foundations.md) | type_system_foundations |
| **Copy 与 specialization** | ✅ 已补全 | Def COP1、定理 COP-T1；1.93 移除内部 specialization；[type_system_foundations](type_system_foundations.md) | type_system_foundations, variance |
| **const 中 &mut static** | ⚠️ 部分 | Def CONST-MUT1；1.93 允许 const 含 &mut static；lint 规则；[advanced_types](advanced_types.md) | advanced_types |
| **offset_of!** | ✅ 已补全 | Def OFFSET1、定理 OFFSET-T1；[type_system_foundations](type_system_foundations.md) | type_system_foundations |
| **impl Trait 捕获规则** | ⚠️ 部分 | async fn、impl Trait 捕获的精确规则；RPITIT/ASYNC-T1 已覆盖 Trait 内语义 | trait_system_formalization |
| **never_type (!) 严格化** | ✅ 已补全 | Def BOT1、定理 BOT-T1；1.92+ 与 ⊥ 对应；[type_system_foundations](type_system_foundations.md) | type_system_foundations |
| **deref_nullptr deny** | ⚠️ 部分 | Def DEREF-NULL1；1.93 deny-by-default；[type_system_foundations](type_system_foundations.md) | type_system_foundations |

**对类型构造能力的影响**：上述 ⚠️ 缺口可能影响 [construction_capability](construction_capability.md) 中的构造路径判定。impl Trait 捕获、Trait 继承菱形、DST 规则、类型推断歧义、对象安全完整规则 → 见 [construction_capability § 类型理论缺口对构造能力的影响](construction_capability.md#类型理论缺口对构造能力的影响)。

---

## 2. 组合法则缺口

**组合法则**：类型、Trait、生命周期等如何组合的规则；组合后性质如何保持。

### 2.1 已有组合法则（形式化程度）

| 法则 | 形式化程度 | 文档 |
| :--- | :--- | :--- |
| 型变传递 | ✅ 有 Def、Theorem | variance_theory T1–T4 |
| 生命周期 outlives | ✅ 有 Def、Theorem | lifetime_formalization |
| 泛型单态化 | ⚠️ 有描述 | type_system_foundations |
| Trait 约束传播 | ⚠️ 有描述 | trait_system_formalization |

### 2.2 组合法则缺口

| 组合法则 | 状态 | 缺口说明 | 应补充 |
| :--- | :--- | :--- | :--- |
| **Trait coherence（一致性）** | ✅ 已补全 | Axiom COH1/COH2、定理 COH-T1：至多一个 impl；证明思路见 [trait_system_formalization](trait_system_formalization.md) | trait_system_formalization |
| **Orphan rule 放宽** | ⚠️ 部分 | Def ORPH1、ORPH-RELAX1；当前规则已形式化；2024 放宽为倡议未稳定 | trait_system_formalization |
| **negative impls** | ✅ 已补全 | Def NEG1、Axiom NEG1、定理 NEG-T1；[trait_system_formalization](trait_system_formalization.md) | trait_system_formalization |
| **类型与生命周期组合** | ✅ 已补全 | 定理 VAR-COM-T1、推论 VAR-COM-C1（[variance_theory](variance_theory.md)） | variance_theory |
| **Trait + 泛型 + GAT 组合** | ⚠️ 部分 | Def TRAIT-GAT1；解析优先级、与 AT-L1 衔接；[trait_system_formalization](trait_system_formalization.md) | trait_system_formalization, advanced_types |
| **impl Trait 与 dyn Trait 组合** | ✅ 已补全 | Def DYN-IMPL1、定理 DYN-T1、推论 DYN-C1；[trait_system_formalization](trait_system_formalization.md) | trait_system_formalization |
| **const 泛型与类型组合** | ✅ 已补全 | Def CONST-EVAL1、定理 CONST-EVAL-T1；[advanced_types](advanced_types.md) | advanced_types |

---

## 3. Trait 特性缺口

| Trait 特性 | 状态 | 缺口说明 | 应补充 |
| :--- | :--- | :--- | :--- |
| **对象安全完整规则** | ⚠️ 部分 | 有方法列表；推论 RPIT-C1 覆盖 RPITIT 与 dyn 交互；其余未来兼容性未形式化 | trait_system_formalization |
| **RPITIT (Return Position Impl Trait In Trait)** | ✅ 已补全 | Def RPIT1、定理 RPIT-T1、推论 RPIT-C1；[trait_system_formalization](trait_system_formalization.md) | trait_system_formalization |
| **async fn in trait** | ✅ 已补全 | Def ASYNC1、定理 ASYNC-T1（Send 边界）；[trait_system_formalization](trait_system_formalization.md) | trait_system_formalization |
| **Trait 继承传递** | ⚠️ 部分 | `trait B: A` 有；**菱形继承**（trait D: B, C; B: A; C: A）的解析未形式化 | trait_system_formalization |
| **specialization** | ⚠️ 部分 | Def SPEC1、定理 SPEC-T1；不稳定；[trait_system_formalization](trait_system_formalization.md) | trait_system_formalization |
| **fundamental 类型** | ⚠️ 部分 | Def FUND1；RFC 1023 孤儿规则例外；完整规则未形式化 | trait_system_formalization |
| **blanket impl 冲突** | ⚠️ 部分 | 有反例；**冲突检测算法**无形式化 | trait_system_formalization |
| **Trait 方法默认参数** | ❌ 未覆盖 | 若稳定化；与 impl 解析的交互 | - |

**对类型构造能力的影响**：对象安全、Trait 继承菱形、blanket impl 冲突 → 可能 Multi 或 Impossible；见 [construction_capability § 类型理论缺口](construction_capability.md#类型理论缺口对构造能力的影响)。

---

## 4. 类型系统特性缺口

| 特性 | 状态 | 缺口说明 | 应补充 |
| :--- | :--- | :--- | :--- |
| **类型推断歧义** | ⚠️ 部分 | 报错有；**何时可消除歧义**的规则未形式化 | type_system_foundations |
| **类型 ascription** | ✅ 已补全 | Def ASC1、定理 ASC-T1；[type_system_foundations](type_system_foundations.md) | type_system_foundations |
| **unsized 类型** | ⚠️ 部分 | `?Sized` 有；**DST 的完整类型规则**未形式化 | type_system_foundations |
| **existential type** | ⚠️ 部分 | Def EXIST1；不稳定；存在类型；[advanced_types](advanced_types.md) | advanced_types |
| **higher-ranked trait bounds** | ⚠️ 部分 | `for<'a> T: Trait<'a>` 有描述；**与生命周期推断**的交互未形式化 | lifetime_formalization, trait_system_formalization |
| **newtype 与零成本** | ⚠️ 部分 | Def NEWTYPE1、定理 NEWTYPE-T1；repr(transparent)；[type_system_foundations](type_system_foundations.md) | type_system_foundations |

**对类型构造能力的影响**：类型推断歧义、unsized 类型（DST）→ 可能 Multi 或 Impossible；见 [construction_capability](construction_capability.md)。

---

## 5. 缺口汇总与优先级

```text
高优先级（影响类型安全论证）
└── 孤儿规则放宽（倡议未稳定）

中优先级（影响组合论证）
└── 已全部补全 ✅

已补全（原高/中优先级）
├── Trait coherence（COH-T1）✅
├── LUB coercion、Copy specialization（LUB-T1、COP-T1）✅
├── 类型+生命周期+型变 三元组合（VAR-COM-T1）✅
├── RPITIT、async fn in trait（RPIT-T1、ASYNC-T1）✅
├── negative impls（NEG-T1）✅
├── impl Trait 与 dyn 边界（DYN-T1）✅
└── const 泛型求值失败（CONST-EVAL-T1）✅

低优先级（扩展覆盖）
├── offset_of!、never_type、type ascription ✅ 已补全
├── const &mut static、fundamental、specialization、existential、newtype、deref_nullptr、Trait+GAT ⚠️ 部分（Def 已补全）
└── Trait 方法默认参数（若稳定化）
```

---

## 6. 与已有文档的衔接

| 文档 | 已覆盖 | 缺口所在 |
| :--- | :--- | :--- |
| [type_system_foundations](type_system_foundations.md) | 进展性、保持性、类型安全 T1–T3、LUB、Copy、**OFFSET-T1**、**ASC-T1**、**BOT-T1**、**NEWTYPE-T1**、**DEREF-NULL1** | 类型推断歧义 |
| [trait_system_formalization](trait_system_formalization.md) | 对象安全、impl 解析、coherence、**COH-T1**、**RPIT-T1**、**ASYNC-T1**、**NEG-T1**、**DYN-T1**、**TRAIT-GAT1**、**SPEC-T1** | 孤儿放宽（倡议） |
| [lifetime_formalization](lifetime_formalization.md) | outlives、引用有效性 | 与型变、泛型组合 |
| [advanced_types](advanced_types.md) | GAT、const 泛型、**CONST-EVAL-T1**、**CONST-MUT1**、**EXIST1** | existential 完整规则 |
| [variance_theory](variance_theory.md) | 协变/逆变/不变 T1–T4 | 与 Copy 变更、组合传递 |

---

## 7. 补全路线图

| 阶段 | 目标 | 产出 |
| :--- | :--- | :--- |
| 阶段 1 | Trait coherence 形式化 | ✅ 定理 COH-T1、Axiom COH1/COH2、推论 COH-C1 已补全 |
| 阶段 2 | Rust 1.93 类型变更 | ✅ Def LUB1/COP1、定理 LUB-T1/COP-T1 已补全（type_system_foundations） |
| 阶段 3 | 组合法则 | ✅ 定理 VAR-COM-T1、推论 VAR-COM-C1 已补全（variance_theory） |
| 阶段 4 | RPITIT、async fn in trait | ✅ Def RPIT1/ASYNC1、定理 RPIT-T1/ASYNC-T1、推论 RPIT-C1 已补全（trait_system_formalization） |
| 阶段 5 | 孤儿规则、negative impls、impl/dyn 边界、const 求值失败 | ✅ Def ORPH1/NEG1/DYN-IMPL1/CONST-EVAL1、定理 NEG-T1/DYN-T1/CONST-EVAL-T1 已补全 |
| 阶段 6 | 低优先级扩展 | ✅ Def OFFSET1/ASC1/BOT1、定理 OFFSET-T1/ASC-T1/BOT-T1 已补全（type_system_foundations） |
| 阶段 7 | 剩余缺口 Def 占位 | ✅ Def NEWTYPE1/DEREF-NULL1/CONST-MUT1/EXIST1/TRAIT-GAT1/SPEC1；定理 NEWTYPE-T1/SPEC-T1 |

---

## 引用

- [construction_capability](construction_capability.md) — 类型构造能力；§ 类型理论缺口对构造能力的影响 与本缺口对应
- [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](../RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) — 92 项特性；类型相关需与本缺口对照
- [ARGUMENTATION_GAP_INDEX](../ARGUMENTATION_GAP_INDEX.md) — 论证缺口追踪
- [RFC 1023 Rebalancing Coherence](https://rust-lang.github.io/rfcs/1023-rebalancing-coherence.html)
- [Relaxing the Orphan Rule (2024)](https://rust-lang.github.io/rust-project-goals/2024h2/Relaxing-the-Orphan-Rule.html)

---

## 8. 国际对标缺口（与阶段 1 交付物联动）

**详见**: [INTERNATIONAL_FORMAL_VERIFICATION_INDEX](../INTERNATIONAL_FORMAL_VERIFICATION_INDEX.md)、[FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02](../FORMAL_PROOF_CRITICAL_ANALYSIS_AND_PLAN_2026_02.md)

| 缺口类型 | 说明 | 对标成果 |
| :--- | :--- | :--- |
| **L3 机器可检查证明** | 类型系统 T-TY3 骨架已创建（[TYPE_SAFETY.v](../coq_skeleton/TYPE_SAFETY.v)，证明 Admitted 待补全）；T-OW2/T-BR1 骨架见 [coq_skeleton](../coq_skeleton/) | RustBelt、Aeneas |
| **范畴论对应** | 指称语义与类型论（Fω、System F）的范畴论对应未形式化 | 学术前沿 |
| **工具对接** | 无 Aeneas、coq-of-rust 对接 | [AENEAS_INTEGRATION_PLAN](../AENEAS_INTEGRATION_PLAN.md)、[COQ_OF_RUST_INTEGRATION_PLAN](../COQ_OF_RUST_INTEGRATION_PLAN.md) |
