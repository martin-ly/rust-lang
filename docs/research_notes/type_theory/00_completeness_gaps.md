# 类型理论完备性缺口：形式化论证不充分声明

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ⚠️ **本目录形式化论证不充分；以下缺口待补全**

---

## 宗旨

本文档**明确承认** type_theory 目录下各文档的形式化论证**不完备**，并系统列出：

1. **Rust 1.93 类型系统特性**：未覆盖或仅部分覆盖
2. **组合法则**：缺失或未形式化
3. **Trait 特性**：未完备形式化

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
| **LUB coercion** | ❌ 未形式化 | 1.93 修正函数项、安全性；无类型规则 | type_system_foundations |
| **Copy 与 specialization** | ❌ 未形式化 | 1.93 移除 Copy 内部 specialization；生命周期影响无形式化 | type_system_foundations, variance |
| **const 中 &mut static** | ❌ 未形式化 | 1.93 允许 const 含 &mut static；const_item_interior_mutations lint 无形式化 | advanced_types |
| **offset_of!** | ❌ 未形式化 | 1.93 well-formed 检查；类型检查规则无形式化 | type_system_foundations |
| **impl Trait 捕获规则** | ⚠️ 部分 | async fn、impl Trait 捕获的精确规则未形式化 | trait_system_formalization |
| **never_type (!) 严格化** | ⚠️ 部分 | 1.92+ Lint 严格化；与 ⊥ 对应未充分论证 | type_system_foundations |
| **deref_nullptr deny** | ❌ 未形式化 | 1.93 deny-by-default；与类型系统衔接未形式化 | - |

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
| **Trait coherence（一致性）** | ⚠️ 部分 | 孤儿规则、重叠规则有描述；**无形式化定理**证明「任意 (Trait, Type) 至多一个 impl」 | trait_system_formalization |
| **Orphan rule 放宽** | ❌ 未覆盖 | 2024 放宽孤儿规则倡议；实验性变更未见形式化 | trait_system_formalization |
| **negative impls** | ❌ 未形式化 | `impl !Trait for T` 的语义、与 coherence 的交互 | trait_system_formalization |
| **类型与生命周期组合** | ⚠️ 部分 | `&'a T` 组合规则有；**泛型+生命周期+型变**三元组合的传递律未形式化 | lifetime_formalization, variance_theory |
| **Trait + 泛型 + GAT 组合** | ❌ 未形式化 | `impl<T> Trait for Vec<T>` 与 GAT 组合；解析优先级无形式化 | trait_system_formalization, advanced_types |
| **impl Trait 与 dyn Trait 组合** | ⚠️ 部分 | 两者可组合；**何时可互相替换**的边界未形式化 | trait_system_formalization |
| **const 泛型与类型组合** | ⚠️ 部分 | `[T; N]` 有；**const 表达式求值失败**时的类型错误规则未形式化 | advanced_types |

---

## 3. Trait 特性缺口

| Trait 特性 | 状态 | 缺口说明 | 应补充 |
| :--- | :--- | :--- | :--- |
| **对象安全完整规则** | ⚠️ 部分 | 有方法列表；**未来兼容性**（如 RPITIT）对对象安全的影响未形式化 | trait_system_formalization |
| **RPITIT (Return Position Impl Trait In Trait)** | ❌ 未形式化 | 1.93 稳定化；Trait 方法返回 impl Trait 的语义 | trait_system_formalization |
| **async fn in trait** | ❌ 未形式化 | 异步 Trait 方法的类型、Send 边界 | trait_system_formalization |
| **Trait 继承传递** | ⚠️ 部分 | `trait B: A` 有；**菱形继承**（trait D: B, C; B: A; C: A）的解析未形式化 | trait_system_formalization |
| **specialization** | ❌ 未形式化 | 不稳定； overlapping impl 的规则、与 coherence 的关系 | trait_system_formalization |
| **fundamental 类型** | ❌ 未形式化 | `#[fundamental]` 对孤儿规则的例外；RFC 1023 | trait_system_formalization |
| **blanket impl 冲突** | ⚠️ 部分 | 有反例；**冲突检测算法**无形式化 | trait_system_formalization |
| **Trait 方法默认参数** | ❌ 未覆盖 | 若稳定化；与 impl 解析的交互 | - |

---

## 4. 类型系统特性缺口

| 特性 | 状态 | 缺口说明 | 应补充 |
| :--- | :--- | :--- | :--- |
| **类型推断歧义** | ⚠️ 部分 | 报错有；**何时可消除歧义**的规则未形式化 | type_system_foundations |
| **类型 ascription** | ❌ 未形式化 | `e: T` 的语义、与推断的交互 | type_system_foundations |
| **unsized 类型** | ⚠️ 部分 | `?Sized` 有；**DST 的完整类型规则**未形式化 | type_system_foundations |
| **existential type** | ❌ 未形式化 | 不稳定；存在类型的类型论对应 | advanced_types |
| **higher-ranked trait bounds** | ⚠️ 部分 | `for<'a> T: Trait<'a>` 有描述；**与生命周期推断**的交互未形式化 | lifetime_formalization, trait_system_formalization |
| **newtype 与零成本** | ❌ 未形式化 | 结构体包装零成本；**repr(transparent)** 的形式化 | - |

---

## 5. 缺口汇总与优先级

```text
高优先级（影响类型安全论证）
├── Trait coherence 形式化定理
├── 孤儿规则、negative impls
├── LUB coercion、Copy specialization 移除
└── RPITIT、async fn in trait

中优先级（影响组合论证）
├── 类型+生命周期+型变 三元组合
├── impl Trait 与 dyn 边界
└── const 泛型求值失败规则

低优先级（扩展覆盖）
├── offset_of!、const &mut static
├── fundamental、specialization
└── existential type
```

---

## 6. 与已有文档的衔接

| 文档 | 已覆盖 | 缺口所在 |
| :--- | :--- | :--- |
| [type_system_foundations](type_system_foundations.md) | 进展性、保持性、类型安全 T1–T3 | LUB、Copy、offset_of!、类型推断歧义 |
| [trait_system_formalization](trait_system_formalization.md) | 对象安全、impl 解析、coherence 描述 | coherence 定理、RPITIT、async fn、孤儿放宽 |
| [lifetime_formalization](lifetime_formalization.md) | outlives、引用有效性 | 与型变、泛型组合 |
| [advanced_types](advanced_types.md) | GAT、const 泛型 | const 求值失败、existential |
| [variance_theory](variance_theory.md) | 协变/逆变/不变 T1–T4 | 与 Copy 变更、组合传递 |

---

## 7. 补全路线图

| 阶段 | 目标 | 产出 |
| :--- | :--- | :--- |
| 阶段 1 | Trait coherence 形式化 | 定理 COH-T1：至多一个 impl；证明思路 |
| 阶段 2 | Rust 1.93 类型变更 | LUB、Copy、const 的形式化 |
| 阶段 3 | 组合法则 | 类型+生命周期+型变 传递定理 |
| 阶段 4 | RPITIT、async fn in trait | 新增章节或 advanced_types 扩展 |

---

## 引用

- [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](../RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) — 92 项特性；类型相关需与本缺口对照
- [ARGUMENTATION_GAP_INDEX](../ARGUMENTATION_GAP_INDEX.md) — 论证缺口追踪
- [RFC 1023 Rebalancing Coherence](https://rust-lang.github.io/rfcs/1023-rebalancing-coherence.html)
- [Relaxing the Orphan Rule (2024)](https://rust-lang.github.io/rust-project-goals/2024h2/Relaxing-the-Orphan-Rule.html)
