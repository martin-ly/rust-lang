# 类型系统构造能力

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-12
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **目标**: 系统梳理 Rust 类型系统的「构造能力」维度：哪些类型可构造、用何种语法、构造路径是否唯一；建立类型构造确定性判定树

---

## 📊 目录

- [类型系统构造能力](#类型系统构造能力)
  - [📊 目录](#-目录)
  - [文档宗旨](#文档宗旨)
  - [形式化定义](#形式化定义)
  - [TCON 矩阵](#tcon-矩阵)
  - [Rust 1.93 新增类型/表达式](#rust-193-新增类型表达式)
  - [类型理论缺口对构造能力的影响](#类型理论缺口对构造能力的影响)
  - [类型构造决策树](#类型构造决策树)
  - [确定性判定](#确定性判定)
  - [与已有证明衔接](#与已有证明衔接)
  - [相关文档](#相关文档)

---

## 文档宗旨

本文档填补「类型构造能力」缺口：

1. **构造能力**：哪些类型可构造、用何种语法、构造路径是否唯一
2. **类型构造确定性判定**：何时可推断、何时需注解、何时必然失败
3. **类型构造能力形式化树图**：按基本类型/复合类型/泛型/关联类型/GAT 等分层的决策树

---

## 形式化定义

**Def TCON1（类型构造能力）**：

设 $\mathcal{T}$ 为 Rust 类型集合，$\mathcal{C}$ 为类型构造路径集合。类型的**构造能力**由以下三元组定义：

$$\mathrm{TCON}(\tau) = (\mathit{Syntax}(\tau), \mathit{Constraints}(\tau), \mathit{Determinism}(\tau))$$

其中：

- $\mathit{Syntax}(\tau)$：构造 $\tau$ 的语法形式（字面量、构造子、泛型实例化等）
- $\mathit{Constraints}(\tau)$：构造 $\tau$ 时需满足的约束（Trait、生命周期、const 等）
- $\mathit{Determinism}(\tau) \in \{\mathrm{Unique}, \mathrm{Multi}, \mathrm{Impossible}\}$：唯一可构造、多解、不可构造

**Axiom TCON1**：基本类型（`i32`、`bool`、`char` 等）的构造能力为 Unique；字面量唯一确定类型。

**Axiom TCON2**：复合类型（struct、enum、tuple）的构造能力由各字段类型的构造能力组合决定；若所有字段 Unique，则整体 Unique；若存在歧义字段，则 Multi 或需显式注解。

**定理 TCON-T1（构造与类型安全）**：若 $\tau$ 可构造（$\mathit{Determinism}(\tau) \neq \mathrm{Impossible}$），则构造出的值 $v$ 满足 $\Gamma \vdash v : \tau$（由 [type_system_foundations](type_system_foundations.md) 保持性 T2）。

*证明*：由 [type_system_foundations](type_system_foundations.md) 定理 2（保持性）；构造即求值，求值后类型保持。∎

---

## TCON 矩阵

类型族 × 构造方式 × 确定性

| 类型族 | 构造方式 | 确定性 | 说明 |
| :--- | :--- | :--- | :--- |
| **基本类型** | 字面量 `42`、`true`、`'a'` | Unique | 编译器直接推断 |
| **元组** | `(a, b)`、`()` | Unique（若各分量可推断） | 局部推断；歧义时需 `: (i32, bool)` |
| **结构体** | `S { x: 1, y: 2 }` | Unique（若字段不歧义） | 缺字段或歧义需注解 |
| **枚举** | `E::Variant(a)` | Unique（若变体与参数可推断） | Option/Result 常用 |
| **数组** | `[1, 2, 3]`、`[0; N]` | Unique（元素类型可推断） | `[T; N]` 中 N 需 const |
| **切片** | `&[a, b]`、`v.as_slice()` | Unique | 借用或方法产生 |
| **引用** | `&x`、`&mut x` | Unique | 生命周期由 NLL 推断 |
| **Box** | `Box::new(x)` | Unique | 单态化 |
| **泛型** | `Vec::new()`、`F::<i32>::new()` | Multi（多 impl）或 Unique（约束唯一） | 歧义 impl 需 turbofish |
| **impl Trait** | 返回值、参数 | Unique（调用处推断） | 存在类型，静态分发 |
| **dyn Trait** | `&x as &dyn T`、`Box::new(x)` | Unique（目标 Trait 唯一） | 对象安全约束 |
| **函数项** | `f`、`g::<i32>` | Unique 或 Multi | 重载时需 turbofish |
| **闭包** | `\|x\| x + 1` | Unique（使用处推断） | 唯一匿名类型 |
| **Never (!)** | 不可达、`panic!`、`loop {}` | Unique | 无构造子 |
| **关联类型** | `T::Item` | Unique（impl 唯一） | coherence 保证 |
| **GAT** | `T::Item<'a>` | Unique（约束唯一） | 见 [advanced_types](advanced_types.md) |
| **const 泛型** | `[T; N]` 其中 `const N` | Unique（N 为 const 表达式） | 见 [advanced_types](advanced_types.md) |

---

## Rust 1.93 新增类型/表达式

以下 Rust 1.93 新增或变更的特性影响类型构造能力；详见 [07_rust_1.93_full_changelog](../../06_toolchain/07_rust_1.93_full_changelog.md)、[00_completeness_gaps](00_completeness_gaps.md)。

| 特性 | 构造方式 | 确定性 | 说明 |
| :--- | :--- | :--- | :--- |
| **LUB coercion** | 函数项、多分支匹配 | Unique（修正后） | 1.93 修正 LUB 推断；函数项类型推断更正确 |
| **Copy specialization 移除** | Copy 类型 | Unique | 1.93 不再内部 specialization；Copy 与 Clone 构造路径显式 |
| **const 中 &mut static** | const 上下文 | Unique（受限） | 1.93 允许 const 含 `&mut static`；`const_item_interior_mutations` lint |
| **offset_of!** | 类型检查 | - | 1.93 well-formed 检查；非法类型构造失败 |
| **deref_nullptr deny** | 裸指针解引用 | - | 1.93 deny-by-default；解引用空指针必然失败 |
| **MaybeUninit API** | assume_init_ref/mut、write_copy_of_slice | Unique（契约满足时） | 1.93 新增方法；构造路径更丰富 |
| **never_type (!) 严格化** | `panic!`、`loop {}` | Unique | 1.92+ 与 ⊥ 对应；构造子更明确 |

---

## 类型理论缺口对构造能力的影响

[00_completeness_gaps](00_completeness_gaps.md) 中 ⚠️ 部分缺口可能影响类型构造路径；本表标注其对 TCON 的影响。

| 缺口 | 影响构造路径 | 说明 |
| :--- | :--- | :--- |
| **impl Trait 捕获规则** | 可能 Multi | async fn、impl Trait 捕获的精确规则未完全形式化；歧义时需显式注解 |
| **Trait 继承菱形** | 可能 Multi | trait D: B, C; B: A; C: A 的解析未形式化；`T::Item` 可能歧义 |
| **DST 规则** | 部分 Impossible | `?Sized` 有；DST 的完整类型规则未形式化；某些 DST 构造路径可能失败 |
| **类型推断歧义** | Multi | 报错有；何时可消除歧义的规则未形式化；需 turbofish 或 ascription |
| **对象安全完整规则** | 可能 Impossible | dyn Trait 构造需对象安全；完整规则未形式化；边界情况可能编译失败 |

---

## 类型构造决策树

给定目标类型 → 构造路径选择

```text
目标类型是什么？
├── 基本类型 (i32, bool, char, str, ...)
│   └── 使用字面量或常量；确定性 Unique
├── 元组 (T1, T2, ...) 或 ()
│   └── 直接构造 (a, b) 或 ()；各分量可推断则 Unique
├── 结构体 struct S { ... }
│   ├── 有 Default? → 使用 S::default() 或 Default::default()
│   └── 无 → 必须显式 S { f1: v1, ... }；缺字段则需注解
├── 枚举 enum E { ... }
│   └── 使用变体 E::V(a, b)；变体与参数类型可推断则 Unique
├── 容器 Vec<T>, Option<T>, Result<T,E>
│   ├── Vec → Vec::new(), vec![], Vec::from_iter()
│   ├── Option → Some(x), None
│   └── Result → Ok(x), Err(e)
├── 引用 &T, &mut T
│   └── &x, &mut x；生命周期 NLL 推断
├── 泛型 F<T>
│   ├── 约束唯一？ → 直接调用 F::new() 等
│   └── 歧义？ → turbofish F::<T>::new()
├── impl Trait / dyn Trait
│   ├── impl Trait → 返回值；调用处推断
│   └── dyn Trait → 转换 &x as &dyn T；需对象安全
├── 关联类型 T::Item
│   └── 在 impl 内或约束内；coherence 保证唯一
├── GAT T::Item<'a>
│   └── 约束确定生命周期；见 advanced_types
└── Never (!)
    └── panic!、loop {}、发散；无构造子
```

---

## 确定性判定

| 情形 | 确定性 | 处理 |
| :--- | :--- | :--- |
| **可局部推断** | Unique | 无需注解 |
| **歧义 impl** | Multi | 需 turbofish 或显式类型注解 |
| **生命周期不足** | 不可推断 | 需显式生命周期标注 |
| **类型变量未约束** | Multi 或 Impossible | 添加约束或注解 |
| **overflow / 默认推断** | 可能 Multi | 如 `42` 默认 i32；后缀 `42u64` 指定 |
| **闭包类型** | Unique | 由使用处唯一确定 |
| **dyn Trait** | Unique | 目标 Trait 唯一；需对象安全 |

**引理 TCON-L1（推断失败可判定）**：若类型检查器报错「类型无法推断」或「歧义」，则 $\mathit{Determinism}(\tau) \in \{\mathrm{Multi}, \mathrm{Impossible}\}$；添加适当注解可提升为 Unique。

*证明*：由 [type_system_foundations](type_system_foundations.md) 类型推导算法；约束不足则多解或无解；显式注解等价于添加约束。∎

**推论 TCON-C1**：所有 Safe Rust 良型程序，其类型构造路径在添加必要注解后均可判定为 Unique。

---

## 与已有证明衔接

| 文档 | 衔接点 |
| :--- | :--- |
| [type_system_foundations](type_system_foundations.md) | 类型环境、类型判断、进展性 T1、保持性 T2；构造即求值 |
| [trait_system_formalization](trait_system_formalization.md) | impl Trait、dyn Trait、关联类型、GAT；coherence、对象安全 |
| [advanced_types](advanced_types.md) | GAT、const 泛型、impl Trait 捕获规则 |
| [variance_theory](variance_theory.md) | 型变影响子类型；某些构造路径受型变约束 |
| [00_completeness_gaps](00_completeness_gaps.md) | LUB coercion、Copy specialization 等 1.93 构造相关缺口 |

---

## 相关文档

| 文档 | 用途 |
| :--- | :--- |
| [type_system_foundations](type_system_foundations.md) | 类型系统基础、类型安全定理 |
| [trait_system_formalization](trait_system_formalization.md) | Trait、泛型、impl/dyn |
| [advanced_types](advanced_types.md) | GAT、const 泛型 |
| [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](../RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) | 92 项特性与类型族对应 |
| [UNIFIED_SYSTEMATIC_FRAMEWORK](../UNIFIED_SYSTEMATIC_FRAMEWORK.md) | 全局矩阵与决策树索引 |

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-12
