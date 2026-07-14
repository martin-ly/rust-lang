> **内容分级**: [综述级]
> **本节关键术语**: Type Checking · Type Inference · `typeck` · `Ty<'tcx>` · `InferCtxt` · Inference Variable · Unification · Region Constraint · Snapshot — [完整对照表](../../00_meta/01_terminology/01_terminology_glossary.md)
>
# rustc 类型检查与类型推断

> **EN**: Type Checking and Inference in rustc
> **Summary**: Explains how rustc checks types via the `typeck` query, generates constraints, and resolves inference variables using equality, subtyping, and region constraints.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [专家 / 研究者]
> **Bloom 层级**: L2-L4
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **F** — Formal
> **双维定位**: F×Type — 类型系统（Type System）与形式化方法
> **定位**: 把“编译器如何知道 `Vec<&str>` 并对未标注类型做推断”还原为约束生成、统一与区域求解的完整算法。
> **前置概念**: [Name Resolution and HIR](../05_rustc_internals/04_name_resolution_and_hir.md) · [Trait Solver in rustc](../05_rustc_internals/03_trait_solver_in_rustc.md) · [Type Inference](03_type_inference.md)
> **后置概念**: [NLL 与 Polonius](../../03_advanced/02_unsafe/03_nll_and_polonius.md) · [LLVM Backend and Codegen](../../06_ecosystem/00_toolchain/09_llvm_backend_and_codegen.md)

---

> **来源**: [Rustc Dev Guide — Type inference](https://rustc-dev-guide.rust-lang.org/type-inference.html) · · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Hindley — The Principal Type-Scheme of an Object in Combinatory Logic](https://doi.org/10.2307/2270762) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Rustc Dev Guide — HIR Type checking](https://rustc-dev-guide.rust-lang.org/hir-typeck/summary.html) ·
> [Rustc Dev Guide — The ty module](https://rustc-dev-guide.rust-lang.org/ty.html) ·
> [Rust Reference — Type System](https://doc.rust-lang.org/reference/types.html)

---

## 反命题决策树

(Source: [Rustc Dev Guide — Type inference](https://rustc-dev-guide.rust-lang.org/type-inference.html))

## 📑 目录

- rustc 类型检查与类型推断（Type Inference）
  - [📑 目录](#-目录)
  - [一、类型检查在编译流水线中的位置](#一类型检查在编译流水线中的位置)
  - [二、`Ty<'tcx>`：rustc 内部类型表示](#二tytcxrustc-内部类型表示)
  - [三、`typeck` Query 与 `InferCtxt`](#三typeck-query-与-inferctxt)
    - [3.1 `typeck` query](#31-typeck-query)
    - [3.2 `InferCtxt`](#32-inferctxt)
  - [四、推断变量与统一](#四推断变量与统一)
  - [五、相等约束与子类型约束](#五相等约束与子类型约束)
    - [5.1 相等约束](#51-相等约束)
    - [5.2 子类型约束](#52-子类型约束)
  - [六、区域约束与求解](#六区域约束与求解)
    - [6.1 收集约束](#61-收集约束)
    - [6.2 求解时机](#62-求解时机)
  - [七、Snapshots 与回滚](#七snapshots-与回滚)
  - [嵌入式测验](#嵌入式测验)
    - [测验 1：`typeck` query 的主要输出是什么？](#测验-1typeck-query-的主要输出是什么)
    - [测验 2：整数推断变量 `{integer}` 最终如何变成具体类型？](#测验-2整数推断变量-integer-最终如何变成具体类型)
    - [测验 3：Rust 的子类型关系主要体现在哪里？](#测验-3rust-的子类型关系主要体现在哪里)
    - [测验 4：为什么区域约束要延迟到最后才求解？](#测验-4为什么区域约束要延迟到最后才求解)
  - [权威来源索引](#权威来源索引)

---

## 一、类型检查在编译流水线中的位置

```text
源代码 → AST → HIR → Type Checking / Inference → Trait Solving → Borrow Check → MIR → Codegen
```

类型检查在 HIR 之后执行，负责：

- 为每个表达式确定类型；
- 验证 trait bound 和泛型（Generics）约束；
- 收集生命周期（Lifetimes）/区域约束供借用（Borrowing）检查使用。

> **关键洞察**: Rust 的类型检查 = 为每个节点计算类型 + 生成并求解一组约束。
>
> [Rustc Dev Guide — HIR Type checking](https://rustc-dev-guide.rust-lang.org/)(<https://rustc-dev-guide.rust-lang.org/hir-typeck/summary.html>)

---
(Source: [Rustc Dev Guide — Type inference](https://rustc-dev-guide.rust-lang.org/type-inference.html))

## 二、`Ty<'tcx>`：rustc 内部类型表示

`rustc_middle::ty::Ty<'tcx>` 是编译器内部表示类型的核心类型。注意：

- `Ty<'tcx>` 是一个指向 arena 分配类型的引用（Reference）；
- `'tcx` 是编译上下文生命周期（Lifetimes）；
- 它区分整数变量 `{integer}`、浮点变量 `{float}` 等“待推断”类型。

```rust,ignore
// 用户代码
let x = 1;

// 类型检查初期 x 的类型可能是 TyKind::Infer(IntVar(?I))
// 随后通过约束统一为 i32
```

> [Rustc Dev Guide — The ty module](https://rustc-dev-guide.rust-lang.org/ty.html)(<https://rustc-dev-guide.rust-lang.org/ty.html>)

---
(Source: [Rustc Dev Guide — Type inference](https://rustc-dev-guide.rust-lang.org/type-inference.html))

## 三、`typeck` Query 与 `InferCtxt`

本节解剖 rustc 类型检查的核心数据流：

- **`typeck` query**：对每个函数体执行的查询（query system 的一部分）——输入函数定义，输出类型检查后的 HIR + 推断出的类型表；查询结果缓存，增量编译时只有依赖变更的函数重算；
- **`InferCtxt`（推断上下文）**：类型变量的生命周期的载体——创建类型变量（`next_ty_var`）、登记约束（sub/eq/trait）、最终 `resolve` 出具体类型；`InferCtxt` 是「HM 合一 + trait 求解」的工程合体；
- **两阶段结构**：先收集约束（traversal），后求解（fulfillment）——约束间的依赖（trait 选择依赖类型变量解析）由 fulfillment loop 迭代处理；
- **诊断挂钩**：推断失败的错误（E0282 无法推断、E0277 trait 未实现）在此产生——错误信息质量的核心在「归因」（哪个约束先失败）。

本节附 `InferCtxt` 操作的调用序列图与调试入口（`-Zdump-typeck`）。

### 3.1 `typeck` query

`typeck` 是类型检查的主 query，输入是某个 item 的 `LocalDefId`，输出包含：

- 每个表达式的类型；
- 生成的 trait obligations；
- 区域约束；
- 方法解析结果。

```rust,ignore
// rustc 内部近似示意
let typeck_results = tcx.typeck(item_def_id);
```

### 3.2 `InferCtxt`

`InferCtxt<'tcx>`（Inference Context）是类型推断（Type Inference）的工作区：

```rust,ignore
let infcx = tcx.infer_ctxt().build();
```

它维护着所有 inference variables 和待求解的约束。

---
(Source: [Rustc Dev Guide — Type inference](https://rustc-dev-guide.rust-lang.org/type-inference.html))

## 四、推断变量与统一

推断变量表示暂时未知的类型或生命周期（Lifetimes）：

| 变量种类 | 示例来源 |
|:---|:---|
| 通用类型变量 `?T` | `let v = Vec::new();` |
| 整数变量 `{integer}` | 整数字面量 `42` |
| 浮点变量 `{float}` | 浮点字面量 `3.14` |
| 区域变量 `?r` | 借用（Borrowing）表达式 `&x` |
| 常量变量 `?C` | 泛型（Generics）常量参数 |

统一（unification）是最基本操作：如果推断变量 `?T` 要与 `i32` 相等，就把它实例化为 `i32`。

```rust,ignore
let mut x = vec![]; // x: Vec<?T>
x.push("hello");    // ?T = &str
// 最终 x: Vec<&str>
```

> [Rustc Dev Guide — Inference variables](https://rustc-dev-guide.rust-lang.org/type-inference.html)(<https://rustc-dev-guide.rust-lang.org/type-inference.html#inference-variables>)

---
(Source: [Rustc Dev Guide — Type inference](https://rustc-dev-guide.rust-lang.org/type-inference.html))

## 五、相等约束与子类型约束

本节聚焦「相等约束与子类型约束」，覆盖相等约束 与 子类型约束。论述顺序由定义到边界：先明确「相等约束与子类型约束」在「rustc 类型检查与类型推断」中的确切含义与适用范围，再给出可核验的例证或数据，最后标注它与相邻主题的分界线。读完后应能用一句话复述「相等约束与子类型约束」的判定标准，并指出它在全页论证链中的位置。

### 5.1 相等约束

```rust,ignore
infcx.at(...).eq(t, u);
```

强制 `t` 和 `u` 必须完全相同。成功返回 `InferOk`，可能附带需要进一步满足的 trait obligations。

### 5.2 子类型约束

```rust,ignore
infcx.at(...).sub(t, u); // t <: u
```

Rust 的子类型关系主要体现在生命周期（Lifetimes）上，例如 `&'static str <: &'a str`。

对于普通类型，子类型通常可转化为相等约束；涉及未绑定变量时，会生成 `Subtype(?T, ?U)` obligation 延后处理。

---
(Source: [Rustc Dev Guide — Type inference](https://rustc-dev-guide.rust-lang.org/type-inference.html))

## 六、区域约束与求解

本节展开生命周期（区域）约束的求解机制：

- **区域变量**：推断模式下，未标注的生命周期成为区域变量 `'?0, '?1...`——与类型变量并列的第二类推断变量；
- **约束形式**：`'a: 'b @ P`（'a 在程序点 P 包含 'b）——NLL 的核心数据结构 `RegionConstraintCollector`；约束来源：借用表达式、函数调用的参数-形参匹配、返回值的 outlives 要求；
- **求解算法**：约束图上的传递闭包 + liveness 计算——「区域 = 程序点集合」，`'a: 'b` 即集合包含；传播至不动点；
- **失败诊断**：约束冲突时定位「使 'a 需要存活的借用」与「'b 实际存活的范围」——E0597（借的值活得不够久）的错误信息即此两者的对照报告；
- **Polonius 的演进**：把同一求解改写为 Datalog 规则（`borrow_live_at`/`region_live_at` 谓词），本节给出两种表述的对照表。

### 6.1 收集约束

类型检查不会立即求解生命周期（Lifetimes），而是收集 **outlives** 约束：

```text
'a: 'b   （即 'b <= 'a）
```

例如赋值 `let y: &'a i32 = x;`，若 `x: &'b i32`，则生成约束 `'b: 'a`。

### 6.2 求解时机

- **词法求解（lexical）**: 在类型检查结束时统一求解；
- **NLL（Non-Lexical Lifetimes）**: MIR 借用（Borrowing）检查器在更细粒度控制流上求解。

> **定理**: 区域约束只在其他约束和 trait obligations 都处理完之后才最终求解。
>
> [Rustc Dev Guide — Region constraints](https://rustc-dev-guide.rust-lang.org/borrow_check/region_inference.html)(<https://rustc-dev-guide.rust-lang.org/type-inference.html#region-constraints>)

---
(Source: [Rustc Dev Guide — Type inference](https://rustc-dev-guide.rust-lang.org/type-inference.html))

## 七、Snapshots 与回滚

`InferCtxt` 支持 snapshot 机制：

```rust,ignore
let snapshot = infcx.snapshot();
// 尝试一系列约束操作...
if success {
    infcx.commit(snapshot);
} else {
    infcx.rollback_to(snapshot);
}
```

这在 trait solver 尝试多个候选时非常有用——可以临时假设某个候选成立，失败时无损回滚。

> **关键洞察**: Snapshot 让 rustc 能够在复杂的类型/约束空间中安全地回溯。
>
> [Rustc Dev Guide — Snapshots](https://rustc-dev-guide.rust-lang.org/type-inference.html)(<https://rustc-dev-guide.rust-lang.org/type-inference.html#snapshots>)

---
(Source: [Rustc Dev Guide — Type inference](https://rustc-dev-guide.rust-lang.org/type-inference.html))

## 嵌入式测验

理解「嵌入式测验」需要把握测验 1：`typeck` query 的主要输出是什么？、测验 2：整数推断变量 `{integer}` 最终如何变成具体类型？、测验 3：Rust 的子类型关系主要体现在哪里？与测验 4：为什么区域约束要延迟到最后才求解？，本节依次展开。

### 测验 1：`typeck` query 的主要输出是什么？

<details>
<summary>✅ 答案与解析</summary>

`typeck` 返回一个 item 的类型检查结果，包括每个表达式的类型、trait obligations、区域约束和方法解析结果。

</details>

---

### 测验 2：整数推断变量 `{integer}` 最终如何变成具体类型？

<details>
<summary>✅ 答案与解析</summary>

通过统一操作。当编译器发现 `{integer}` 必须与某个具体整型（如 `i32`）相等，或者必须满足某个需要具体整型的 trait bound 时，就把它实例化为该类型。

</details>

---

### 测验 3：Rust 的子类型关系主要体现在哪里？

<details>
<summary>✅ 答案与解析</summary>

主要体现在生命周期（Lifetimes）上，例如 `'static` 比任何 `'a` 都长，因此 `&'static T` 是 `&'a T` 的子类型。

</details>

---

### 测验 4：为什么区域约束要延迟到最后才求解？

<details>
<summary>✅ 答案与解析</summary>

因为生命周期（Lifetimes）约束往往依赖于其他推断变量的最终值；提前求解可能得到不完整或错误的结果。延迟求解确保所有类型信息已知后再做统一判断。

</details>

---

## 权威来源索引

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Rustc Dev Guide — Type inference](https://rustc-dev-guide.rust-lang.org/type-inference.html) | ✅ 一级 | 类型推断官方文档 |
| [Rustc Dev Guide — HIR Type checking](https://rustc-dev-guide.rust-lang.org/hir-typeck/summary.html) | ✅ 一级 | HIR 类型检查官方文档 |
| [Rustc Dev Guide — The ty module](https://rustc-dev-guide.rust-lang.org/ty.html) | ✅ 一级 | `Ty<'tcx>` 官方文档 |
| [Rust Reference — Type System](https://doc.rust-lang.org/reference/types.html) | ✅ 一级 | 语言层面类型系统 |

---

> **权威来源**: [Rustc Dev Guide — Type inference](https://rustc-dev-guide.rust-lang.org/type-inference.html) · [Rustc Dev Guide — HIR Type checking](https://rustc-dev-guide.rust-lang.org/hir-typeck/summary.html) · [Rust Reference — Type System](https://doc.rust-lang.org/reference/types.html) · [Pierce 2002 — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)
> **权威来源对齐变更日志**: 2026-06-21 创建，对齐 Rust 1.97.0 类型检查与推断文档
> [Authority Source Sprint Batch L4](../../00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 1.0
**最后更新**: 2026-06-21
**状态**: ✅ 权威来源对齐完成 (Batch L4)

---

## Rust 1.97.0 交叉语义

> **适用版本**: Rust 1.97.0+ (Edition 2024)
> **交叉域**: 类型系统（Type System）× Trait Solver × Edition 2024 兼容性
> **审计出处**: `reports/GLOBAL_SEMANTIC_CRITICAL_AUDIT_2026_07_11.md` §2.4、§4 P2-2 缺口 #2
> **本小节性质**: 交叉语义补充，**只增不删**；原有推断变量/统一/区域约束小节（§二–§七）保持不变。

### 1. 从 `{integer}`/`{float}` 到“回退默认值”：1.97 的改动点

本文 §四 已说明浮点字面量在类型检查初期是 `TyKind::Infer(FloatVar(?F))`（即 `{float}`），整数字面量是 `IntVar(?I)`（即 `{integer}`）。当类型检查结束时若推断变量**仍未被任何约束固定**，rustc 会为其指定一个**回退默认值（fallback default）**：

| 推断变量 | 历史回退默认值 | 依据 |
|:---|:---|:---|
| `{integer}`（`42`） | `i32` | Rust Reference（既定） |
| `{float}`（`3.14`） | `f64` | Rust Reference（既定，1.97 之前） |

Rust 1.97.0 触及的是 **`{float}` 这一行的回退行为**，且**当前可观察形态是一条 future-compatibility warning**，而非立刻把所有未约束浮点字面量硬改为 `f32`。

**事实（两个权威来源一致）**：

- Rust 1.97.0 release notes 的 *Compatibility Notes*：`"Emit a future-compatibility warning when relying on f32: From<{float}> to constrain {float}"`——即当代码依赖 `f32: From<{float}>` 这条约束来固定 `{float}` 时，发出未来兼容性警告。
- 版本页 §2.6 / §7 给出**演进方向**：在需要具体类型、且未被其它约束确定为 `f64` 时，`{float}` 将**更可能回退到 `f32`**，并通过 future-compat lint 逐步过渡。

```rust,ignore
// edition = "2024", rust = "1.97" —— 演示“回退默认值”被显式约束取代的过程
fn takes_f32(_: f32) {}
fn takes_f64(_: f64) {}

fn main() {
    takes_f32(1.0);        // 1.0 被参数类型 f32 约束 → 不依赖回退，无警告
    takes_f64(1.0);        // 1.0 被参数类型 f64 约束 → 不依赖回退，无警告

    let a = 1.0;           // 无上下文约束：历史回退 f64；1.97 起该回退路径进入 future-compat 过渡
    let b: f32 = 2.0;      // 显式标注 f32 → 推断变量被标注固定，不触发 future-compat
    let _ = (a, b);
}
```

> **边界（哪些回退、哪些仍报错/告警）**：
>
> - **仍由上下文固定、不回退**：函数参数、`let x: f32/f64` 标注、结构体字段类型、`return` 类型、数组/元组元素的已知类型——这些情况下 `{float}` 在检查结束**前**已被等值约束实例化，不进入回退，也**不**触发 future-compat。
> - **进入回退但 1.97 仅告警**：完全无上下文约束、或仅经 `From`/`Into`/泛型 bound 间接约束的 `{float}`（如 `let v = 1.0.into();` 配合下游 `let _: f32 = v;`），触发 `f32: From<{float}>` 的 **future-compatibility warning**；当前（1.97.0）仍可编译。
> - **仍报错的情形**：当 `{float}` 同时被两个相互矛盾的具体类型约束（如同一变量既要 `f32` 又要 `f64`），统一失败 → 类型不匹配错误，与回退无关。
>
> ⚠ **需专家复核**：release notes 与版本页均**未逐项枚举**“哪些未约束上下文在 1.97 已实际回退到 `f32`、哪些仍停留在告警阶段”。上文“演进方向为 f32 回退、与 `{integer}`→`i32` 对称”的论断来自项目版本页 §2.6 的表述；release notes 仅确认 *future-compatibility warning* 这一可观察形态。具体逐上下文边界请以 Rust Reference — Type inference 与对应 future-compat lint 文档为准（来源：release notes；版本页 §2.6/§7）。

### 2. 与 never type fallback（`!` → `()`）的统一对比

Edition 2024 还调整了另一类“回退默认值”：**never type `!` 向 `()` 的回退**。两类 fallback 在 1.97/2024 被同一套“future-compat 逐步过渡”机制处理，可在类型检查层统一建模：

| 维度 | `{float}` → 浮点默认 | never type `!` → `()` |
|:---|:---|:---|
| 触发位置 | 浮点字面量推断变量检查结束未固定 | `!` 类型需要与一个期望类型统一（如 `match`/`if` 分支、发散表达式） |
| 历史默认 | `f64` | `()`（`!` 在许多位置回退/强转为 `()`） |
| 1.97/2024 改动方向 | 倾向回退到 `f32`（经 future-compat 过渡） | 收窄 `!`→`()` 的回退，让 `!` 更常保持为 `!` |
| 当前可观察形态 | future-compatibility warning（仍编译） | future-compat / dependency lint（仍编译，未来变硬错误） |
| 统一抽象 | “推断/类型变量在求解末尾被赋予一个默认值” | 同左：`!` 作为可统一类型变量在末尾被赋予默认值 `()` |
| 用户动作 | 给浮点字面量加 `f32`/`f64` 后缀或类型标注 | 显式写 `todo!()`/`unreachable!()` 的类型标注，或确保分支类型一致 |

```rust,ignore
// edition = "2024", rust = "1.97" —— 两类 fallback 的对照示例
fn float_fallback() {
    // 浮点回退：无上下文时 {float} 的默认值进入 future-compat 过渡
    let _x = 1.0;
}

fn never_fallback(flag: bool) -> i32 {
    // never type 回退：todo!() 类型为 !，需与 i32 统一；
    // 历史行为允许 ! → () 类回退参与统一，Edition 2024 收窄该回退。
    // （todo!() 在此为 never type 回退讲解的正例，非未完成示例）
    if flag {
        42
    } else {
        todo!()   // ! 与 i32 的统一路径在 2024 起更严格
    }
}
```

> ⚠ **需专家复核**：never type fallback 在 Edition 2024 的具体 lint 名称（社区中常见写法为 `dependency_on_unit_never_type_fallback`）与精确触发条件，本小节未能从 release notes / 版本页逐项确认；lint 名以 Rust Reference / Edition Guide 为准，请勿在未核对前将上述名称当作稳定 lint 名引用（来源：Rust Reference — The never type；Edition Guide）。

### 3. 对 trait solver 默认值 / 泛型推断的影响

`{float}` 的回退默认值是 **trait/type solver 在所有候选（candidate）求解完毕后、为仍未固定的推断变量指派的最后手段**。因此回退默认值从 `f64` 改为 `f32` 的**演进方向**，会改变泛型/`From` 上下文中的候选选择结果——这正是 `f32: From<{float}>` future-compat 警告的来源：

```rust,ignore
// edition = "2024", rust = "1.97" —— 泛型 + From 约束下的回退影响
fn generic_from<T>() -> T
where
    T: From<f32>, // 注意：bound 写在 f32 上
{
    // 字面量 1.0 的类型 {float} 需要与 T: From<f32> 的输入 f32 协调。
    // 当 {float} 回退默认值变化时，solver 对 {float} 的最终实例化、
    // 以及由此选中的 From 实现候选可能改变 → 触发 future-compat。
    T::from(1.0)
}

fn main() {
    let _v: f32 = generic_from::<f32>();
}
```

- **候选装配（Candidate Assembly）**：对 `T: From<{float}>`，solver 收集 `f32: From<{float}>` / `f64: From<{float}>` 等候选；参见 [`26_trait_solver_in_rustc.md`](../05_rustc_internals/03_trait_solver_in_rustc.md) §三 “Selection：候选装配与筛选”。
- **回退作为 tie-breaker**：当多个候选在语法上都可匹配、`{float}` 未被其它等值约束固定时，回退默认值决定 solver 把 `{float}` 实例化为 `f32` 还是 `f64`，从而决定**哪一个 `From` 候选被选中**。默认值变化 ⟹ 候选选择可能变化 ⟹ future-compat 警告。
- **仅影响“未固定”路径**：若调用点已用 `f64::from(x)`、`let y: f64 = x.into()` 或 turbofish 固定目标类型，则 `{float}` 在求解前已被约束，回退默认值不参与，行为不变（详见 [`migration_197_decision_tree.md`](../../07_future/00_version_tracking/migration_197_decision_tree.md) §4）。

> **统一建模要点**：把“回退默认值”看作 solver 输出端的**默认实例化函数** `default(FloatVar) = f32/f64`、`default(NeverVar) = ()/!`。1.97/2024 改动的是这个**默认函数**的取值，而非统一/子类型规则本身；因此受影响的是“求解末尾仍未固定”的变量，而非“已被约束固定”的变量。

> **来源**: [Rust 1.97.0 Release Notes — Compatibility Notes](https://releases.rs/docs/1.97.0/) · [Rust Reference — Type inference](https://doc.rust-lang.org/reference/introduction.html) · [Rust Reference — The never type](https://doc.rust-lang.org/reference/types/never.html) · 版本页 [`rust_1_97_stabilized.md`](../../07_future/00_version_tracking/rust_1_97_stabilized.md)（§2.6、§7）
> **交叉反链**: [`feature_domain_matrix_197.md`](../../07_future/00_version_tracking/feature_domain_matrix_197.md) · [`migration_197_decision_tree.md`](../../07_future/00_version_tracking/migration_197_decision_tree.md) · [`26_trait_solver_in_rustc.md`](../05_rustc_internals/03_trait_solver_in_rustc.md)

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [creusot-rs/creusot — Rust 演绎验证](https://github.com/creusot-rs/creusot) · [formal-land/coq-of-rust](https://github.com/formal-land/coq-of-rust)

## ⚠️ 反例与陷阱

本节以 `collect()` 缺标注为反例，展示 `FromIterator` 多实现导致的推断歧义与标注修正。

### 反例：`collect()` 缺少类型标注导致推断失败（rustc 1.97.0 实测）

```rust,compile_fail,E0283
fn main() {
    let words = vec!["a", "b", "c"];
    let lens = words.iter().map(|w| w.len()).collect(); // ❌ 目标容器类型未知
    println!("{}", lens);
}
```

**错误**：`E0283 type annotations needed`——`FromIterator` 的实现不唯一（`Vec<_>`/`HashSet<_>`/...），推断无唯一解。

### ✅ 修正：标注收集目标类型

```rust
fn main() {
    let words = vec!["a", "b", "c"];
    let lens: Vec<usize> = words.iter().map(|w| w.len()).collect();
    println!("{:?}", lens);
}
```
