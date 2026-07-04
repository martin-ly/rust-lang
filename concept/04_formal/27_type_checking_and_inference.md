> **内容分级**: [综述级]
> **本节关键术语**: Type Checking · Type Inference · `typeck` · `Ty<'tcx>` · `InferCtxt` · Inference Variable · Unification · Region Constraint · Snapshot — [完整对照表](../00_meta/terminology_glossary.md)
>
# rustc 类型检查与类型推断

> **EN**: Type Checking and Inference in rustc
> **Summary**: Explains how rustc checks types via the `typeck` query, generates constraints, and resolves inference variables using equality, subtyping, and region constraints.
> **受众**: [专家 / 研究者]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **F** — Formal
> **双维定位**: F×Type — 类型系统（Type System）与形式化方法
> **定位**: 把“编译器如何知道 `Vec<&str>` 并对未标注类型做推断”还原为约束生成、统一与区域求解的完整算法。
> **前置概念**: [Name Resolution and HIR](35_name_resolution_and_hir.md) · [Trait Solver in rustc](26_trait_solver_in_rustc.md) · [Type Inference](08_type_inference.md)
> **后置概念**: [NLL 与 Polonius](../03_advanced/08_nll_and_polonius.md) · [LLVM Backend and Codegen](../06_ecosystem/67_llvm_backend_and_codegen.md)

---

> **来源**: [Rustc Dev Guide — Type inference](https://rustc-dev-guide.rust-lang.org/type-inference.html) · · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Hindley — The Principal Type-Scheme of an Object in Combinatory Logic](https://doi.org/10.2307/2270762) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Rustc Dev Guide — HIR Type checking](https://rustc-dev-guide.rust-lang.org/hir-typeck/summary.html) ·
> [Rustc Dev Guide — The ty module](https://rustc-dev-guide.rust-lang.org/ty.html) ·
> [Rust Reference — Type System](https://doc.rust-lang.org/reference/types.html)


---

## 认知路径

> **认知路径**: 本节从 "rustc 类型检查与类型推断（Type Inference）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 rustc 类型检查与类型推断（Type Inference） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 rustc 类型检查与类型推断 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与rustc 类型检查与类型推断的适用边界。
5. **迁移应用**: 将 rustc 类型检查与类型推断 与前置/后置概念链接，形成跨层知识网络。


---

> **过渡**: 从 rustc 类型检查与类型推断 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 rustc 类型检查与类型推断 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 rustc 类型检查与类型推断 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。


---

> **定理 1** [Tier 2]: rustc 类型检查与类型推断 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 rustc 类型检查与类型推断 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 rustc 类型检查与类型推断 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。


---

## 反命题决策树

> **反命题 1**: "rustc 类型检查与类型推断 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 rustc 类型检查与类型推断 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 rustc 类型检查与类型推断 规则被违反的直接信号。

> **反命题 3**: "其他语言对 rustc 类型检查与类型推断 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 rustc 类型检查与类型推断 具有语言特有的形态。


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
> [来源: Rustc Dev Guide — HIR Type checking](https://rustc-dev-guide.rust-lang.org/hir-typeck/summary.html)

---

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

> [来源: Rustc Dev Guide — The ty module](https://rustc-dev-guide.rust-lang.org/ty.html)

---

## 三、`typeck` Query 与 `InferCtxt`

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

> [来源: Rustc Dev Guide — Inference variables](https://rustc-dev-guide.rust-lang.org/type-inference.html#inference-variables)

---

## 五、相等约束与子类型约束

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

## 六、区域约束与求解

### 6.1 收集约束

类型检查不会立即求解生命周期，而是收集 **outlives** 约束：

```text
'a: 'b   （即 'b <= 'a）
```

例如赋值 `let y: &'a i32 = x;`，若 `x: &'b i32`，则生成约束 `'b: 'a`。

### 6.2 求解时机

- **词法求解（lexical）**: 在类型检查结束时统一求解；
- **NLL（Non-Lexical Lifetimes）**: MIR 借用（Borrowing）检查器在更细粒度控制流上求解。

> **定理**: 区域约束只在其他约束和 trait obligations 都处理完之后才最终求解。
>
> [来源: Rustc Dev Guide — Region constraints](https://rustc-dev-guide.rust-lang.org/type-inference.html#region-constraints)

---

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
> [来源: Rustc Dev Guide — Snapshots](https://rustc-dev-guide.rust-lang.org/type-inference.html#snapshots)

---

## 嵌入式测验

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

主要体现在生命周期上，例如 `'static` 比任何 `'a` 都长，因此 `&'static T` 是 `&'a T` 的子类型。

</details>

---

### 测验 4：为什么区域约束要延迟到最后才求解？

<details>
<summary>✅ 答案与解析</summary>

因为生命周期约束往往依赖于其他推断变量的最终值；提前求解可能得到不完整或错误的结果。延迟求解确保所有类型信息已知后再做统一判断。

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

> **权威来源**: [Rustc Dev Guide](https://rustc-dev-guide.rust-lang.org/), [The Rust Reference](https://doc.rust-lang.org/reference/) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)
> **权威来源对齐变更日志**: 2026-06-21 创建，对齐 Rust 1.96.1 类型检查与推断文档

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.1+ (Edition 2024)
**最后更新**: 2026-06-21
**状态**: ✅ 已对齐 Rustc Dev Guide type checking / inference 文档
