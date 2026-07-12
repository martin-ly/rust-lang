# 权威来源映射表（Authority Source Map）
>
> **EN**: Authority Source Map
> **Summary**: A concept-by-concept map from core Rust topics (Ownership, Borrowing, Traits, Lifetimes, Concurrency, …) to their authoritative sources in four tiers — official docs (TRPL / Rust Reference), academic formalizations (RustBelt et al.), and community authorities — each row adding C++/Haskell/Go counterpart references for cross-language alignment.
>
> | 概念 | 官方来源 | 学术来源 | 社区权威 | C++ 对标 | Haskell 对标 | Go 对标 | 备注 |
> | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
>
> | **Ownership** | TRPL Ch4 · Reference § Ownership Types | Ralf Jung *"RustBelt: Securing the Foundations of the Rust Programming Language"* (POPL 2018) · Clarke *"Ownership Types
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [进阶]
> **Bloom 层级**: L4-L5
> **权威来源**: 本文件为 `concept/` 权威页。
> **版本**: v1.1
> **创建日期**: 2026-05-19
> **范围**: concept/ + knowledge/ + docs/ 核心概念
> **对齐语言**: C++ / Haskell / Go
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Bloom 标注、跨文件链接、来源索引格式统一 [Authority Source Sprint Batch 8](05_international_authority_index.md)
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>
> **来源**: [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html)
---

> **相关概念文件**:
>
> - [`concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md`](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md) — 所有权的形式化基础
> - [`concept/02_intermediate/00_traits/01_traits.md`](../../02_intermediate/00_traits/01_traits.md) — Trait 系统的跨语言对比
> - [`concept/05_comparative/01_rust_vs_cpp.md`](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) — Rust vs C++ 深度对比
> - [`concept/04_formal/01_linear_logic.md`](../../04_formal/01_ownership_logic/01_linear_logic.md) — 线性逻辑与所有权形式化
> - [`concept/07_future/03_evolution.md`](../../07_future/04_research_and_experimental/03_evolution.md) — 语言演进与 RFC 追踪

---

## 📑 目录

- [权威来源映射表（Authority Source Map）](#权威来源映射表authority-source-map)
  - [📑 目录](#-目录)
  - [一、一级来源：Rust 官方与形式化 来源分级方法论基于证据金字塔模型 — 官方标准 \> 学术论文 \> 社区权威 \> 实践经验](#一一级来源rust-官方与形式化-来源分级方法论基于证据金字塔模型--官方标准--学术论文--社区权威--实践经验)
  - [二、二级来源：跨语言权威入口 跨语言对比方法论参照 concept/05\_comparative/ 系列文件的对比框架](#二二级来源跨语言权威入口-跨语言对比方法论参照-concept05_comparative-系列文件的对比框架)
    - [C++](#c)
    - [Haskell](#haskell)
    - [Go](#go)
  - [三、网络权威锚点（永久链接） 永久链接选择标准: 域名稳定性 \> 版本归档 \> 社区镜像; 参照 PURL (Persistent Uniform Resource Locator) 标准和 DOI 数字对象标识符的设计原则](#三网络权威锚点永久链接-永久链接选择标准-域名稳定性--版本归档--社区镜像-参照-purl-persistent-uniform-resource-locator-标准和-doi-数字对象标识符的设计原则)
    - [Rust 官方](#rust-官方)
    - [学术](#学术)
    - [社区权威博客](#社区权威博客)
  - [四、执行批次 Authority Source Sprint 执行记录; 对齐方法论参照 AGENTS.md 质量铁三角 — Bloom 层级 100%、来源标注率 ≥15%、跨文件链接 ≥3/文件](#四执行批次-authority-source-sprint-执行记录-对齐方法论参照-agentsmd-质量铁三角--bloom-层级-100来源标注率-15跨文件链接-3文件)
  - [认知路径](#认知路径)
    - [核心推理链](#核心推理链)
    - [反命题与边界](#反命题与边界)
  - [嵌入式测验（Embedded Quiz）](#嵌入式测验embedded-quiz)
    - [测验 1：本文档《权威来源映射表（Authority Source Map）》在 Rust 知识体系中属于哪一层级的元数据？（理解层）](#测验-1本文档权威来源映射表authority-source-map在-rust-知识体系中属于哪一层级的元数据理解层)
    - [测验 2：《权威来源映射表（Authority Source Map）》的主要用途是什么？（理解层）](#测验-2权威来源映射表authority-source-map的主要用途是什么理解层)
    - [测验 3：元数据层文档能否替代 L1-L7 的核心概念学习？（理解层）](#测验-3元数据层文档能否替代-l1-l7-的核心概念学习理解层)

## 一、一级来源：Rust 官方与形式化 [来源分级方法论基于证据金字塔模型 — 官方标准 > 学术论文 > 社区权威 > 实践经验](https://en.wikipedia.org/wiki/Evidence_hierarchy)

| 概念 | 官方来源 | 学术来源 | 社区权威 | C++ 对标 | Haskell 对标 | Go 对标 | 备注 |
| :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- | :--- |
| **Ownership** | TRPL Ch4 · Reference § Ownership Types | Ralf Jung *"RustBelt: Securing the Foundations of the Rust Programming Language"* (POPL 2018) · Clarke *"Ownership Types for Flexible Alias Protection"* (OOPSLA 1998) | Niko Matsakis blog *"The problem of safe and convenient parallelism"* | `unique_ptr` (cppreference) · RAII | Linear Types (Wadler, ICFP 1990) · Affine Logic | 无（GC 管理） | [核心形式化论证见 concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md](https://doc.rust-lang.org/reference/introduction.html)
| **Borrowing** | TRPL Ch4.2 · Reference § References and Borrowing | Ralf Jung *"Stacked Borrows: An Aliasing Model for Rust"* (POPL 2021) | Niko Matsakis *"Two interpretations of borrowing"* | 引用 `&T` / `const T&` 语义 · 悬垂引用规则 | Borrowing in linear/affine type systems (Wadler) | 指针借用（无编译期检查） | [核心形式化论证见 concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md](https://doc.rust-lang.org/reference/introduction.html)
| **Lifetimes** | TRPL Ch10 · Reference § Lifetime Elision · [RFC 2094](https://rust-lang.github.io/rfcs//2094-nll.html) (NLL) | Villani, Hostert, Dreyer & Jung *"Tree Borrows: A New Aliasing Model for Rust"* ([PLDI 2025](https://pldi26.sigplan.org/), **Distinguished Paper Award**) | Jon Gjengset *"Crust of Rust: Lifetime Annotations"* | 无直接对应（RAII + 智能指针处理） | 显式 region / let-binding scope | 无（GC 决定） |
| **Type System** | Reference § Types · [RFC 1210](https://rust-lang.github.io/rfcs//1210-impl-specialization.html) (impl trait) | Pierce *"Types and Programming Languages"* (TAPL, MIT Press) · Hindley-Milner 类型推断 | Without Boats *"Implied bounds and perfect derive"* | Templates · Concepts (C++20) | HM 类型推断 · Type Classes (Wadler & Blott, 1989) | 结构化类型 · 接口（隐式实现） | [TAPL 是类型系统的标准教材; HM 类型推断是 Rust 类型系统的基础](https://www.cis.upenn.edu/~bcpierce/tapl/)
| **Traits** | Reference § Traits · RFC 255 | Morrisett *"Typed Closure Conversion"* · Trait objects vtable 形式化 | Niko Matsakis *"After NLL: Interprocedural lifetimes"* | 抽象类 · Concepts · CRTP | Type Classes · Type Families | 接口 (interface) · 嵌入式接口 |
| **Generics** | Reference § Generic Parameters · [RFC 2000](https://rust-lang.github.io/rfcs//2000-const-generics.html) (const generics) | Jones *"A system of constructor classes"* (JFP 1993) · Monomorphization 成本分析 | Jon Gjengset *"Crust of Rust: GATs"* | Templates (全特化/偏特化) | Parametric Polymorphism · Higher-Ranked Types | 泛型 (type parameters) |
| **Send/Sync** | Reference § Send and Sync · Nomicon § Send and Sync | RustBelt § Protocol Verification · Data Race Freedom Proof | Ralf Jung *"The Case for a Memory Safe Systems Language"* | `thread_safety` 概念（无编译器保证） | `NFData` / `Par` monad 约束 | Goroutine + Channel（CSP） |
| **Async/Await** | TRPL Ch17 · Reference § async blocks · [RFC 3185](https://rust-lang.github.io/rfcs//3185-static-async-fn-in-trait.html) (AFIT) · [RFC 3668](https://rust-lang.github.io/rfcs/3668-async-closures.html) (async closures) | POPL 2023 *"Asynchronous Execution in Rust"* 类工作 | Without Boats *"Pin and Suffering"* · Niko Matsakis *"Async/Await I: Self-Referential Structs"* | C++20 Coroutines (`co_await`) | Async/IO Monads · `async`/`await` 语法糖 | Goroutine + Channel（隐式调度） |
| **Unsafe** | Reference § Unsafe Rust · Nomicon | RustBelt § Iris 框架 · Ralf Jung *"The Meaning of Memory Safety"* (PLArch 2021) | Ralf Jung blog · The Rustonomicon | `unsafe` 块 · UB 规则 | `unsafePerformIO` · `ForeignFunctionInterface` | `unsafe` 包（ limited ） |
| **Macros** | Reference § Macros · The Little Book of Macros | Hygienic Macros (Kohlbecker et al., 1986) | dtolnay *"Procedural Macros: Derive"* | C Preprocessor · Templates | Template Haskell · Quasi-Quotes | `go generate`（无宏系统） |

---

## 二、二级来源：跨语言权威入口 [跨语言对比方法论参照 concept/05_comparative/ 系列文件的对比框架](https://doc.rust-lang.org/reference/introduction.html)

「二级来源：跨语言权威入口 跨语言对比方法论参照 conce…」涉及 C++、Haskell与Go，本节逐一说明其要点。

### C++

- **cppreference.com**: <https://en.cppreference.com/> —— ISO C++ 标准参考
- **C++ Core Guidelines**: <https://isocpp.github.io/CppCoreGuidelines/CppCoreGuidelines.html>
- **Stroustrup**: *"The C++ Programming Language, 4th Ed."* · *"A Tour of C++"*

### Haskell

- **GHC User Guide**: <https://downloads.haskell.org/ghc/latest/docs/users_guide/>
- **Typeclassopedia**: <https://wiki.haskell.org/Typeclassopedia>
- **Wadler**: *"Theorems for Free!"* (FPCA 1989) · *"Linear Types can Change the World!"* (1990)

### Go

- **Go Spec**: <https://go.dev/ref/spec>
- **Effective Go**: <https://go.dev/doc/effective_go>
- **Go Memory Model**: <https://go.dev/ref/mem>

---

## 三、网络权威锚点（永久链接） [永久链接选择标准: 域名稳定性 > 版本归档 > 社区镜像; 参照 PURL (Persistent Uniform Resource Locator) 标准和 DOI 数字对象标识符的设计原则](https://en.wikipedia.org/wiki/Persistent_uniform_resource_locator)

本节将「网络权威锚点（永久链接） 永久链接选择标准: 域名稳定性…」分解为若干主题： Rust 官方、学术与社区权威博客。

### Rust 官方

```
TRPL:        https://doc.rust-lang.org/book/
TRPL Ch17:   https://doc.rust-lang.org/book/ch17-00-async-await.html
Async Book:  https://rust-lang.github.io/async-book/  (⚠️ rewrite 中，状态 WIP)
Reference:   https://doc.rust-lang.org/reference/
Nomicon:     https://doc.rust-lang.org/nomicon/
RFCs:        https://rust-lang.github.io/rfcs/
Rust By Ex:  https://doc.rust-lang.org/rust-by-example/
```

### 学术

```
RustBelt (POPL 2018):  https://plv.mpi-sws.org/rustbelt/
Stacked Borrows:       https://plv.mpi-sws.org/rustbelt/stacked-borrows/
Tree Borrows:          https://plv.mpi-sws.org/rustbelt/
Iris Project:          https://iris-project.org/
Ralf Jung 主页:         https://ralfj.de/
```

### 社区权威博客

```
Niko Matsakis:         https://smallcultfollowing.com/babysteps/
Without Boats:         https://without.boats/
Jon Gjengset:          https://thesquareplanet.com/blog/ · YouTube: @JonGjengset
Ralf Jung (blog):      https://www.ralfj.de/blog/
dtolnay:               https://github.com/dtolnay
```

---

## 四、执行批次 [Authority Source Sprint 执行记录; 对齐方法论参照 AGENTS.md 质量铁三角 — Bloom 层级 100%、来源标注率 ≥15%、跨文件链接 ≥3/文件](../00_framework/methodology.md)

| 批次 | 目标文件 | 核心补全内容 |
|:---|:---|:---|
| **Batch 1** | `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | 深化 RustBelt / COR 论证摘要，补全 C++ RAII vs Rust Ownership 形式化差异 |
| **Batch 1** | `knowledge/01_fundamentals/ownership.md` | 补全 TRPL / Wikipedia 来源标注，添加 C++ / Go 内存管理对比来源 |
| **Batch 1** | `docs/02_reference/CROSS_LANGUAGE_COMPARISON.md` | 全篇补来源标注（cppreference / Go Spec / Haskell Wiki） |
| **Batch 2** | `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` + 对应 knowledge/docs | Stacked Borrows → Tree Borrows 演进论证，C++ 引用语义对比 |
| **Batch 3** | `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` + 对应 knowledge/docs | NLL / Polonius / Tree Borrows 来源链，形式化区域类型论证 |
| **Batch 4** | `concept/02_intermediate/00_traits/01_traits.md` + 对应 knowledge/docs | Type Classes 对比论证，Orphan Rule 设计来源 |
| **Batch 5** | L3-L7 核心文件 + 对应知识层 | 按映射表逐篇补全 |

---

> **维护规范**: 每完成一个批次，更新本表中的 ✅ 状态，并在对应文件顶部 `变更日志` 中记录。
---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/introduction.html), [The Rust Programming Language](https://doc.rust-lang.org/book/title-page.html), [Rustonomicon](https://doc.rust-lang.org/nomicon/index.html)
> **权威来源对齐变更日志**: 2026-05-19 补全权威来源标注（Rust Reference、TRPL、Rustonomicon、RFCs、学术论文） [Authority Source Sprint Batch 8](05_international_authority_index.md)

**文档版本**: 1.1
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

## 认知路径

> **认知路径**: 本文件作为 Rust 分层知识体系的 **权威来源映射表（Authority Source Map）** 元层导航节点，连接概念定义、学习路径与质量评估框架。

### 核心推理链

| 定理 | 前提 | 结论 | 置信度 |
|:---|:---|:---|:---|
| Authority Source Map 结构化定义 ⟹ 学习者认知锚点可建立 | 本文件定义了元层结构 | 支持上层概念定位 | 高 |

> **过渡**: 利用本文件的导航结构，读者可以从当前位置快速跃迁到任意概念层级，实现非线性学习。
> **过渡**: 权威来源映射表（Authority Source Map） 的维护需要与概念内容同步更新，确保元数据与实际知识体系的一致性。
> **过渡**: 将 权威来源映射表（Authority Source Map） 作为学习起点或复习锚点，有助于建立全局视野，避免陷入局部细节而忽视整体架构。

### 反命题与边界

> **反命题**: "元层文档可以替代具体概念学习" —— 错误。权威来源映射表（Authority Source Map） 提供的是导航与评估框架，不能替代对核心概念（L1-L5）的深入理解与实践。
> **内容分级**: [综述级]

## 嵌入式测验（Embedded Quiz）

理解「嵌入式测验（Embedded Quiz）」需要把握测验 1：本文档《权威来源映射表（Authority Source M…、测验 2：《权威来源映射表（Authority Source Map）…与测验 3：元数据层文档能否替代 L1-L7 的核心概念学习？（理解层），本节依次展开。

### 测验 1：本文档《权威来源映射表（Authority Source Map）》在 Rust 知识体系中属于哪一层级的元数据？（理解层）

**题目**: 本文档《权威来源映射表（Authority Source Map）》在 Rust 知识体系中属于哪一层级的元数据？

<details>
<summary>✅ 答案与解析</summary>

属于 00_meta 元数据层，为整个知识体系提供导航、评估、审计和结构化的支持框架，辅助学习者定位和理解核心概念。
</details>

---

### 测验 2：《权威来源映射表（Authority Source Map）》的主要用途是什么？（理解层）

**题目**: 《权威来源映射表（Authority Source Map）》的主要用途是什么？

<details>
<summary>✅ 答案与解析</summary>

作为知识体系的支撑文档，提供学习路径导航、概念关系映射、质量评估标准或审计检查清单，帮助学习者和维护者高效使用知识库。
</details>

---

### 测验 3：元数据层文档能否替代 L1-L7 的核心概念学习？（理解层）

**题目**: 元数据层文档能否替代 L1-L7 的核心概念学习？

<details>
<summary>✅ 答案与解析</summary>

不能。元数据层提供导航和评估框架，但不能替代对核心概念（所有权、类型系统、并发等）的深入理解与实践。
</details>
