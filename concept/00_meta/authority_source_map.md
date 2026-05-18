# 权威来源映射表（Authority Source Map）

> **版本**: v1.0
> **创建日期**: 2026-05-19
> **范围**: concept/ + knowledge/ + docs/ 核心概念
> **对齐语言**: C++ / Haskell / Go

---

## 一、一级来源：Rust 官方与形式化

| 概念 | 官方来源 | 学术来源 | 社区权威 | C++ 对标 | Haskell 对标 | Go 对标 |
|:---|:---|:---|:---|:---|:---|:---|
| **Ownership** | TRPL Ch4 · Reference § Ownership Types | Ralf Jung *"RustBelt: Securing the Foundations of the Rust Programming Language"* (POPL 2018) · Clarke *"Ownership Types for Flexible Alias Protection"* (OOPSLA 1998) | Niko Matsakis blog *"The problem of safe and convenient parallelism"* | `unique_ptr` (cppreference) · RAII | Linear Types (Wadler, ICFP 1990) · Affine Logic | 无（GC 管理） |
| **Borrowing** | TRPL Ch4.2 · Reference § References and Borrowing | Ralf Jung *"Stacked Borrows: An Aliasing Model for Rust"* (POPL 2021) | Niko Matsakis *"Two interpretations of borrowing"* | 引用 `&T` / `const T&` 语义 · 悬垂引用规则 | Borrowing in linear/affine type systems (Wadler) | 指针借用（无编译期检查） |
| **Lifetimes** | TRPL Ch10 · Reference § Lifetime Elision · RFC 2094 (NLL) | Ralf Jung *"Tree Borrows: Or, How I Learned to Stop Worrying and Love the Alias"* (arXiv 2023) | Jon Gjengset *"Crust of Rust: Lifetime Annotations"* | 无直接对应（RAII + 智能指针处理） | 显式 region / let-binding scope | 无（GC 决定） |
| **Type System** | Reference § Types · RFC 1210 (impl trait) | Pierce *"Types and Programming Languages"* (TAPL, MIT Press) · Hindley-Milner 类型推断 | Without Boats *"Implied bounds and perfect derive"* | Templates · Concepts (C++20) | HM 类型推断 · Type Classes (Wadler & Blott, 1989) | 结构化类型 · 接口（隐式实现） |
| **Traits** | Reference § Traits · RFC 255 | Morrisett *"Typed Closure Conversion"* · Trait objects vtable 形式化 | Niko Matsakis *"After NLL: Interprocedural lifetimes"* | 抽象类 · Concepts · CRTP | Type Classes · Type Families | 接口 (interface) · 嵌入式接口 |
| **Generics** | Reference § Generic Parameters · RFC 2000 (const generics) | Jones *"A system of constructor classes"* (JFP 1993) · Monomorphization 成本分析 | Jon Gjengset *"Crust of Rust: GATs"* | Templates (全特化/偏特化) | Parametric Polymorphism · Higher-Ranked Types | 泛型 (type parameters) |
| **Send/Sync** | Reference § Send and Sync · Nomicon § Send and Sync | RustBelt § Protocol Verification · Data Race Freedom Proof | Ralf Jung *"The Case for a Memory Safe Systems Language"* | `thread_safety` 概念（无编译器保证） | `NFData` / `Par` monad 约束 | Goroutine + Channel（CSP） |
| **Async/Await** | Reference § async blocks · RFC 3185 (async fn in traits) | POPL 2023 *"Asynchronous Execution in Rust"* 类工作 | Without Boats *"Pin and Suffering"* · Niko Matsakis *"Async/Await I: Self-Referential Structs"* | C++20 Coroutines (`co_await`) | Async/IO Monads · `async`/`await` 语法糖 | Goroutine + Channel（隐式调度） |
| **Unsafe** | Reference § Unsafe Rust · Nomicon | RustBelt § Iris 框架 · Ralf Jung *"The Meaning of Memory Safety"* (PLArch 2021) | Ralf Jung blog · The Rustonomicon | `unsafe` 块 · UB 规则 | `unsafePerformIO` · `ForeignFunctionInterface` | `unsafe` 包（ limited ） |
| **Macros** | Reference § Macros · The Little Book of Macros | Hygienic Macros (Kohlbecker et al., 1986) | dtolnay *"Procedural Macros: Derive"* | C Preprocessor · Templates | Template Haskell · Quasi-Quotes | `go generate`（无宏系统） |

---

## 二、二级来源：跨语言权威入口

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

## 三、网络权威锚点（永久链接）

### Rust 官方

```
TRPL:        https://doc.rust-lang.org/book/
Reference:   https://doc.rust-lang.org/reference/
Nomicon:     https://doc.rust-lang.org/nomicon/
RFCs:        https://rust-lang.github.io/rfcs/
Rust By Ex:  https://doc.rust-lang.org/rust-by-example/
```

### 学术

```
RustBelt (POPL 2018):  https://plv.mpi-sws.org/rustbelt/
Stacked Borrows:       https://plv.mpi-sws.org/rustbelt/stacked-borrows/
Tree Borrows:          https://plv.mpi-sws.org/rustbelt/tree-borrows/
Iris Project:          https://iris-project.org/
Ralf Jung 主页:         https://ralfj.de/
```

### 社区权威博客

```
Niko Matsakis:         https://smallcultfollowing.com/babysteps/
Without Boats:         https://without.boats/
Jon Gjengset:          https://thesquareplanet.com/blog/ · YouTube: @JonGjengset
Ralf Jung (blog):      https://www.ralfj.de/blog/
dtolnay:               https://dtolnay.github.io/
```

---

## 四、执行批次

| 批次 | 目标文件 | 核心补全内容 |
|:---|:---|:---|
| **Batch 1** | `concept/01_foundation/01_ownership.md` | 深化 RustBelt / COR 论证摘要，补全 C++ RAII vs Rust Ownership 形式化差异 |
| **Batch 1** | `knowledge/01_fundamentals/ownership.md` | 补全 TRPL / Wikipedia 来源标注，添加 C++ / Go 内存管理对比来源 |
| **Batch 1** | `docs/02_reference/CROSS_LANGUAGE_COMPARISON.md` | 全篇补来源标注（cppreference / Go Spec / Haskell Wiki） |
| **Batch 2** | `concept/01_foundation/02_borrowing.md` + 对应 knowledge/docs | Stacked Borrows → Tree Borrows 演进论证，C++ 引用语义对比 |
| **Batch 3** | `concept/01_foundation/03_lifetimes.md` + 对应 knowledge/docs | NLL / Polonius / Tree Borrows 来源链，形式化区域类型论证 |
| **Batch 4** | `concept/02_intermediate/01_traits.md` + 对应 knowledge/docs | Type Classes 对比论证，Orphan Rule 设计来源 |
| **Batch 5** | L3-L7 核心文件 + 对应知识层 | 按映射表逐篇补全 |

---

> **维护规范**: 每完成一个批次，更新本表中的 ✅ 状态，并在对应文件顶部 `变更日志` 中记录。
