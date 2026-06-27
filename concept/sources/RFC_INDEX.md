> **内容分级**:
>
> [综述级]
> **受众**: [研究者]
> **定理链**: N/A — 描述性/综述性/导航性文档，不涉及形式化定理链
>
# RFC 索引：关键设计提案跟踪
>
> **EN**: Rfc Index
> **Summary**: Rfc Index. Core Rust concept.
>
> | RFC | 标题 | 状态 | 稳定版本 | 概念文件 |
> | :--- | :--- | :---: | :---: | :--- |
> | [RFC 0243](https://rust-lang.github.io/rfcs//0243-trait-based-exception-handling.html) | Trait-based exception handling (`Try` trait) | ✅ | 1.26 | `04_error_handling.md` |
> | [RFC 1210](https://rust-lang.github.io/rfcs//1210-impl-specialization.html) | Specialization | 🚧 | nightly|
>
> **定位**: 覆盖对 Rust 语言语义、类型系统（Type System）、内存模型、并发和生态有结构性影响的 RFC。
> **状态标注**: ✅ Implemented | 🚧 Accepted (未实现) | ⚠️ Deprecated | 🔍 Draft | ❌ Rejected
> **维护**: 每 6 周扫描 RFC 仓库更新状态。

>
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/)
> **前置概念**: N/A
> **后置概念**: N/A
---

## 一、语言核心（Language Core）

| RFC | 标题 | 状态 | 稳定版本 | 概念文件 |
| :--- | :--- | :---: | :---: | :--- |
| [RFC 0243](https://rust-lang.github.io/rfcs//0243-trait-based-exception-handling.html) | Trait-based exception handling (`Try` trait) | ✅ | 1.26 | `04_error_handling.md` |
| [RFC 1210](https://rust-lang.github.io/rfcs//1210-impl-specialization.html) | Specialization | 🚧 | nightly | `01_traits.md` §5.7 |
| [RFC 1598](https://rust-lang.github.io/rfcs//1598-generic_associated_types.html) | Generic Associated Types (GATs) | ✅ | 1.65 | `01_traits.md` §4.6 |
| [RFC 2000](https://rust-lang.github.io/rfcs//2000-const-generics.html) | Const Generics | ✅ | 1.51 | `02_generics.md` §5.7 |
| [RFC 2086](https://rust-lang.github.io/rfcs//2086-allow-if-let-irrefutables.html) | Allow `if let` guards in match arms | ✅ | 1.95 | `05_rust_version_tracking.md` §2.2 |
| [RFC 2094](https://rust-lang.github.io/rfcs//2094-nll.html) | Non-lexical lifetimes (NLL) | ✅ | 1.31 | `03_lifetimes.md` §十二 |
| [RFC 2349](https://rust-lang.github.io/rfcs//2349-pin.html) | Pin API | ✅ | 1.33 | `06_pin_unpin.md` |
| [RFC 2394](https://rust-lang.github.io/rfcs//2394-async_await.html) | async/await | ✅ | 1.39 | `02_async.md` |
| [RFC 2497](https://rust-lang.github.io/rfcs//2497-if-let-chains.html) | if-let chains | ✅ | 1.88 (2024Ed) | `02_borrowing.md` §九 |
| [RFC 2582](https://rust-lang.github.io/rfcs//2582-raw-reference-mir-operator.html) | `&raw` operators | ✅ | 1.82 | `05_rust_version_tracking.md` §2.1 |
| [RFC 2585](https://rust-lang.github.io/rfcs//2585-unsafe-block-in-unsafe-fn.html) | `unsafe_op_in_unsafe_fn` lint | ✅ | 1.52 | `03_unsafe.md` §7.3 |
| [RFC 2930](https://rust-lang.github.io/rfcs//2930-read-buf.html) | Readiness and waking for async I/O | ✅ | 1.36 | `02_async.md` §3.4 |
| [RFC 3191](https://rust-lang.github.io/rfcs//3191-debugger-visualizer.html) | Destructuring assignment | ✅ | 1.59 | — |
| [RFC 3243](https://rust-lang.github.io/rfcs//3243-packages-as-optional-namespaces.html) | Collapse `impl Trait` in associated types | 🚧 | — | `01_traits.md` |
| [RFC 3382](https://github.com/rust-lang/rfcs/pull/3382) | `const` trait bounds | 🚧 | nightly | `01_traits.md` §4.7 |

## 二、类型系统与泛型

| RFC | 标题 | 状态 | 稳定版本 | 概念文件 |
| :--- | :--- | :---: | :---: | :--- |
| [RFC 0192](https://rust-lang.github.io/rfcs//0192-bounds-on-object-and-generic-types.html) | Associated items | ✅ | 1.0 | `01_traits.md` |
| [RFC 0445](https://rust-lang.github.io/rfcs//0445-extension-trait-conventions.html) | Allow overloading of `*` / `&` | ❌ | — | — |
| [RFC 0738](https://rust-lang.github.io/rfcs//0738-variance.html) | Variadic generics | ❌ | — | — |
| [RFC 1023](https://rust-lang.github.io/rfcs//1023-rebalancing-coherence.html) | Rebalancing coherence / orphan rules | ✅ | 1.0 | `01_traits.md` §4.1 |
| [RFC 1053](https://github.com/rust-lang/rfcs/pull/1053) | Allow overloading shift operators | ✅ | 1.0 | — |
| [RFC 1156](https://rust-lang.github.io/rfcs//1156-adjust-default-object-bounds.html) | Adjust default object bounds | ✅ | 1.17 | `01_traits.md` |
| [RFC 1327](https://rust-lang.github.io/rfcs//1327-dropck-param-eyepatch.html) | Dropck eyepatch | ✅ | 1.13 | `03_memory_management.md` |
| [RFC 1951](https://rust-lang.github.io/rfcs//1951-expand-impl-trait.html) | Expand `where` clause syntax | ✅ | 1.23 | `02_generics.md` |
| [RFC 2289](https://rust-lang.github.io/rfcs//2289-associated-type-bounds.html) | Associated type constructors | 🚧 | — | `01_traits.md` §4.6 |

## 三、内存模型与 Unsafe

| RFC | 标题 | 状态 | 稳定版本 | 概念文件 |
| :--- | :--- | :---: | :---: | :--- |
| [RFC 0769](https://rust-lang.github.io/rfcs//0769-sound-generic-drop.html) | Sound generic drop | ✅ | 1.0 | `03_memory_management.md` |
| [RFC 1861](https://rust-lang.github.io/rfcs//1861-extern-types.html) | Extern types | 🚧 | nightly | `05_rust_ffi.md` |
| [RFC 2581](https://github.com/rust-lang/rfcs/pull/2581) | `&mut` reborrows for `DerefMut` | ✅ | — | `02_borrowing.md` |
| [RFC 2753](https://github.com/rust-lang/rfcs/pull/2753) | Union types | ✅ | 1.19 | `04_type_system.md` |
| [RFC 2807](https://github.com/rust-lang/rfcs/pull/2807) | Target feature support | ✅ | 1.27 | `03_unsafe.md` |
| [RFC 2835](https://rust-lang.github.io/rfcs//2835-project-safe-transmute.html) | Type alias enum variants | ✅ | 1.37 | `04_type_system.md` |

## 四、并发与异步

| RFC | 标题 | 状态 | 稳定版本 | 概念文件 |
| :--- | :--- | :---: | :---: | :--- |
| [RFC 1299](https://github.com/rust-lang/rfcs/pull/1299) | Incremental compilation | ✅ | 1.24 | — |
| [RFC 2010](https://github.com/rust-lang/rfcs/pull/2010) | Integer atomics | ✅ | 1.34 | `01_concurrency.md` §3.1 |
| [RFC 2052](https://rust-lang.github.io/rfcs//2052-epochs.html) | Epochs (后发展为 Edition) | ⚠️ | — | `05_rust_version_tracking.md` |
| [RFC 2592](https://rust-lang.github.io/rfcs//2592-futures.html) | Futures and async/await | ✅ | 1.36 | `02_async.md` §3.1 |

## 五、Edition 与工具链

| RFC | 标题 | 状态 | 稳定版本 | 概念文件 |
| :--- | :--- | :---: | :---: | :--- |
| [RFC 2052](https://rust-lang.github.io/rfcs//2052-epochs.html) | Epochs (后发展为 Edition) | ⚠️ | — | `22_edition_guide.md` |
| [RFC 3086](https://rust-lang.github.io/rfcs//3086-macro-metavar-expr.html) | Macro metavariable expressions | ✅ | 1.60 | `04_macros.md` |
| [RFC 3101](https://rust-lang.github.io/rfcs//3101-reserved_prefixes.html) | Reserved prefixes | ✅ | 1.53 (2021Ed) | `22_edition_guide.md` |
| [RFC 3501](https://rust-lang.github.io/rfcs//3501-edition-2024.html) | Edition 2024 | ✅ | 1.85 | `22_edition_guide.md` |

## 六、前沿提案（Preview / Unstable）

| RFC/跟踪 | 标题 | 状态 | 目标版本 | 概念文件 |
| :--- | :--- | :---: | :---: | :--- |
| [RFC 3627](https://rust-lang.github.io/rfcs//3627-match-ergonomics-2024.html) | Return type notation (RTN) | 🚧 | nightly | `12_return_type_notation_preview.md` |
| 无 RFC | `gen` blocks / sync generators | 🔍 | 1.95+ nightly | `15_gen_blocks_preview.md` |
| 无 RFC | `unsafe` fields | 🔍 | nightly | `13_unsafe_fields_preview.md` |
| 无 RFC | Effects system / `const` effects | 🔍 | 远期 | `04_effects_system.md` |
| 无 RFC | Arbitrary self types v2 | 🔍 | nightly | — |
| 无 RFC | Async drop | 🔍 | nightly | `18_async_drop_preview.md` |
| 无 RFC | Specialization (完整版) | 🚧 | nightly | `26_specialization_preview.md` |
| 无 RFC | Const trait impl | 🚧 | nightly | `11_const_trait_impl_preview.md` |

---

## 使用规范

### 概念文件中引用 RFC 的标准格式

```markdown
> **来源: [RFC 2394 — async/await](https://rust-lang.github.io/rfcs/2394-async_await.html)** 引入 `async`/`await` 语法糖...
> **状态**: ✅ Implemented (Rust 1.39) | 替代方案: RFC 2592 (Futures)
```

### 禁止格式

```markdown
❌ [来源: RFCs]  # 无编号
❌ 来源: [RFC 2394](https://rust-lang.github.io/rfcs/2394-async_await.html)  # 无标题
❌ RFC 2394 (无状态标注)
```

---

## 变更日志

| 日期 | 变更 |
|:---|:---|
| 2026-05-24 | 初始建立，覆盖 40 个关键 RFC |

## 嵌入式测验（Embedded Quiz）

### 测验 1：《RFC 索引：关键设计提案跟踪》是知识体系的来源文档。来源文档的作用是什么？（理解层）

**题目**: 《RFC 索引：关键设计提案跟踪》是知识体系的来源文档。来源文档的作用是什么？

<details>
<summary>✅ 答案与解析</summary>

记录和规范化所有概念文件的权威引用（Reference）来源，确保知识的可追溯性和学术严谨性，便于读者深入查证。
</details>

---

### 测验 2：为什么来源文档需要区分一级来源和二级来源？（理解层）

**题目**: 为什么来源文档需要区分一级来源和二级来源？

<details>
<summary>✅ 答案与解析</summary>

一级来源（如 Rust Reference、RFC）是权威定义，二级来源（如博客、教程）是解释和补充。区分帮助读者判断信息的可靠性。
</details>

---

### 测验 3：在引用来源时，为什么建议精确到具体章节而非只写根 URL？（理解层）

**题目**: 在引用（Reference）来源时，为什么建议精确到具体章节而非只写根 URL？

<details>
<summary>✅ 答案与解析</summary>

精确到章节便于读者快速定位相关内容，避免因文档庞大而找不到对应信息，也便于后续审核和更新引用。
</details>
