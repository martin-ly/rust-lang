> **内容分级**: [综述级]
> **受众**: [研究者]

# RFC 索引：关键设计提案跟踪

> **定位**: 覆盖对 Rust 语言语义、类型系统、内存模型、并发和生态有结构性影响的 RFC。
> **状态标注**: ✅ Implemented | 🚧 Accepted (未实现) | ⚠️ Deprecated | 🔍 Draft | ❌ Rejected
> **维护**: 每 6 周扫描 RFC 仓库更新状态。

---

## 一、语言核心（Language Core）

| RFC | 标题 | 状态 | 稳定版本 | 概念文件 |
| :--- | :--- | :---: | :---: | :--- |
| RFC 0243 | Trait-based exception handling (`Try` trait) | ✅ | 1.26 | `04_error_handling.md` |
| RFC 1210 | Specialization | 🚧 | nightly | `01_traits.md` §5.7 |
| RFC 1598 | Generic Associated Types (GATs) | ✅ | 1.65 | `01_traits.md` §4.6 |
| RFC 2000 | Const Generics | ✅ | 1.51 | `02_generics.md` §5.7 |
| RFC 2086 | Allow `if let` guards in match arms | ✅ | 1.95 | `05_rust_version_tracking.md` §2.2 |
| RFC 2094 | Non-lexical lifetimes (NLL) | ✅ | 1.31 | `03_lifetimes.md` §十二 |
| RFC 2349 | Pin API | ✅ | 1.33 | `06_pin_unpin.md` |
| RFC 2394 | async/await | ✅ | 1.39 | `02_async.md` |
| RFC 2497 | if-let chains | ✅ | 1.88 (2024Ed) | `02_borrowing.md` §九 |
| RFC 2582 | `&raw` operators | ✅ | 1.82 | `05_rust_version_tracking.md` §2.1 |
| RFC 2585 | `unsafe_op_in_unsafe_fn` lint | ✅ | 1.52 | `03_unsafe.md` §7.3 |
| RFC 2930 | Readiness and waking for async I/O | ✅ | 1.36 | `02_async.md` §3.4 |
| RFC 3191 | Destructuring assignment | ✅ | 1.59 | — |
| RFC 3243 | Collapse `impl Trait` in associated types | 🚧 | — | `01_traits.md` |
| RFC 3382 | `const` trait bounds | 🚧 | nightly | `01_traits.md` §4.7 |

## 二、类型系统与泛型

| RFC | 标题 | 状态 | 稳定版本 | 概念文件 |
| :--- | :--- | :---: | :---: | :--- |
| RFC 0192 | Associated items | ✅ | 1.0 | `01_traits.md` |
| RFC 0445 | Allow overloading of `*` / `&` | ❌ | — | — |
| RFC 0738 | Variadic generics | ❌ | — | — |
| RFC 1023 | Rebalancing coherence / orphan rules | ✅ | 1.0 | `01_traits.md` §4.1 |
| RFC 1053 | Allow overloading shift operators | ✅ | 1.0 | — |
| RFC 1156 | Adjust default object bounds | ✅ | 1.17 | `01_traits.md` |
| RFC 1327 | Dropck eyepatch | ✅ | 1.13 | `03_memory_management.md` |
| RFC 1951 | Expand `where` clause syntax | ✅ | 1.23 | `02_generics.md` |
| RFC 2289 | Associated type constructors | 🚧 | — | `01_traits.md` §4.6 |

## 三、内存模型与 Unsafe

| RFC | 标题 | 状态 | 稳定版本 | 概念文件 |
| :--- | :--- | :---: | :---: | :--- |
| RFC 0769 | Sound generic drop | ✅ | 1.0 | `03_memory_management.md` |
| RFC 1861 | Extern types | 🚧 | nightly | `05_rust_ffi.md` |
| RFC 2581 | `&mut` reborrows for `DerefMut` | ✅ | — | `02_borrowing.md` |
| RFC 2753 | Union types | ✅ | 1.19 | `04_type_system.md` |
| RFC 2807 | Target feature support | ✅ | 1.27 | `03_unsafe.md` |
| RFC 2835 | Type alias enum variants | ✅ | 1.37 | `04_type_system.md` |

## 四、并发与异步

| RFC | 标题 | 状态 | 稳定版本 | 概念文件 |
| :--- | :--- | :---: | :---: | :--- |
| RFC 1299 | Incremental compilation | ✅ | 1.24 | — |
| RFC 2010 | Integer atomics | ✅ | 1.34 | `01_concurrency.md` §3.1 |
| RFC 2052 | Epochs (后发展为 Edition) | ⚠️ | — | `05_rust_version_tracking.md` |
| RFC 2592 | Futures and async/await | ✅ | 1.36 | `02_async.md` §3.1 |

## 五、Edition 与工具链

| RFC | 标题 | 状态 | 稳定版本 | 概念文件 |
| :--- | :--- | :---: | :---: | :--- |
| RFC 2052 | Epochs (后发展为 Edition) | ⚠️ | — | `22_edition_guide.md` |
| RFC 3086 | Macro metavariable expressions | ✅ | 1.60 | `04_macros.md` |
| RFC 3101 | Reserved prefixes | ✅ | 1.53 (2021Ed) | `22_edition_guide.md` |
| RFC 3501 | Edition 2024 | ✅ | 1.85 | `22_edition_guide.md` |

## 六、前沿提案（Preview / Unstable）

| RFC/跟踪 | 标题 | 状态 | 目标版本 | 概念文件 |
| :--- | :--- | :---: | :---: | :--- |
| RFC 3627 | Return type notation (RTN) | 🚧 | nightly | `12_return_type_notation_preview.md` |
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
> **[来源: RFC 2394 — async/await]** 引入 `async`/`await` 语法糖...
> **状态**: ✅ Implemented (Rust 1.39) | 替代方案: RFC 2592 (Futures)
```

### 禁止格式

```markdown
❌ [来源: RFCs]  # 无编号
❌ [来源: RFC 2394]  # 无标题
❌ RFC 2394 (无状态标注)
```

---

## 变更日志

| 日期 | 变更 |
|:---|:---|
| 2026-05-24 | 初始建立，覆盖 40 个关键 RFC |
