# Rustc 错误码与反例边界对齐索引 {#rustc-错误码与反例边界对齐索引}

> **EN**: Rustc Errors Alignment
> **Summary**: Rustc 错误码与反例边界对齐索引 Rustc Errors Alignment.
> **概念族**: 权威来源对齐 / rustc 错误码
> **内容分级**: [核心级]
> **层级**: L6
> **Bloom 层级**: L5-L6
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [Rustc 错误码与反例边界对齐索引 {#rustc-错误码与反例边界对齐索引}](#rustc-错误码与反例边界对齐索引-rustc-错误码与反例边界对齐索引)
  - [目录 {#目录}](#目录-目录)
  - [一、对齐说明 {#一对齐说明}](#一对齐说明-一对齐说明)
  - [二、所有权（Ownership）与借用（Borrowing）错误 {#二所有权与借用错误}](#二所有权与借用错误-二所有权与借用错误)
  - [三、类型系统（Type System）错误 {#三类型系统错误}](#三类型系统错误-三类型系统错误)
  - [四、模块（Module）与可见性错误 {#四模块与可见性错误}](#四模块与可见性错误-四模块与可见性错误)
  - [五、并发与 unsafe 错误 {#五并发与-unsafe-错误}](#五并发与-unsafe-错误-五并发与-unsafe-错误)
  - [六、生命周期（Lifetimes）错误 {#六生命周期错误}](#六生命周期错误-六生命周期错误)
  - [七、未覆盖缺口 {#七未覆盖缺口}](#七未覆盖缺口-七未覆盖缺口)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、对齐说明 {#一对齐说明}

本文档将项目反例边界文件中提到的 rustc 错误码与 [Rust Error Codes Index](https://doc.rust-lang.org/error_codes/error-index.html) 建立映射，便于学习者从错误码反向定位到概念解释和修复方案。

---

## 二、所有权与借用错误 {#二所有权与借用错误}

| 错误码 | 错误信息 | 项目反例 | 权威解释 |
|--------|----------|----------|----------|
| E0382 | borrow of moved value | [60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §1 | [E0382](https://doc.rust-lang.org/error_codes/E0382.html) |
| E0499 | cannot borrow as mutable more than once | [60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §2 | [E0499](https://doc.rust-lang.org/error_codes/E0499.html) |
| E0502 | cannot borrow as mutable because borrowed as immutable | [60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §3 | [E0502](https://doc.rust-lang.org/error_codes/E0502.html) |
| E0515 | cannot return reference to local variable | [60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §4 | [E0515](https://doc.rust-lang.org/error_codes/E0515.html) |

---

## 三、类型系统错误 {#三类型系统错误}

| 错误码 | 错误信息 | 项目反例 | 权威解释 |
|--------|----------|----------|----------|
| E0106 | missing lifetime specifier | [60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §4 / §7 | [E0106](https://doc.rust-lang.org/error_codes/E0106.html) |
| E0277 | trait bound not satisfied / size not known | [60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §3 | [E0277](https://doc.rust-lang.org/error_codes/E0277.html) |
| E0117 | only traits defined in current crate can be implemented | [60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §5 | [E0117](https://doc.rust-lang.org/error_codes/E0117.html) |
| E0184 | Copy may not be implemented for this type | [60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §7 | [E0184](https://doc.rust-lang.org/error_codes/E0184.html) |
| E0221 | ambiguous associated type | [60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §6 | [E0221](https://doc.rust-lang.org/error_codes/E0221.html) |

---

## 四、模块与可见性错误 {#四模块与可见性错误}

| 错误码 | 错误信息 | 项目反例 | 权威解释 |
|--------|----------|----------|----------|
| E0428 | name defined multiple times | [60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §2 | [E0428](https://doc.rust-lang.org/error_codes/E0428.html) |
| E0433 | failed to resolve | [60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §1 / §3 | [E0433](https://doc.rust-lang.org/error_codes/E0433.html) |
| E0583 | file not found for module | [60_module_counterexamples.md](formal_modules/60_module_counterexamples.md) §2 | [E0583](https://doc.rust-lang.org/error_codes/E0583.html) |

---

## 五、并发与 unsafe 错误 {#五并发与-unsafe-错误}

| 错误码 | 错误信息 | 项目反例 | 权威解释 |
|--------|----------|----------|----------|
| E0277 | `Rc<T>` cannot be sent between threads safely | [60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) §1 | [E0277](https://doc.rust-lang.org/error_codes/E0277.html) |
| E0133 | call to unsafe function requires unsafe function or block | [60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) §2 | [E0133](https://doc.rust-lang.org/error_codes/E0133.html) |

---

## 六、生命周期错误 {#六生命周期错误}

| 错误码 | 错误信息 | 项目反例 | 权威解释 |
|--------|----------|----------|----------|
| E0106 | missing lifetime specifier | [60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) §7 | [E0106](https://doc.rust-lang.org/error_codes/E0106.html) |
| lifetime mismatch | lifetime may not live long enough | [60_type_system_counterexamples.md](type_theory/60_type_system_counterexamples.md) §2 | [Lifetime Errors](https://doc.rust-lang.org/error_codes/E0621.html) |

---

## 七、未覆盖缺口 {#七未覆盖缺口}

1. 宏（Macro）系统错误码（Exxxx）可进一步整理。
2. 编译器 warnings（如 `unsafe_op_in_unsafe_fn`）与 Edition 2024 变化可补充。
3. 未来可自动生成「项目反例 → rustc 错误码」反向索引。

> **权威来源**: [Rust Error Codes Index](https://doc.rust-lang.org/error_codes/error-index.html) | [rustc-dev-guide – Diagnostics](https://rustc-dev-guide.rust-lang.org/diagnostics.html)

## 相关概念 {#相关概念}

- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [Rust Reference 对齐](10_rust_reference_alignment.md)
- [各主题反例边界文件](10_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)

## 社区权威参考 {#社区权威参考}

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)
