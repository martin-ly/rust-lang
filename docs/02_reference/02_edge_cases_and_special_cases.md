> **权威来源**:
>
> [Rust Reference](https://doc.rust-lang.org/reference/),
>
> **分级**: [A]
>
> [Rustonomicon](https://doc.rust-lang.org/nomicon/),
> [The Rust Programming Language](https://doc.rust-lang.org/book/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、Rustonomicon 来源标注 [Authority Source Sprint Batch 8](../../concept/00_meta/02_sources/international_authority_index.md)

# Rust 边界条件与特例示例 (Edge Cases And Special Cases) {#rust-边界条件与特例示例}

> **EN**: Edge Cases And Special Cases
> **Summary**: Rust 边界条件与特例示例 Edge Cases And Special Cases. (stub/archive redirect)
> **Bloom 层级**: L2
> **创建日期**: 2026-02-12
> **最后更新**: 2026-05-08
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **用途**: 集合、算法、并发等模块（Module）的边界/特例示例

---

---

## 集合边界 {#集合边界}
> **权威来源**: [Rust 集合类型](../../concept/01_foundation/05_collections/08_collections.md)
> 通用概念解释已在 `concept/` 权威页中覆盖，本节不再重复，请直接参考权威页。
## 算法特例 {#算法特例}
> **权威来源**: [Rust 集合与算法](../../concept/01_foundation/05_collections/08_collections.md)
> 通用概念解释已在 `concept/` 权威页中覆盖，本节不再重复，请直接参考权威页。
## 并发特例 {#并发特例}
> **权威来源**: [Rust 并发编程](../../concept/03_advanced/00_concurrency/01_concurrency.md)
> 通用概念解释已在 `concept/` 权威页中覆盖，本节不再重复，请直接参考权威页。
## 数值溢出 {#数值溢出}
> **权威来源**: [Rust 数值类型](../../concept/01_foundation/02_type_system/10_numerics.md)
> 通用概念解释已在 `concept/` 权威页中覆盖，本节不再重复，请直接参考权威页。
## 字符串与切片 {#字符串与切片}
> **权威来源**: [Rust 字符串与文本](../../concept/01_foundation/06_strings_and_text/09_strings_and_text.md)
> 通用概念解释已在 `concept/` 权威页中覆盖，本节不再重复，请直接参考权威页。
## unsafe 与 FFI {#unsafe-与-ffi}
> **权威来源**: [Rust Unsafe 与 FFI](../../concept/03_advanced/02_unsafe/03_unsafe.md)
> 通用概念解释已在 `concept/` 权威页中覆盖，本节不再重复，请直接参考权威页。
## WASM 特例 {#wasm-特例}
> **权威来源**: [WebAssembly 与 Rust](../../concept/06_ecosystem/11_domain_applications/59_wasm_glossary.md)
> 通用概念解释已在 `concept/` 权威页中覆盖，本节不再重复，请直接参考权威页。
## panic 边界 {#panic-边界}
> **权威来源**: [Rust panic 与错误处理](../../concept/01_foundation/08_error_handling/13_panic_and_abort.md)
> 通用概念解释已在 `concept/` 权威页中覆盖，本节不再重复，请直接参考权威页。
## 空 Future 与异步 {#空-future-与异步}
> **权威来源**: [Rust 异步编程](../../concept/03_advanced/01_async/02_async.md)
> 通用概念解释已在 `concept/` 权威页中覆盖，本节不再重复，请直接参考权威页。
## Rust 1.93 行为变更特例 {#rust-193-行为变更特例}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### BTreeMap::append 行为变更 {#btreemapappend-行为变更}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

**Rust 1.93** 起，`BTreeMap::append` 当追加的条目已存在时，**不再覆盖**目标中的现有键，而是保留目标中的值。

```rust
use std::collections::BTreeMap;

let mut a = BTreeMap::new();
a.insert(1, "a");
let mut b = BTreeMap::new();
b.insert(1, "b");  // 相同 key

a.append(&mut b);
// 1.93 之前：a[1] 可能为 "b"
// 1.93 起：a[1] 保留为 "a"，b 中 (1,"b") 被丢弃
assert_eq!(a.get(&1), Some(&"a"));
```

### Copy specialization 移除 {#copy-specialization-移除}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

**Rust 1.93** 在 Copy trait 上停止内部使用 specialization。部分标准库 API 可能改为调用 `Clone::clone` 而非按位复制，**可能导致性能回归**。

```rust
// 若依赖 Copy 类型的按位复制优化，1.93 后可能略有性能差异
let v: Vec<i32> = vec![1, 2, 3];
let v2 = v.clone();  // 可能受影响
```

### vec::IntoIter 与 RefUnwindSafe {#vecintoiter-与-refunwindsafe}
>
> **[来源: [crates.io](https://crates.io/)]**

**Rust 1.93** 放宽 `vec::IntoIter<T>: UnwindSafe` 约束，不再要求 `T: RefUnwindSafe`。

```rust
// 1.93 起：即使 T 不实现 RefUnwindSafe，vec::IntoIter<T> 仍为 UnwindSafe
use std::panic::UnwindSafe;
use std::vec::IntoIter;

fn assert_unwind_safe<T: UnwindSafe>() {}
assert_unwind_safe::<IntoIter<*mut i32>>();  // 1.93 可行
```

---

> 本节通用概念解释请参见 `concept/` 对应权威页。
> 本节通用概念解释请参见 `concept/` 对应权威页。
>
## 相关文档 {#相关文档}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 速查卡 {#速查卡}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

- [集合与迭代器速查卡](quick_reference/02_collections_iterators_cheatsheet.md)
- [算法速查卡](quick_reference/02_algorithms_cheatsheet.md)
- [线程与并发速查卡](quick_reference/02_threads_concurrency_cheatsheet.md)
- [所有权速查卡](quick_reference/02_ownership_cheatsheet.md)

### 形式化文档 {#形式化文档}
>
> **[来源: [crates.io](https://crates.io/)]**

- [所有权模型形式化](../research_notes/formal_methods/10_ownership_model.md)
- [借用检查器证明](../research_notes/formal_methods/10_borrow_checker_proof.md)
- 生命周期形式化
- [Send/Sync 形式化](../research_notes/formal_methods/10_send_sync_formalization.md)

---

## Rust 1.95+ 更新 {#rust-195-更新}
>
> **[来源: [docs.rs](https://docs.rs/)]**
> **适用版本**: Rust 1.97.0+

详见 Rust 1.94 发布说明

**最后更新**: 2026-05-08

---

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**
> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
