# C02 类型系统示例

本目录包含 `c02_type_system` crate 的可运行示例，覆盖从基础类型到高级类型技巧的 Rust 代码。

---

## 📚 示例列表

### 基础与自定义类型

| 示例 | 描述 | 运行命令 |
|------|------|----------|
| `basic_types.rs` | 标量、复合、引用与切片 | `cargo run --example basic_types -p c02_type_system` |
| `type_inference.rs` | 类型推断与显式标注 | `cargo run --example type_inference -p c02_type_system` |
| `type_definition_examples.rs` | `struct`/`enum` 定义与使用 | `cargo run --example type_definition_examples -p c02_type_system` |
| `type_equivalence_newtype_examples.rs` | Newtype 模式与类型等价 | `cargo run --example type_equivalence_newtype_examples -p c02_type_system` |
| `newtype_pattern.rs` | Newtype 与 Identifier trait | `cargo run --example newtype_pattern -p c02_type_system` |
| `pattern_matching_advanced.rs` | 高级模式匹配与穷尽性 | `cargo run --example pattern_matching_advanced -p c02_type_system` |

### 类型系统前沿特性

| 示例 | 描述 | 运行命令 |
|------|------|----------|
| `never_type_control_flow.rs` | `!` never 类型在控制流中的应用 | `cargo run --example never_type_control_flow -p c02_type_system` |
| `const_eval_assoc_consts.rs` | 常量求值与关联常量 | `cargo run --example const_eval_assoc_consts -p c02_type_system` |
| `generics_where_performance.rs` | 泛型、`where` 子句与零成本抽象 | `cargo run --example generics_where_performance -p c02_type_system` |
| `variance_examples.rs` | 协变/逆变/不变示例 | `cargo run --example variance_examples -p c02_type_system` |
| `variance_demo.rs` | 型变核心概念演示 | `cargo run --example variance_demo -p c02_type_system` |
| `phantom_types.rs` | PhantomData 与类型级状态机 | `cargo run --example phantom_types -p c02_type_system` |
| `trait_objects_safety.rs` | trait object 与对象安全 | `cargo run --example trait_objects_safety -p c02_type_system` |

### 内存布局与 unsafe 类型

| 示例 | 描述 | 运行命令 |
|------|------|----------|
| `repr_packed_safety.rs` | `repr(packed)` 与内存对齐 | `cargo run --example repr_packed_safety -p c02_type_system` |
| `maybeuninit_manuallydrop.rs` | `MaybeUninit` / `ManuallyDrop` | `cargo run --example maybeuninit_manuallydrop -p c02_type_system` |
| `nonnull_raw_pointers.rs` | 非空裸指针类型 | `cargo run --example nonnull_raw_pointers -p c02_type_system` |
| `unsafe_cell_interior_mutability.rs` | `UnsafeCell` 与内部可变性 | `cargo run --example unsafe_cell_interior_mutability -p c02_type_system` |
| `pin_self_referential_basics.rs` | `Pin` 与自引用类型 | `cargo run --example pin_self_referential_basics -p c02_type_system` |

### 标准库与生态

| 示例 | 描述 | 运行命令 |
|------|------|----------|
| `standard_library_comprehensive_guide.rs` | 标准库类型综合演示 | `cargo run --example standard_library_comprehensive_guide -p c02_type_system` |
| `iterators_zero_cost.rs` | 迭代器适配器与零成本抽象 | `cargo run --example iterators_zero_cost -p c02_type_system` |
| `open_source_ecosystem_examples.rs` | 开源生态中的类型模式 | `cargo run --example open_source_ecosystem_examples -p c02_type_system` |
| `modern_rust_patterns_2025.rs` | 现代 Rust 惯用法 | `cargo run --example modern_rust_patterns_2025 -p c02_type_system` |
| `rust_best_practices_vs_antipatterns.rs` | 最佳实践与反模式 | `cargo run --example rust_best_practices_vs_antipatterns -p c02_type_system` |
| `ffi_abi_repr.rs` | FFI 与 `extern "C"` 类型 | `cargo run --example ffi_abi_repr -p c02_type_system` |
| `non_exhaustive_compat.rs` | `#[non_exhaustive]` 兼容性 | `cargo run --example non_exhaustive_compat -p c02_type_system` |

### Rust 版本特性示例

| 示例 | 描述 | 运行命令 |
|------|------|----------|
| `vec_push_mut_demo.rs` | `Vec::push_mut` / `insert_mut` | `cargo run --example vec_push_mut_demo -p c02_type_system` |
| `cold_path_demo.rs` | `core::hint::cold_path` | `cargo run --example cold_path_demo -p c02_type_system` |
| `bool_try_from_demo.rs` | `bool::TryFrom<{integer}>` | `cargo run --example bool_try_from_demo -p c02_type_system` |

### 批量运行

| 示例 | 描述 | 运行命令 |
|------|------|----------|
| `run_all_examples.rs` | 顺序运行多个示例 | `cargo run --example run_all_examples -p c02_type_system` |

---

## 🚀 快速开始

```bash
# 运行类型定义示例
cargo run --example type_definition_examples -p c02_type_system

# 运行模式匹配示例
cargo run --example pattern_matching_advanced -p c02_type_system

# 运行高级类型示例
cargo run --example variance_examples -p c02_type_system
```
---

## 📖 学习路径

1. **基础**：`type_definition_examples` → `type_equivalence_newtype_examples` → `pattern_matching_advanced`
2. **进阶**：`variance_examples` → `trait_objects_safety` → `generics_where_performance`
3. **高级**：`pin_self_referential_basics` → `unsafe_cell_interior_mutability` → `const_eval_assoc_consts`

---

## 🔗 相关文档

- [C02 文档首页](../docs/README.md)
- [类型系统快速参考](../../../docs/02_reference/quick_reference/type_system.md)
- [Rust Reference](https://doc.rust-lang.org/reference/)

---

*示例基于 Rust 1.96+，Edition 2024*

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)

**文档版本**: 1.2
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-06-24
**状态**: 🔄 随源码重构持续更新
