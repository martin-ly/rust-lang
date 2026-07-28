> **内容分级**: [综述级]

# 学习入口索引（Knowledge Index）

> **EN**: Knowledge Index
> **Summary**: 导航性索引，汇总 `knowledge/` 目录下的学习入口、速查页与重定向 stub，统一指向 `concept/` 权威页。
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [初学者 / 进阶]
> **Bloom 层级**: L1-L3
> **权威来源**: 本文件为学习入口 stub，完整概念解释统一维护在 `concept/` 中。
>
> 根据 AGENTS.md §2 Canonical 规则，通用 Rust 概念解释统一维护在 `concept/` 中；
> `knowledge/` 仅保留摘要、速查与链接。

---

## 目录

- [L2 进阶概念](#l2-进阶概念)
- [L3 高级概念](#l3-高级概念)
- [L4 专家概念](#l4-专家概念)
- [L5 参考速查](#l5-参考速查)
- [L6 生态实践](#l6-生态实践)

---

## L2 进阶概念

| 文件 | 主题 | 指向 `concept/` 权威页 |
|:---|:---|:---|
| [`02_intermediate/01_collections.md`](02_intermediate/01_collections.md) | 集合类型速查 | [`concept/01_foundation/05_collections/01_collections.md`](../concept/01_foundation/05_collections/01_collections.md) |
| [`02_intermediate/05_strings.md`](02_intermediate/05_strings.md) | 字符串速查 | [`concept/01_foundation/06_strings_and_text/01_strings_and_text.md`](../concept/01_foundation/06_strings_and_text/01_strings_and_text.md) |
| [`02_intermediate/06_traits.md`](02_intermediate/06_traits.md) | Trait 系统速查 | [`concept/02_intermediate/00_traits/01_traits.md`](../concept/02_intermediate/00_traits/01_traits.md) |

## L3 高级概念

| 文件 | 主题 | 指向 `concept/` 权威页 |
|:---|:---|:---|
| [`03_advanced/02_ffi.md`](03_advanced/02_ffi.md) | FFI 入门 | [`concept/03_advanced/04_ffi/01_rust_ffi.md`](../concept/03_advanced/04_ffi/01_rust_ffi.md) |
| [`03_advanced/05_performance_optimization.md`](03_advanced/05_performance_optimization.md) | 性能优化速查 | [`concept/06_ecosystem/10_performance/01_performance_optimization.md`](../concept/06_ecosystem/10_performance/01_performance_optimization.md) |
| [`03_advanced/unsafe/README.md`](03_advanced/unsafe/README.md) | Unsafe Rust 学习入口 | [`concept/03_advanced/02_unsafe/01_unsafe.md`](../concept/03_advanced/02_unsafe/01_unsafe.md) |
| [`03_advanced/unsafe/03_unsafe_rust.md`](03_advanced/unsafe/03_unsafe_rust.md) | Unsafe Rust 速查 | [`concept/03_advanced/02_unsafe/01_unsafe.md`](../concept/03_advanced/02_unsafe/01_unsafe.md) |

## L4 专家概念

| 文件 | 主题 | 指向 `concept/` 权威页 |
|:---|:---|:---|
| [`04_expert/01_compiler_internals.md`](04_expert/01_compiler_internals.md) | 编译器内部速查 | [`concept/06_ecosystem/00_toolchain/04_compiler_internals.md`](../concept/06_ecosystem/00_toolchain/04_compiler_internals.md) |
| [`04_expert/miri/01_tree_borrows.md`](04_expert/miri/01_tree_borrows.md) | Tree Borrows 速查 | [`concept/04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md`](../concept/04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md) |

## L5 参考速查

| 文件 | 主题 | 指向 `concept/` 权威页 |
|:---|:---|:---|
| [`05_reference/03_std_library_cheatsheet.md`](05_reference/03_std_library_cheatsheet.md) | 标准库速查 | [`concept/01_foundation/05_collections/01_collections.md`](../concept/01_foundation/05_collections/01_collections.md) 等 |

## L6 生态实践

| 文件 | 主题 | 指向 `concept/` 权威页 |
|:---|:---|:---|
| [`06_ecosystem/02_edition_2024.md`](06_ecosystem/02_edition_2024.md) | Edition 2024 速查 | [`concept/07_future/01_edition_roadmap/02_edition_guide.md`](../concept/07_future/01_edition_roadmap/02_edition_guide.md) |
| [`06_ecosystem/databases/02_sqlx_deep_dive.md`](06_ecosystem/databases/02_sqlx_deep_dive.md) | sqlx 深度实践 | [`concept/06_ecosystem/06_data_and_distributed/02_database_access.md`](../concept/06_ecosystem/06_data_and_distributed/02_database_access.md) |

---

## 使用建议

1. **学习路径**：从 [`concept/00_meta/04_navigation/08_learning_mvp_path.md`](../concept/00_meta/04_navigation/08_learning_mvp_path.md) 开始，遇到具体概念时通过本索引定位速查页。
2. **贡献规范**：新增 `knowledge/` 文件时，必须在本索引中注册，并确保正文为 stub/摘要/速查，不重复 `concept/` 权威页正文。
3. **维护频率**：每次 `concept/` 权威页重命名或新增时，同步更新本索引。
