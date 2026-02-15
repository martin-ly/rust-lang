# Rust 1.93 相关反例与边界集中索引

> **创建日期**: 2026-02-14
> **最后更新**: 2026-02-14
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **用途**: 集中列出与 Rust 1.93 变更相关的反例与边界情况，便于迁移与形式化文档交叉引用
> **上位**: [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md)、[FORMAT_AND_CONTENT_ALIGNMENT_PLAN](FORMAT_AND_CONTENT_ALIGNMENT_PLAN.md)

---

## 📊 目录

- [Rust 1.93 相关反例与边界集中索引](#rust-193-相关反例与边界集中索引)
  - [📊 目录](#-目录)
  - [1.93 新增/变更相关反例](#193-新增变更相关反例)
  - [与形式化/设计文档的衔接](#与形式化设计文档的衔接)

---

## 1.93 新增/变更相关反例

| 特性/变更 | 反例或边界说明 | 形式化/设计文档 |
| :--- | :--- | :--- |
| **deref_nullptr** | 对空指针解引用为未定义行为；`*ptr` 当 `ptr.is_null()` 时 UB | [borrow_checker_proof](formal_methods/borrow_checker_proof.md)、[ownership_model](formal_methods/ownership_model.md) |
| **C variadic** | FFI 中 C 风格可变参数；类型与 ABI 必须与 C 端一致，否则未定义行为 | [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) § 9. FFI |
| **const &mut in static** | `static` 中 `&mut` 的约束与 `const` 求值；不当使用导致编译错误或语义差异 | [advanced_types](type_theory/advanced_types.md)、[RUST_193](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) § 8. 常量与编译期 |
| **Copy 特化移除** | 不再允许为仅部分类型参数实现 Copy 的特化；反例：仅对 `T: Copy` 特化 Copy 的泛型 | [trait_system_formalization](type_theory/trait_system_formalization.md)、[RUST_193](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) § 10. 1.93 新增 |
| **offset_of!** | 对非 `packed` 或零大小字段的用法、跨 crate 稳定性；不当字段导致编译错误 | [RUST_193](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) § 10. 1.93 新增 |
| **asm_cfg / target_cfg** | `asm!` 与 `cfg` 组合下目标不支持时的回退；错误配置导致编译失败 | [RUST_193](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) § 9. FFI、§ 10 |
| **LUB coercion** | 分支类型 LUB 与自动强转；若类型不兼容仍会报错，反例为过度依赖隐式 LUB 导致的可读性下降 | [type_system_foundations](type_theory/type_system_foundations.md)、[RUST_193](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) § 2. 类型系统 |
| **全局分配器 / thread_local** | 分配器与 thread_local 的初始化顺序；错误依赖导致未定义行为或崩溃 | [ownership_model](formal_methods/ownership_model.md)、[RUST_193](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md) § 1. 内存与所有权 |
| **lint 变更** | 1.93 默认启用或升级的 lint；旧代码可能新增警告或错误，需按发布说明迁移 | [INCREMENTAL_UPDATE_FLOW](INCREMENTAL_UPDATE_FLOW.md)、releases.rs 1.93.0 |

---

## 与形式化/设计文档的衔接

- **所有权/借用**：deref_nullptr、全局分配器反例见 [formal_methods](formal_methods/README.md) 六篇并表与 [borrow_checker_proof](formal_methods/borrow_checker_proof.md)。
- **类型/Trait**：Copy 特化移除、const/static 边界见 [type_theory](type_theory/README.md)、[trait_system_formalization](type_theory/trait_system_formalization.md)、[advanced_types](type_theory/advanced_types.md)。
- **92 项特性与反例**：每项特性的动机/形式化/反例见 [RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS](RUST_193_LANGUAGE_FEATURES_COMPREHENSIVE_ANALYSIS.md)；本索引仅作 1.93 相关反例的集中入口。

---

**维护者**: Rust Formal Methods Research Team
**最后更新**: 2026-02-14
**状态**: ✅ 与 FORMAT_AND_CONTENT_ALIGNMENT_PLAN F2.4 对齐
