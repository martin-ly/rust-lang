# C02 Type System - Master Index (English)

> **Version**: 1.0 | **Rust**: 1.93.0+ | **Last Update**: 2026-02-13
> **Full Chinese version**: [00_MASTER_INDEX.md](./00_MASTER_INDEX.md)

---

## Official Resources

| Resource | Link |
| :--- | :--- |
| **The Rust Book** | [Ch. 10 Generic Types, Traits, and Lifetimes](https://doc.rust-lang.org/book/ch10-00-generics.html) |
| **Rust By Example** | [Custom Types](https://doc.rust-lang.org/rust-by-example/custom_types.html) |
| **Rust Reference** | [Type system](https://doc.rust-lang.org/reference/types.html) |
| **Rustonomicon** | [Subtyping and Variance](https://doc.rust-lang.org/nomicon/subtyping.html) |

**Rust 1.93 Compatibility**: [Compatibility Notes](../../../docs/06_toolchain/06_rust_1.93_compatibility_notes.md) | [Deep Dive](../../../docs/06_toolchain/09_rust_1.93_compatibility_deep_dive.md)

---

## Quick Navigation

### By Role

- **Beginner**: [Project Overview](tier_01_foundations/01_项目概览.md) | [Glossary](tier_01_foundations/03_术语表.md) | [FAQ](tier_01_foundations/04_常见问题.md)
- **Intermediate**: [Basic Types Guide](tier_02_guides/01_基础类型指南.md) | [Generics Guide](tier_02_guides/03_泛型编程指南.md) | [Trait System Guide](tier_02_guides/04_Trait系统指南.md)
- **Advanced**: [Type System Spec](tier_03_references/01_类型系统规范.md) | [Variance Reference](tier_03_references/02_类型型变参考.md) | [Dispatch Reference](tier_03_references/03_分派机制参考.md)

### Tier Structure

| Tier | Name | Entry |
| :--- | :--- | :--- |
| **Tier 1** | Foundation | [tier_01_foundations/](tier_01_foundations/README.md) |
| **Tier 2** | Core Guides | [tier_02_guides/](tier_02_guides/) |
| **Tier 3** | References | [tier_03_references/](tier_03_references/) |
| **Tier 4** | Advanced | [tier_04_advanced/](tier_04_advanced/) |

---

## Cargo Package Management

Standalone Cargo documentation covering dependency management, features, workspaces:

- [Cargo Package Management Index](cargo_package_management/00_INDEX.md)

---

## Rust Version Features

- [Rust 1.91 Type System Improvements](RUST_191_TYPE_SYSTEM_IMPROVEMENTS.md)
- [Rust 1.92 Type System Improvements](RUST_192_TYPE_SYSTEM_IMPROVEMENTS.md)
- [Rust 1.92 Examples Collection](RUST_192_EXAMPLES_COLLECTION.md)

---

## Code Examples

```bash
# Run examples
cargo run -p c02_type_system --example <example_name>

# Run all tests
cargo test -p c02_type_system
```

---

## Cheatsheet & Rustlings

- **Cheatsheet**: [generics_cheatsheet](../../../docs/02_reference/quick_reference/generics_cheatsheet.md) | [type_system](../../../docs/02_reference/quick_reference/type_system.md)
- **Rustlings**: [04_primitive_types](https://github.com/rust-lang/rustlings/tree/main/exercises/04_primitive_types), [07_structs](https://github.com/rust-lang/rustlings/tree/main/exercises/07_structs), [08_enums](https://github.com/rust-lang/rustlings/tree/main/exercises/08_enums), [15_traits](https://github.com/rust-lang/rustlings/tree/main/exercises/15_traits)

---

## Related

- [Project README](../../../README.md)
- [Rustlings Mapping](../../../exercises/RUSTLINGS_MAPPING.md)
- [Official Resources Mapping](../../../docs/01_learning/OFFICIAL_RESOURCES_MAPPING.md)
