# 编译器错误码 → 本项目文档映射

> **创建日期**: 2026-02-13
> **用途**: 常见 Rust 编译器错误码快速定位到本项目文档与示例
> **权威源**: [Compiler Error Index](https://doc.rust-lang.org/error-index.html)

---

## 快速查找

遇到编译错误时，根据错误码（如 `E0382`）在下表查找本项目对应文档。

---

## 所有权与借用 (E03xx)

| 错误码 | 典型信息 | 本项目文档 | 速查卡 |
| :--- | :--- | :--- | :--- || **E0382** | borrow of moved value | [TROUBLESHOOTING 所有权错误](../05_guides/TROUBLESHOOTING_GUIDE.md#1-所有权错误) | [ownership_cheatsheet](quick_reference/ownership_cheatsheet.md) |
| **E0383** | partial move / borrow of partially moved value | C01 所有权、[EDGE_CASES](./EDGE_CASES_AND_SPECIAL_CASES.md) | ownership_cheatsheet |
| **E0384** | cannot assign twice to immutable variable | C03 控制流 | control_flow_functions_cheatsheet |
| **E0499** | cannot borrow as mutable more than once | C01 借用检查器 | ownership_cheatsheet |
| **E0502** | cannot borrow as immutable (already borrowed as mutable) | C01 借用规则 | ownership_cheatsheet |
| **E0503** | cannot use (value was moved) | C01 所有权 | ownership_cheatsheet |
| **E0505** | cannot move out of (value is borrowed) | C01 借用与移动 | ownership_cheatsheet |
| **E0506** | cannot assign to (borrowed) | C01 借用 | ownership_cheatsheet |
| **E0507** | cannot move out of borrowed content | C01 借用检查器 | ownership_cheatsheet |

---

## 生命周期 (E05xx)

| 错误码 | 典型信息 | 本项目文档 | 速查卡 |
| :--- | :--- | :--- | :--- || **E0597** | does not live long enough | [TROUBLESHOOTING 生命周期](../05_guides/TROUBLESHOOTING_GUIDE.md#2-生命周期错误) | [type_system](quick_reference/type_system.md) |
| **E0599** | no method named ... for type | C02 Trait、C04 泛型 | type_system、generics_cheatsheet |
| **E0609** | no field ... on type | C02 结构体、C03 枚举 | type_system |
| **E0614** | expected ... found ... (type mismatch) | C02 类型系统 | type_system |

---

## 类型系统 (E02xx, E03xx)

| 错误码 | 典型信息 | 本项目文档 | 速查卡 |
| :--- | :--- | :--- | :--- || **E0308** | mismatched types | [TROUBLESHOOTING 类型不匹配](../05_guides/TROUBLESHOOTING_GUIDE.md#3-类型不匹配) | type_system |
| **E0277** | trait bound not satisfied | C02 Trait、C04 泛型约束 | generics_cheatsheet |
| **E0282** | type annotations needed | C02 类型推断 | type_system |
| **E0283** | type annotations required | C02 类型推断 | type_system |
| **E0284** | type ... cannot be formatted | C03 格式化 | strings_formatting_cheatsheet |
| **E0310** | parameter ... may not live long enough | C01 生命周期 | type_system |
| **E0325** | overflow evaluating requirement | C04 泛型、GATs | generics_cheatsheet |

---

## 错误处理 (E0xxx)

| 错误码 | 典型信息 | 本项目文档 | 速查卡 |
| :--- | :--- | :--- | :--- || **E0433** | unresolved import | C02 模块系统 | modules_cheatsheet |
| **E0446** | private type in public interface | C02 可见性 | modules_cheatsheet |
| **E0451** | unknown attribute | C11 宏、属性 | macros_cheatsheet |
| **E0463** | can't find crate | Cargo 依赖 | cargo_cheatsheet |

---

## 异步与并发 (E0xxx)

| 错误码 | 典型信息 | 本项目文档 | 速查卡 |
| :--- | :--- | :--- | :--- || **E0373** | closure may outlive current function | C06 异步、C01 生命周期 | [async_patterns](quick_reference/async_patterns.md) |
| **E0378** | Send/Sync 相关 | C05 线程、C06 异步 | threads_concurrency_cheatsheet |
| **E0381** | borrow of moved value in async | C06 异步、持锁跨 await | async_patterns |

---

## 宏与属性 (E0xxx)

| 错误码 | 典型信息 | 本项目文档 | 速查卡 |
| :--- | :--- | :--- | :--- || **E0658** | unstable feature | 06_toolchain、Edition | - |
| **E0554** | unknown feature | Cargo features | cargo_cheatsheet |

---

## 使用建议

1. **编译错误**：复制完整错误信息，提取 `error[EXXXX]` 中的错误码
2. **查表**：在本文档中查找对应错误码
3. **跳转**：点击「本项目文档」或「速查卡」链接深入学习
4. **官方详解**：访问 [Compiler Error Index](https://doc.rust-lang.org/error-index.html) 查看完整说明

---

## 相关文档

- [故障排查指南](../05_guides/TROUBLESHOOTING_GUIDE.md)
- [边界条件与特例](./EDGE_CASES_AND_SPECIAL_CASES.md)
- [速查卡目录](quick_reference/README.md)
- [官方 Compiler Error Index](https://doc.rust-lang.org/error-index.html)
