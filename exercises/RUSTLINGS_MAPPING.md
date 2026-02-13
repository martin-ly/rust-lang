# Rustlings 习题与项目模块映射表

> **创建日期**: 2026-02-13  
> **用途**: 本项目 C01–C12 模块 ↔ Rustlings 习题主题对应  
> **Rustlings 仓库**: <https://github.com/rust-lang/rustlings>

---

## 快速开始

```bash
# 安装并运行 Rustlings
cargo install rustlings
rustlings watch
```

---

## 模块 ↔ Rustlings 主题映射

| 本项目模块 | Rustlings 主题 | 对应目录 | 学习顺序建议 |
|------------|----------------|----------|--------------|
| **C01 所有权与借用** | 06_move_semantics, 16_lifetimes, 19_smart_pointers | exercises/06_move_semantics, 16_lifetimes, 19_smart_pointers | 先 06 → 16 → 19 |
| **C02 类型系统** | 04_primitive_types, 07_structs, 08_enums, 15_traits | exercises/04_primitive_types, 07_structs, 08_enums, 15_traits | 04 → 07 → 08 → 15 |
| **C03 控制流与函数** | 01_variables, 02_functions, 03_if, 12_options, 13_error_handling, 18_iterators | exercises/01_variables, 02_functions, 03_if, 12_options, 13_error_handling, 18_iterators | 01 → 02 → 03 → 12 → 13 → 18 |
| **C04 泛型编程** | 14_generics | exercises/14_generics | 学完 C02/C03 后 |
| **C05 线程与并发** | 20_threads | exercises/20_threads | 学完 C01/C02 后 |
| **C06 异步编程** | - | Rustlings 无异步专题 | 参考 [RBE Async](https://doc.rust-lang.org/rust-by-example/async.html) |
| **C07 进程管理** | - | Rustlings 无进程专题 | 参考 [RBE Process](https://doc.rust-lang.org/rust-by-example/std_misc/process.html) |
| **C08 算法** | 05_vecs, 11_hashmaps, 18_iterators | exercises/05_vecs, 11_hashmaps, 18_iterators | 集合与迭代器 |
| **C09 设计模式** | 07_structs, 08_enums, 15_traits | 综合运用 | 无直接对应 |
| **C10 网络** | - | Rustlings 无网络专题 | 参考 C10 模块 |
| **C11 宏系统** | 21_macros | exercises/21_macros | 学完基础后 |
| **C12 WASM** | - | Rustlings 无 WASM 专题 | 参考 C12 模块 |

---

## Rustlings 完整主题列表（按顺序）

| 序号 | 主题 | 本项目对应 | RBE 对应 |
|------|------|------------|----------|
| 00 | intro | 入门 | - |
| 01 | variables | C03 变量 | [Variables](https://doc.rust-lang.org/rust-by-example/variable_bindings.html) |
| 02 | functions | C03 函数 | [Functions](https://doc.rust-lang.org/rust-by-example/fn.html) |
| 03 | if | C03 控制流 | [If/Else](https://doc.rust-lang.org/rust-by-example/flow_control/if_else.html) |
| 04 | primitive_types | C02 类型 | [Primitive Types](https://doc.rust-lang.org/rust-by-example/primitives.html) |
| 05 | vecs | C08 集合 | [Vectors](https://doc.rust-lang.org/rust-by-example/std/vec.html) |
| 06 | move_semantics | C01 所有权 | [Move](https://doc.rust-lang.org/rust-by-example/scope/move.html) |
| 07 | structs | C02 结构体 | [Structs](https://doc.rust-lang.org/rust-by-example/custom_types/structs.html) |
| 08 | enums | C02/C03 枚举 | [Enums](https://doc.rust-lang.org/rust-by-example/custom_types/enum.html) |
| 09 | strings | C03 字符串 | [Strings](https://doc.rust-lang.org/rust-by-example/std/str.html) |
| 10 | modules | C02 模块 | [Modules](https://doc.rust-lang.org/rust-by-example/mod.html) |
| 11 | hashmaps | C08 集合 | [HashMap](https://doc.rust-lang.org/rust-by-example/std/hash.html) |
| 12 | options | C03 Option | [Option](https://doc.rust-lang.org/rust-by-example/std/option.html) |
| 13 | error_handling | C03 错误处理 | [Error](https://doc.rust-lang.org/rust-by-example/error.html) |
| 14 | generics | C04 泛型 | [Generics](https://doc.rust-lang.org/rust-by-example/generics.html) |
| 15 | traits | C02 Trait | [Traits](https://doc.rust-lang.org/rust-by-example/trait.html) |
| 16 | lifetimes | C01 生命周期 | [Lifetime](https://doc.rust-lang.org/rust-by-example/scope/lifetime.html) |
| 17 | tests | 测试 | [Testing](https://doc.rust-lang.org/rust-by-example/testing.html) |
| 18 | iterators | C03/C08 迭代器 | [Iterator](https://doc.rust-lang.org/rust-by-example/trait/iter.html) |
| 19 | smart_pointers | C01 智能指针 | [Box](https://doc.rust-lang.org/rust-by-example/std/box.html) |
| 20 | threads | C05 线程 | [Threads](https://doc.rust-lang.org/rust-by-example/std_misc/threads.html) |
| 21 | macros | C11 宏 | [Macros](https://doc.rust-lang.org/rust-by-example/macros.html) |
| 22 | clippy | 代码质量 | - |
| 23 | conversions | C02 From/Into | [Conversion](https://doc.rust-lang.org/rust-by-example/conversion.html) |
| - | quizzes | 测验 | - |

---

## 推荐学习路径

### 路径 A：Rustlings 先行（适合零基础）

1. Rustlings 00_intro → 06_move_semantics（约 1–2 天）
2. 本项目 C01 模块（巩固所有权）
3. Rustlings 01–05, 07–09（变量、函数、类型、集合）
4. 本项目 C02、C03 模块
5. Rustlings 12–16（Option、错误、泛型、Trait、生命周期）
6. 本项目 C04、C05、C11 模块

### 路径 B：本项目先行（适合有经验者）

1. 按 C01 → C02 → C03 顺序学习
2. 每学完一模块，完成对应 Rustlings 主题巩固
3. 参考上表「本项目模块」列查找对应 Rustlings 目录

---

## 相关文档

- [exercises/README.md](./README.md) - 交互式练习入口
- [OFFICIAL_RESOURCES_MAPPING](../docs/01_learning/OFFICIAL_RESOURCES_MAPPING.md) - 官方资源映射
- [Rustlings 官方](https://github.com/rust-lang/rustlings)
- [Rust by Example](https://doc.rust-lang.org/rust-by-example/)
