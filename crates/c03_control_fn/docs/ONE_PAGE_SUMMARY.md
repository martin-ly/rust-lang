# C03 控制流与函数 - 一页纸总结

> **用途**: 快速回顾核心概念、常见坑、学习路径
> **完整文档**: [00_MASTER_INDEX](./00_MASTER_INDEX.md)

---

## 核心概念（4 条）

| 概念 | 说明 |
| :--- | :--- || **条件与循环** | `if`/`else`、`loop`/`while`/`for`；`break`/`continue` 带标签 |
| **模式匹配** | `match` 穷尽性；`if let`/`while let` 简化 |
| **Option 与 Result** | `Some`/`None`；`Ok`/`Err`；`?` 错误传播 |
| **闭包与迭代器** | `|x| x + 1`；`iter()`/`into_iter()`；链式适配器 |

---

## 常见坑与解决

| 坑 | 解决 |
| :--- | :--- || `?` 在非 Result 函数中使用 | 函数签名改为 `-> Result<T, E>` 或 `-> Option<T>` |
| 生产代码滥用 `unwrap` | 用 `?` 传播或 `match`/`map_err` 处理 |
| 混淆 Option 与 Result 语义 | 「未找到」用 Option；「可恢复错误」用 Result |
| 持锁跨 `await` | 缩短锁作用域，或使用异步友好原语 |

---

## 控制流速选

| 场景 | 选型 |
| :--- | :--- || 多分支穷尽匹配 | `match` |
| 单分支可选匹配 | `if let` |
| 错误传播 | `?` + `Result` |
| 可选值链式处理 | `map`/`and_then`/`unwrap_or` |
| 集合遍历 | `for x in iter` 或 `iter().map().collect()` |

---

## 学习路径

1. **入门** (1–2 周): 条件、循环 → Option/Result 基础 → 错误处理
2. **进阶** (2–3 周): 闭包 → 迭代器 → 模式匹配深入
3. **高级** (持续): 异步控制流、与 C06 互链

---

## 速查与练习

- **速查卡**: [control_flow_functions_cheatsheet](../../../docs/02_reference/quick_reference/control_flow_functions_cheatsheet.md) | [error_handling_cheatsheet](../../../docs/02_reference/quick_reference/error_handling_cheatsheet.md)
- **RBE 练习**: [Flow Control](https://doc.rust-lang.org/rust-by-example/flow_control.html) · [Option](https://doc.rust-lang.org/rust-by-example/std/option.html) · [Error](https://doc.rust-lang.org/rust-by-example/error.html) · [Iterator](https://doc.rust-lang.org/rust-by-example/trait/iter.html)
- **Rustlings**: [01_variables](https://github.com/rust-lang/rustlings/tree/main/exercises/01_variables) · [02_functions](https://github.com/rust-lang/rustlings/tree/main/exercises/02_functions) · [03_if](https://github.com/rust-lang/rustlings/tree/main/exercises/03_if) · [12_options](https://github.com/rust-lang/rustlings/tree/main/exercises/12_options) · [13_error_handling](https://github.com/rust-lang/rustlings/tree/main/exercises/13_error_handling) · [18_iterators](https://github.com/rust-lang/rustlings/tree/main/exercises/18_iterators)
