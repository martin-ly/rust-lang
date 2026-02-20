# C08 算法与数据结构 - 一页纸总结

> **用途**: 快速回顾核心概念、常见坑、学习路径
> **完整文档**: [00_MASTER_INDEX](./00_MASTER_INDEX.md)

---

## 核心概念（4 条）

| 概念 | 说明 |
| :--- | :--- || **集合类型** | `Vec`、`HashMap`、`BTreeMap`、`HashSet`；选型看访问模式 |
| **迭代器** | `iter()`/`into_iter()`/`iter_mut()`；适配器 `map`/`filter`/`fold` |
| **算法复杂度** | O(1)、O(log n)、O(n)；排序、搜索、图算法 |
| **Rust 特色** | 零成本抽象；迭代器惰性求值；`sort_unstable` 等 |

---

## 常见坑与解决

| 坑 | 解决 |
| :--- | :--- || 迭代器消费后复用 | 用 `by_ref()` 或 `iter()` 多次；或 `collect` 再 `iter` |
| HashMap key 无 `Hash` | 用 `BTreeMap` 或为 key 实现 `Hash` |
| 排序稳定性 | 稳定用 `sort`；性能用 `sort_unstable` |
| 浮点作 key | 用 `ordered_float` 或整数编码 |

---

## 集合速选

| 场景 | 选型 |
| :--- | :--- || 顺序、索引访问 | `Vec` |
| 键值查找、无序 | `HashMap` |
| 键值有序 | `BTreeMap` |
| 去重、成员检测 | `HashSet`/`BTreeSet` |
| 双端队列 | `VecDeque` |

---

## 学习路径

1. **入门** (1–2 周): Vec/HashMap → 迭代器基础 → 常用算法
2. **进阶** (2–3 周): 排序、搜索、图、动态规划
3. **高级** (持续): 并行算法、与 C05/C06 结合

---

## 速查与练习

- **速查卡**: [algorithms_cheatsheet](../../../docs/02_reference/quick_reference/algorithms_cheatsheet.md) | [collections_iterators_cheatsheet](../../../docs/02_reference/quick_reference/collections_iterators_cheatsheet.md)
- **RBE 练习**: [Vectors](https://doc.rust-lang.org/rust-by-example/std/vec.html) · [HashMap](https://doc.rust-lang.org/rust-by-example/std/hash.html) · [Iterator](https://doc.rust-lang.org/rust-by-example/trait/iter.html)
- **Rustlings**: [05_vecs](https://github.com/rust-lang/rustlings/tree/main/exercises/05_vecs) · [11_hashmaps](https://github.com/rust-lang/rustlings/tree/main/exercises/11_hashmaps) · [18_iterators](https://github.com/rust-lang/rustlings/tree/main/exercises/18_iterators)
