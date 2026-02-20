# C01 所有权与借用 - 一页纸总结

> **用途**: 快速回顾核心概念、常见坑、学习路径
> **完整文档**: [00_MASTER_INDEX](./00_MASTER_INDEX.md)

---

## 核心概念（3 条）

| 规则 | 说明 |
| :--- | :--- || **所有权** | 每个值有且仅有一个所有者；赋值/传参发生 Move |
| **借用** | `&T` 不可变借用（可多个）；`&mut T` 可变借用（同一时刻仅一个） |
| **生命周期** | 引用不能 outlive 其指向的数据；编译器通过生命周期标注推断 |

---

## 常见坑与解决

| 坑 | 解决 |
| :--- | :--- || 移动后使用 | 用 `clone()` 或 `&` 借用 |
| 可变与不可变借用冲突 | 缩小不可变借用作用域，或调整使用顺序 |
| 返回悬垂引用 | 返回所有权（`String`）或使用生命周期参数 |
| 循环中借用 | 先收集到 `Vec` 再修改，或使用 `RefCell` |

---

## 智能指针速选

| 场景 | 选型 |
| :--- | :--- || 堆分配、递归类型 | `Box<T>` |
| 单线程多重所有权 | `Rc<T>` |
| 多线程多重所有权 | `Arc<T>` |
| 单线程内部可变 | `RefCell<T>` |
| 多线程内部可变 | `Mutex<T>` / `RwLock<T>` |

---

## 学习路径

1. **入门** (1–2 周): 所有权 → 借用 → 切片 → 生命周期省略
2. **进阶** (2–4 周): 智能指针 → 高级所有权模式
3. **高级** (持续): 零成本抽象、形式化验证

---

## 速查与练习

- **速查卡**: [ownership_cheatsheet](../../../docs/02_reference/quick_reference/ownership_cheatsheet.md)
- **RBE 练习**: [Scope](https://doc.rust-lang.org/rust-by-example/scope.html) · [Move](https://doc.rust-lang.org/rust-by-example/scope/move.html) · [Borrow](https://doc.rust-lang.org/rust-by-example/scope/borrow.html) · [Lifetime](https://doc.rust-lang.org/rust-by-example/scope/lifetime.html)
- **Rustlings**: [06_move_semantics](https://github.com/rust-lang/rustlings/tree/main/exercises/06_move_semantics) · [16_lifetimes](https://github.com/rust-lang/rustlings/tree/main/exercises/16_lifetimes) · [19_smart_pointers](https://github.com/rust-lang/rustlings/tree/main/exercises/19_smart_pointers)
