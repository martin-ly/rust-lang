# Brown University CRP Ownership Inventory 练习

> **Source**: Inspired by the Brown University CRP Ownership Inventory.
> **目标**: 通过 8 个聚焦所有权子主题的小练习，帮助学习者建立对 Rust 所有权、借用和生命周期的直觉。
>
> **学习目标 / Learning Goals**:
>
> - 区分移动（move）与 Copy 语义
> - 理解可变借用与不可变借用的互斥规则
> - 识别并避免悬垂引用
> - 为函数和结构体标注生命周期
> - 理解 RAII 与自定义 Drop
> - 修复涉及 Vec 和切片的借用检查器错误
> - 掌握在循环中转移所有权与借用迭代

---

## 练习索引

| 文件 | 主题 / Topic | 核心概念 |
|---|---|---|
| `inventory_01.rs` | 移动语义 vs. Copy 语义 / Move vs. Copy | `String` move, `i32` Copy |
| `inventory_02.rs` | 可变借用规则 / Mutable Borrowing | `&mut T` vs `&T` 互斥 |
| `inventory_03.rs` | 悬垂引用 / Dangling References | 返回 owned `String` 而非局部引用 |
| `inventory_04.rs` | 生命周期标注 / Lifetime Annotations | 结构体与函数生命周期 |
| `inventory_05.rs` | RAII 与 Drop 语义 / RAII and Drop | 自定义 `Drop`、drop 顺序 |
| `inventory_06.rs` | 借用检查器错误修复 / Fixing Borrow Checker Errors | Vec + 可变借用冲突 |
| `inventory_07.rs` | Vec 重新分配与切片失效 / Vec Reallocation | 切片失效、先读后写 |
| `inventory_08.rs` | 循环中的所有权 / Ownership in Loops | 消费迭代 vs 引用迭代 |

---

## 运行测试

```bash
cargo test -p exercises --lib ownership_borrowing::brown_inventories
```
---

## 国际学习者入口

这些练习对应 Brown University 交互版 Rust Book 中的所有权可视化内容：

- [Brown University — The Rust Programming Language](https://rust-book.cs.brown.edu/)
- [Brown University — What’s Different About This Book](https://rust-book.cs.brown.edu/ch00-01-what-to-expect.html)
