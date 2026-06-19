# Brown University「Ownership Inventory」映射与整合方案

> **报告日期**: 2026-06-19
> **来源**: [Brown University Interactive Book](https://rust-book.cs.brown.edu/) · Crichton et al., OOPSLA 2023 · Crichton & Krishnamurthi, OOPSLA 2024
> **目标**: 将 Brown Book 的所有权评估工具映射到本项目的学习路径，并设计可复现的嵌入式测验

---

## 1. 什么是 Ownership Inventory

Ownership Inventory 是 Brown University Cognitive Engineering Lab 在交互式 Rust Book 中设计的一系列**概念清单（concept inventory）**测验。其设计目标：

- 检验学习者对所有权在真实代码场景中如何运作的理解
- 题目灵感来自 StackOverflow 上的常见 Rust 问题
- 采用「程序 → 预测输出 / 判断合法性 / 解释原因」的三段式提问

根据 OOPSLA 2023 论文，Inventory 包含 **8 个核心程序**，每个程序对应 3 道问题（Q1 判断、Q2a 选择、Q3a 解释），共 24 题。题目类型包括：

- **判断题**：程序能否编译？输出什么？
- **多选题**：选择正确/错误选项（干扰项来自常见误解）
- **解释题**：用一句话说明原因

---

## 2. Brown Book 中的四个 Inventory 节点

| Inventory | Brown Book 位置 | 前置章节 | 本项目对应 |
|:---|:---|:---|:---|
| **Ownership Inventory #1** | [Ch 6.4](https://rust-book.cs.brown.edu/ch06-04-inventory.html) | Ownership、Borrowing、Enums | `concept/01_foundation/01_ownership.md` · `02_borrowing.md` |
| **Ownership Inventory #2** | [Ch 8.4](https://rust-book.cs.brown.edu/ch08-04-inventory.html) | Common Collections | `concept/01_foundation/08_collections.md` · `17_collections_advanced.md` |
| **Ownership Inventory #3** | [Ch 10.4](https://rust-book.cs.brown.edu/ch10-04-inventory.html) | Generics、Traits、Lifetimes | `concept/01_foundation/03_lifetimes.md` · `03_lifetimes_advanced.md` |
| **Ownership Inventory #4** | [Ch 18.4](https://rust-book.cs.brown.edu/ch18-04-inventory.html) | Smart Pointers | `concept/03_advanced/03_unsafe.md` · `02_intermediate/??` |

> 注：Brown Book 的 Inventory #4 位于 Smart Pointers 之后，本项目智能指针相关内容主要在 `concept/03_advanced/` 与 `concept/02_intermediate/`。

---

## 3. 学术基础

### 3.1 OOPSLA 2023: A Grounded Conceptual Model for Ownership Types in Rust

- **作者**: Will Crichton, Gavin Gray, Shriram Krishnamurthi
- **核心贡献**: 提出基于「权限（permissions）」的所有权概念模型
  - 读权限（R）、写权限（W）、拥有权限（O）
  - 路径（path）在不同程序点的权限变化
- **教学效果**: 使用新模型的学习者在所有权测验中表现优于仅读原版 TRPL 的学习者
- **DOI**: [10.1145/3622841](https://doi.org/10.1145/3622841)

### 3.2 OOPSLA 2024: Profiling Programming Language Learning

- **作者**: Will Crichton, Shriram Krishnamurthi
- **核心贡献**: 通过在线教科书收集学习数据，分析常见误解
- **荣誉**: Distinguished Paper

---

## 4. 整合到本项目的路径

### 4.1 已有基础

- `concept/01_foundation/23_quiz_ownership_borrowing.md`：本地所有权/借用测验（试点）
- `concept/01_foundation/02_borrowing.md`：已整合 Brown Book「Fixing Ownership Errors」
- `LEARNING_MVP_PATH.md`：已将 Brown Book 标注为 Day 3-4 / Day 10-11 外部参考

### 4.2 已实施

1. ✅ **`concept/01_foundation/28_ownership_inventories_brown_book.md`**
   - 说明 Ownership Inventory 的设计思想
   - 列出 4 个 Inventory 的链接与本项目对应章节
   - 提供 3 道示例题（基于真实 StackOverflow 场景）

2. ✅ **在相关章节底部添加「自测入口」**
   - `01_ownership.md` → Inventory #1
   - `02_borrowing.md` → Inventory #1
   - `08_collections.md` → Inventory #2
   - `03_lifetimes.md` → Inventory #3
   - 智能指针章节 → Inventory #4（待有独立文档后补充）

3. ✅ **练习代码映射**
   - 新增 `exercises/src/ownership_borrowing/ex06_string_replace_chain.rs`（Inventory #1）
   - 新增 `exercises/src/ownership_borrowing/ex07_vec_slice_borrow.rs`（Inventory #2）
   - 新增 `exercises/src/ownership_borrowing/ex08_dangling_reference.rs`（Inventory #3）
   - 新增 `exercises/src/ownership_borrowing/ex09_dangling_stack_reference.rs`
   - 新增 `exercises/src/ownership_borrowing/ex10_vec_reallocation.rs`
   - 新增 `exercises/src/ownership_borrowing/ex11_hashmap_borrow.rs`
   - 新增 `exercises/src/ownership_borrowing/ex12_string_in_loop.rs`
   - 更新 `exercises/src/ownership_borrowing/mod.rs` 导出上述模块

### 4.3 与 Aquascope 的联动

- Brown Book 的 Inventory 题目常配合 Aquascope 可视化使用
- 在 `concept/01_foundation/28_ownership_inventories_brown_book.md` 中可链接到 Brown Book 的交互式题目，作为「可视化辅助自测」

---

## 5. 样例题目设计（基于 Inventory 方法论）

以下题目遵循 Brown Book Inventory 的三段式：

### 样例 1：字符串替换链（对应 make_exciting）

```rust
fn make_exciting(s: &str) -> String {
    let s2 = s.replace(".", "!");
    let s3 = s2.replace("?", "‽");
    s3
}
```

- **Q1**: `make_exciting` 接收 `&str` 是否安全？返回值的所有权归谁？
- **Q2**: 若调用者写下 `let s = String::from("hi"); let out = make_exciting(&s);`，`s` 在调用后是否仍可用？
- **Q3**: 解释为什么 `s.replace(...)` 返回 `String` 而不是 `&str`。

### 样例 2：Vec 与切片（对应 Inventory #2）

```rust
fn main() {
    let v = vec![1, 2, 3];
    let s = &v[0..2];
    println!("{}", s[0]);
}
```

- **Q1**: 此代码能否编译？
- **Q2**: 若在第 4 行后添加 `v.push(4);`，能否编译？
- **Q3**: 用生命周期规则解释原因。

> 完整示例题见 `concept/01_foundation/28_ownership_inventories_brown_book.md`。

---

## 6. 决策建议

- **短期**：创建 `28_ownership_inventories_brown_book.md`，在 4 个核心章节底部添加 Inventory 链接
- **中期**：将 8 个核心程序整理为 `exercises/src/ownership_borrowing/` 的独立练习
- **长期**：若 Aquascope POC 成功，可将 Inventory 题目与 Aquascope 可视化绑定，实现「看图表 → 答题 → 核对」闭环
