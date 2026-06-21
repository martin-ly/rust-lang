> **内容分级**: [综述级]

# 所有权清单自测：Brown University Ownership Inventory

> **EN**: Brown University Ownership Inventory
> **Summary**: Brown University Ownership Inventory: core Rust concepts, syntax, and examples.
> **受众**: [初学者]
> **内容分级**: [综述级]
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **定理链**: N/A — 测验性/互动性文档

>
> **来源**: [Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL — Understanding Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)
---

> **来源**:
> [Brown University Interactive Book — Ownership Inventory #1](https://rust-book.cs.brown.edu/ch06-04-inventory.html) ·
> [Ownership Inventory #2](https://rust-book.cs.brown.edu/ch08-04-inventory.html) ·
> [Ownership Inventory #3](https://rust-book.cs.brown.edu/ch10-04-inventory.html) ·
> [Ownership Inventory #4](https://rust-book.cs.brown.edu/ch18-04-inventory.html) ·
> [Crichton et al., OOPSLA 2023](https://doi.org/10.1145/3622841)
>
> **前置概念**:
> [Ownership](./01_ownership.md) ·
> [Borrowing](./02_borrowing.md) ·
> [Lifetimes](./03_lifetimes.md)
>
> **对应练习**:
> [`exercises/src/ownership_borrowing/`](../../exercises/src/ownership_borrowing/) ·
> [`23_quiz_ownership_borrowing.md`](./23_quiz_ownership_borrowing.md)

---

> **Bloom 层级**: 理解 → 应用 → 分析
> **定位**:
> 本文档为 **Brown University Interactive Book** 中「Ownership Inventory」概念清单的本地映射。
> Inventory 题目灵感来自真实 StackOverflow 问题，重点检验所有权、借用、生命周期在**真实代码场景**中的运用。
> **使用方式**: 先阅读对应前置概念，再尝试回答示例题，最后点击展开核对解析；亦可直接访问 Brown Book 的交互式题目获得 IDE 与可视化辅助。

---

## 一、四个 Inventory 节点

| Inventory | 完成时机 | Brown Book 链接 | 本项目对应 |
|:---|:---|:---|:---|
| **Inventory #1** | 学完所有权、借用、枚举后 | [Ch 6.4](https://rust-book.cs.brown.edu/ch06-04-inventory.html) | `01_ownership.md` · `02_borrowing.md` |
| **Inventory #2** | 学完集合类型后 | [Ch 8.4](https://rust-book.cs.brown.edu/ch08-04-inventory.html) | `08_collections.md` |
| **Inventory #3** | 学完泛型、trait、生命周期后 | [Ch 10.4](https://rust-book.cs.brown.edu/ch10-04-inventory.html) | `03_lifetimes.md` |
| **Inventory #4** | 学完智能指针后 | [Ch 18.4](https://rust-book.cs.brown.edu/ch18-04-inventory.html) | 智能指针相关章节 |

> **提示**: Brown Book 提供浏览器内 IDE（基于 rust-analyzer WASM）和 Aquascope 可视化，推荐在 PC 端 Chrome/Firefox 体验。

---

## 二、样题示例（基于 Inventory 方法论）

### 样题 1：字符串替换链

```rust
fn make_exciting(s: &str) -> String {
    let s2 = s.replace(".", "!");
    let s3 = s2.replace("?", "‽");
    s3
}

fn main() {
    let s = String::from("Hello.");
    let out = make_exciting(&s);
    println!("{s}");
    println!("{out}");
}
```

**Q1**: 这段代码能否编译？

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**: ✅ 能编译。

**解析**:

- `make_exciting` 接收 `&str`，不获取 `s` 的所有权，因此调用后 `s` 仍可用。
- `s.replace(...)` 返回新的 `String`，其所有权在函数内部通过 `s2` → `s3` 传递，最终返回给调用者。
- `out` 拥有返回的 `String`，`s` 仍拥有自己的 `String`，两者独立。

</details>

---

### 样题 2：Vec 与切片

```rust,compile_fail
fn main() {
    let mut v = vec![1, 2, 3];
    let s = &v[0..2];
    v.push(4);
    println!("{:?}", s);
}
```

**Q1**: 这段代码能否编译？

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**: ❌ 不能编译。

**错误信息**（类似）: `cannot borrow`v`as mutable because it is also borrowed as immutable`

**解析**:

- `s` 是对 `v` 的不可变借用（`&[i32]`）。
- `v.push(4)` 需要可变借用 `&mut v`。
- Rust 禁止同时存在对同一数据的可变借用和不可变借用，因此编译失败。
- 修复方案：在 `push` 之前停止使用 `s`，或先 `clone` 出独立数据。

</details>

---

### 样题 3：函数返回值的生命周期

```rust,compile_fail
fn first_word(s: &str) -> &str {
    &s[0..1]
}

fn main() {
    let result;
    {
        let s = String::from("hello");
        result = first_word(&s);
    }
    println!("{result}");
}
```

**Q1**: 这段代码能否编译？

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**: ❌ 不能编译。

**错误信息**（类似）: `result` does not live long enough / `s` does not live long enough

**解析**:

- `first_word(&s)` 返回的 `&str` 生命周期不能超过 `s`。
- `s` 在内部块结束时被释放，但 `result` 仍指向它。
- 修复方案：将 `result` 的创建和使用限制在 `s` 的有效作用域内，或返回 `String` 而非引用。

</details>

---

## 三、学习建议

1. **先做题，后看解析**：Inventory 的价值在于暴露真实误解，不要直接展开答案。
2. **对照 Brown Book 交互版**：对于卡住的题目，访问 Brown Book 链接，使用 IDE 悬停类型、Aquascope 查看权限变化。
3. **动手改代码**：将示例代码复制到本地，尝试修改并观察编译器错误，形成肌肉记忆。
4. **定期复习**：所有权是 Rust 的核心心智模型，建议在每个 Inventory 节点做一遍自测。

---

## 四、与本地练习的衔接

- 完成本样题后，可继续：
  - [`23_quiz_ownership_borrowing.md`](./23_quiz_ownership_borrowing.md) — 更多所有权/借用选择题
  - [`exercises/src/ownership_borrowing/`](../../exercises/src/ownership_borrowing/) — 可编译的修复练习
    - [`ex06_string_replace_chain.rs`](../../exercises/src/ownership_borrowing/ex06_string_replace_chain.rs) — 字符串替换链（对应 Inventory #1）
    - [`ex07_vec_slice_borrow.rs`](../../exercises/src/ownership_borrowing/ex07_vec_slice_borrow.rs) — Vec 与切片借用冲突（对应 Inventory #2）
    - [`ex08_dangling_reference.rs`](../../exercises/src/ownership_borrowing/ex08_dangling_reference.rs) — 避免悬垂引用（对应 Inventory #3）
    - [`ex09_dangling_stack_reference.rs`](../../exercises/src/ownership_borrowing/ex09_dangling_stack_reference.rs) — 悬垂栈引用
    - [`ex10_vec_reallocation.rs`](../../exercises/src/ownership_borrowing/ex10_vec_reallocation.rs) — Vec 重新分配与引用失效
    - [`ex11_hashmap_borrow.rs`](../../exercises/src/ownership_borrowing/ex11_hashmap_borrow.rs) — HashMap 借用冲突
    - [`ex12_string_in_loop.rs`](../../exercises/src/ownership_borrowing/ex12_string_in_loop.rs) — 循环中的所有权
  - [`02_borrowing.md`](./02_borrowing.md) — 系统学习「Fixing Ownership Errors」的 5 种常见模式
