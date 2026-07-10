> **内容分级**: [综述级]

# 所有权清单自测：Brown University Ownership Inventory

> **EN**: Brown University Ownership Inventory
> **Summary**: Brown University Ownership Inventory: core Rust concepts, syntax, and examples.
> **受众**: [初学者]
> **内容分级**: [综述级]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` 权威页。
> **定理链**: N/A — 测验性/互动性文档
>
> **来源**: [Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL — Understanding Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) · [学习指南](../../00_meta/04_navigation/learning_guide.md) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> **后置概念**: N/A
---

> **来源**:
>
> [Brown University Interactive Book — Ownership Inventory #1](https://rust-book.cs.brown.edu/ch06-04-inventory.html) ·
> [Ownership Inventory #2](https://rust-book.cs.brown.edu/ch08-04-inventory.html) ·
> [Ownership Inventory #3](https://rust-book.cs.brown.edu/ch10-04-inventory.html) ·
> [Ownership Inventory #4](https://rust-book.cs.brown.edu/ch18-04-inventory.html) ·
> [Crichton et al., OOPSLA 2023](https://doi.org/10.1145/3622841)
>
> **前置概念**:
> [Ownership](01_ownership.md) ·
> [Borrowing](02_borrowing.md) ·
> [Lifetimes](03_lifetimes.md)
>
> **对应练习**:
> [`exercises/src/ownership_borrowing/`](../../exercises/src/ownership_borrowing) ·
> [`23_quiz_ownership_borrowing.md`](../11_quizzes/33_quiz_ownership_borrowing.md)

---

> **Bloom 层级**: L2-L4
> **定位**:
> 本文档为 **Brown University Interactive Book** 中「Ownership Inventory」概念清单的本地映射。
> Inventory 题目灵感来自真实 StackOverflow 问题，重点检验所有权（Ownership）、借用（Borrowing）、生命周期（Lifetimes）在**真实代码场景**中的运用。
> **使用方式**: 先阅读对应前置概念，再尝试回答示例题，最后点击展开核对解析；亦可直接访问 Brown Book 的交互式题目获得 IDE 与可视化辅助。

---

---

---

> **过渡**: 从 所有权（Ownership）清单自测 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 所有权（Ownership）清单自测 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 所有权（Ownership）清单自测 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **反向推理 1**: 如果程序在 所有权清单自测 相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。
>
> **反向推理 2**: 如果某段代码在运行时（Runtime）表现出非预期行为且与 所有权（Ownership）清单自测 有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。
> **权威来源**: [Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/) · [TRPL — Understanding Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html)
>
> **权威来源对齐变更日志**: 2026-07-10 补充权威来源标注（Brown Book、TRPL、Rust Reference）

## 认知路径

> **认知路径**: 本节从 "所有权（Ownership）清单自测" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 所有权（Ownership）清单自测 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 所有权清单自测 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与所有权清单自测的适用边界。
5. **迁移应用**: 将 所有权清单自测 与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "所有权清单自测 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 所有权清单自测 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 所有权清单自测 规则被违反的直接信号。

> **反命题 3**: "其他语言对 所有权清单自测 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 所有权清单自测 具有语言特有的形态。

## 一、四个 Inventory 节点

> (Source: [Brown University Interactive Rust Book](https://rust-book.cs.brown.edu/))

| Inventory | 完成时机 | Brown Book 链接 | 本项目对应 |
|:---|:---|:---|:---|
| **Inventory #1** | 学完所有权（Ownership）、借用（Borrowing）、枚举（Enum）后 | Ch 6.4 | `01_ownership.md` · `02_borrowing.md` |
| **Inventory #2** | 学完集合类型后 | [Ch 8.4](https://rust-book.cs.brown.edu/ch08-04-inventory.html) | `08_collections.md` |
| **Inventory #3** | 学完泛型（Generics）、trait、生命周期（Lifetimes）后 | Ch 10.4 | `03_lifetimes.md` |
| **Inventory #4** | 学完智能指针（Smart Pointer）后 | [Ch 18.4](https://rust-book.cs.brown.edu/ch18-04-inventory.html) | 智能指针相关章节 |

> **提示**: Brown Book 提供浏览器内 IDE（基于 rust-analyzer WASM）和 Aquascope 可视化，推荐在 PC 端 Chrome/Firefox 体验。

---

## 二、样题示例
>
> (Source: [TRPL — Understanding Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html))
（基于 Inventory 方法论）

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

- `make_exciting` 接收 `&str`，不获取 `s` 的所有权（Ownership），因此调用后 `s` 仍可用。
- `s.replace(...)` 返回新的 `String`，其所有权（Ownership）在函数内部通过 `s2` → `s3` 传递，最终返回给调用者。
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

- `s` 是对 `v` 的不可变借用（Immutable Borrow）（`&[i32]`）。
- `v.push(4)` 需要可变借用（Mutable Borrow） `&mut v`。
- Rust 禁止同时存在对同一数据的可变借用和不可变借用（Immutable Borrow），因此编译失败。
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

- `first_word(&s)` 返回的 `&str` 生命周期（Lifetimes）不能超过 `s`。
- `s` 在内部块结束时被释放，但 `result` 仍指向它。
- 修复方案：将 `result` 的创建和使用限制在 `s` 的有效作用域内，或返回 `String` 而非引用（Reference）。

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
  - `23_quiz_ownership_borrowing.md` — 更多所有权/借用（Borrowing）选择题
  - [`exercises/src/ownership_borrowing/`](../../exercises/src/ownership_borrowing) — 可编译的修复练习
    - [`ex06_string_replace_chain.rs`](../../exercises/src/ownership_borrowing/ex06_string_replace_chain.rs) — 字符串替换链（对应 Inventory #1）
    - [`ex07_vec_slice_borrow.rs`](../../exercises/src/ownership_borrowing/ex07_vec_slice_borrow.rs) — Vec 与切片（Slice）借用（Borrowing）冲突（对应 Inventory #2）
    - `ex08_dangling_reference.rs` — 避免悬垂引用（Reference）（对应 Inventory #3）
    - [`ex09_dangling_stack_reference.rs`](../../exercises/src/ownership_borrowing/ex09_dangling_stack_reference.rs) — 悬垂栈引用（Reference）
    - [`ex10_vec_reallocation.rs`](../../exercises/src/ownership_borrowing/ex10_vec_reallocation.rs) — Vec 重新分配与引用（Reference）失效
    - [`ex11_hashmap_borrow.rs`](../../exercises/src/ownership_borrowing/ex11_hashmap_borrow.rs) — HashMap 借用（Borrowing）冲突
    - [`ex12_string_in_loop.rs`](../../exercises/src/ownership_borrowing/ex12_string_in_loop.rs) — 循环中的所有权
  - [`02_borrowing.md`](02_borrowing.md) — 系统学习「Fixing Ownership Errors」的 5 种常见模式
