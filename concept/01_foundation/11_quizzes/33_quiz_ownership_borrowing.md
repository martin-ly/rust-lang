> **内容分级**: [综述级]

# 测验：所有权、借用与生命周期（试点）
>
> **EN**: Ownership
> **Summary**: Quiz Ownership Borrowing. Core Rust concept.
> ```rust fn main() { let s1 = String::from("hello"); let s2 = s1; println!("{s1}"); }```
> <details> <summary>💡 点击展开答案与解析</summary> **答案**：❌ 不能编译。
> **错误信息**：`borrow of moved value: s1` **解析**：`String` 未实现 `Copy` trait，赋值 `let s2 = s1` 会**移动（move）**ownership。`s1` 在移动后变为未初始化状态，不能再使用。
> **知识点**：Rust 中每个值有且只有一个所有者
> **受众**: [初学者]
> **内容分级**: [综述级]
> **Rust 版本**: 1.96.1+ (Edition 2024)
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链
> **后置概念**: [Borrowing](../01_ownership_borrow_lifetime/02_borrowing.md)
---

> **来源**:
>
> · [自测题库](../../00_meta/04_navigation/self_assessment.md)
> · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/)
> · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003)
> · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/)
> · [Brown Interactive Rust Book](https://rust-book.cs.brown.edu/)
> · [Rust Reference — Functions and Borrowing](https://doc.rust-lang.org/reference/items/functions.html)
> · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
>
> [The Rust Programming Language — Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) ·
> [The Rust Programming Language — References and Borrowing](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html) ·
> [The Rust Programming Language — Lifetimes](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html)
>
> **前置概念**:
>
> [Ownership](../01_ownership_borrow_lifetime/01_ownership.md) ·
> [Borrowing](../01_ownership_borrow_lifetime/02_borrowing.md) ·
> [Lifetimes](../01_ownership_borrow_lifetime/03_lifetimes.md)
>
> **对应练习**:
>
> [`exercises/src/ownership_borrowing/`](../../exercises/src/ownership_borrowing) ·
> [`exercises/rustlings_style/ex01_borrow_fix`](../../exercises/rustlings_style/ex01_borrow_fix)

---

> **Bloom 层级**: 理解 → 应用
> **定位**:
> 本文件为**嵌入式互动测验试点**，采用 `<details>` 交互标签实现"自测-展开-核对"的轻量级学习闭环。
> 每道题均锚定于对应的 L1 核心概念文件，并链接至可编译练习代码。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

---

## 认知路径

> **认知路径**: 本节从 "测验" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 测验 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 测验 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与测验的适用边界。
5. **迁移应用**: 将 测验 与前置/后置概念链接，形成跨层知识网络。

---

> **过渡**: 从 测验 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 测验 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 测验 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: 测验 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 测验 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 测验 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

---

## 反命题决策树

> **反命题 1**: "测验 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 测验 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 测验 规则被违反的直接信号。

> **反命题 3**: "其他语言对 测验 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 测验 具有语言特有的形态。

---

> **反向推理 1**: 如果程序在 测验 相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。
>
> **反向推理 2**: 如果某段代码在运行时（Runtime）表现出非预期行为且与 测验 有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。

## 一、所有权规则

### Q1. 以下代码能否编译？若不能，原因是什么？

```rust,compile_fail
fn main() {
    let s1 = String::from("hello");
    let s2 = s1;
    println!("{s1}");
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`borrow of moved value: s1`

**解析**：`String` 未实现 `Copy` trait，赋值 `let s2 = s1` 会**移动（move）**所有权（Ownership）。`s1` 在移动后变为未初始化状态，不能再使用。

**知识点**：Rust 中每个值有且只有一个所有者。当所有者离开作用域，值被自动丢弃（drop）。→ 所有权（Ownership）规则详解

</details>

---

### Q2. 以下代码能否编译？若不能，如何修改？

```rust,compile_fail
fn main() {
    let s = String::from("hello");
    take_ownership(s);
    println!("{s}");
}

fn take_ownership(s: String) {
    println!("{s}");
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`borrow of moved value: s`

**解析**：`take_ownership(s)` 将 `s` 的所有权（Ownership）移动到函数参数中。函数结束后 `s` 被 drop，`main` 中的 `s` 不再有效。

**修改方案**（二选一）：

1. **使用引用（Reference）**（推荐，零成本）：

```rust
fn take_ownership(s: &String) {
    println!("{s}");
}
```

1. **显式克隆**（有堆分配成本）：

```rust,ignore
let s = String::from("hello");
take_ownership(s.clone());
println!("{s}");
```

**知识点**：通过引用（Reference）借用（Borrowing）可以避免所有权（Ownership）转移。→ 借用详解

</details>

---

### Q3. 为什么 `i32` 可以复制而 `String` 不能？

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：`i32` 实现了 `Copy` trait，`String` 没有。

**解析**：

| 类型 | 存储位置 | 是否 `Copy` | 赋值行为 |
|:---|:---|:---:|:---|
| `i32` | 栈 | ✅ | 位复制（bitwise copy） |
| `String` | 栈（元数据）+ 堆（字符数据） | ❌ | 移动（move） |

`String` 包含堆内存的指针，若按位复制会导致**双重释放（double free）**。Rust 禁止为管理堆内存的类型自动实现 `Copy`。

**知识点**：`Copy` trait 标记"按位复制安全"的类型。自定义类型可通过 `#[derive(Copy, Clone)]` 显式实现（前提是所有字段都实现 `Copy`）。→ 类型系统（Type System）详解

</details>

---

## 二、借用规则

### Q4. 以下代码能否编译？若不能，原因是什么？

```rust,compile_fail
fn main() {
    let mut s = String::from("hello");
    let r1 = &mut s;
    let r2 = &mut s;
    println!("{r1} {r2}");
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`cannot borrow`s`as mutable more than once at a time`

**解析**：Rust 的**可变借用（Mutable Borrow）规则**规定：在同一作用域内，对同一数据只能有一个可变引用（Mutable Reference）（&mut）。这是数据竞争自由（data-race freedom）的编译期保证。

**修改方案**——通过**限制作用域**或**顺序使用**分离借用（Borrowing）：

```rust
fn main() {
    let mut s = String::from("hello");
    {
        let r1 = &mut s;
        println!("{r1}");
    } // r1 在此处失效
    let r2 = &mut s;
    println!("{r2}");
}
```

**知识点**：Rust 借用（Borrowing）检查器通过作用域分析（而非运行时（Runtime）锁）保证内存安全（Memory Safety）。[→ 借用规则详解](../01_ownership_borrow_lifetime/02_borrowing.md)

</details>

---

### Q5. 以下代码能否编译？

```rust,compile_fail
fn main() {
    let s = String::from("hello");
    let r1 = &s;
    let r2 = &s;
    let r3 = &mut s;
    println!("{r1} {r2} {r3}");
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`cannot borrow`s`as mutable because it is also borrowed as immutable`

**解析**：Rust 的**借用（Borrowing）规则二**规定：不可变引用（Immutable Reference）（&T）和可变引用（&mut T）不能同时存在。因为不可变引用的使用者可能依赖数据不被修改。

**修改方案**——确保不可变引用（Immutable Reference）不再使用后再创建可变引用：

```rust
fn main() {
    let mut s = String::from("hello");
    let r1 = &s;
    let r2 = &s;
    println!("{r1} {r2}"); // 最后使用 r1, r2
    let r3 = &mut s;       // 现在可以创建 &mut
    println!("{r3}");
}
```

**知识点**：Rust 使用**非词法生命周期（NLL）**分析引用（Reference）的实际使用位置，而非仅依赖词法作用域。[→ NLL 与 Polonius](../../03_advanced/02_unsafe/08_nll_and_polonius.md)

</details>

---

### Q6. 悬垂引用（Dangling Reference）在 Rust 中是否可能？以下代码能否编译？

```rust,compile_fail
fn dangle() -> &String {
    let s = String::from("hello");
    &s
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`missing lifetime specifier`（在函数签名处）

**解析**：`s` 在函数结束时被 drop，返回的引用（Reference）将指向已释放的内存。Rust 的借用（Borrowing）检查器**在编译期阻止所有悬垂引用**。

**正确写法**——转移所有权（Ownership）：

```rust
fn no_dangle() -> String {
    let s = String::from("hello");
    s // 移动所有权，而非返回引用
}
```

**知识点**：Rust 通过**生命周期（lifetime）**系统跟踪引用（Reference）的有效范围，确保引用永不超出被引用数据的生命周期。[→ 生命周期详解](../01_ownership_borrow_lifetime/03_lifetimes.md)

</details>

---

## 三、生命周期基础

### Q7. 以下代码中，`result` 的生命周期由谁决定？

```rust,compile_fail
fn longest(x: &str, y: &str) -> &str {
    if x.len() > y.len() { x } else { y }
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译——需要显式生命周期（Lifetimes）标注。

**错误信息**：`missing lifetime specifier`

**解析**：编译器无法确定返回的引用（Reference）是 `x` 的还是 `y` 的。需要显式标注生命周期（Lifetimes）：

```rust
fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

**语义**：返回的引用（Reference）生命周期（Lifetimes）至少与 `x` 和 `y` 中**较短的那个**一样长。

**知识点**：生命周期（Lifetimes）标注不改变运行时（Runtime）代码，仅向编译器提供**借用（Borrowing）关系约束**。→ 生命周期语法

</details>

---

### Q8. 以下代码能否编译？

```rust,compile_fail
fn main() {
    let string1 = String::from("long string is long");
    let result;
    {
        let string2 = String::from("xyz");
        result = longest(&string1, &string2);
    }
    println!("The longest string is {result}");
}

fn longest<'a>(x: &'a str, y: &'a str) -> &'a str {
    if x.len() > y.len() { x } else { y }
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`result` does not live long enough

**解析**：`result` 的生命周期（Lifetimes）被标注为 `'a`，而 `'a` 是 `x` 和 `y` 的交集。`string2` 在内部作用域结束即被 drop，因此 `result` 不能在外部作用域使用。

**修正方案**：将 `println!` 移入内部作用域：

```rust,ignore
fn main() {
    let string1 = String::from("long string is long");
    {
        let string2 = String::from("xyz");
        let result = longest(&string1, &string2);
        println!("The longest string is {result}");
    }
}
```

**知识点**：生命周期（Lifetimes）约束遵循"**最小公约数**"原则——返回引用（Reference）的有效期不超过任何输入引用的有效期。[→ 生命周期详解](../01_ownership_borrow_lifetime/03_lifetimes.md)

</details>

---

## 四、综合应用

### Q9. 以下代码的输出是什么？

```rust,compile_fail
fn main() {
    let mut v = vec![1, 2, 3];
    let first = &v[0];
    v.push(4);
    println!("{first}");
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：❌ 不能编译。

**错误信息**：`cannot borrow`v`as mutable because it is also borrowed as immutable`

**解析**：`&v[0]` 创建了对 `v` 内部元素的不可变引用（Immutable Reference）。`v.push(4)` 需要 `&mut v`。如果 `push` 导致 `Vec` 重新分配内存，`first` 将变成悬垂指针。

**修改方案**——分离借用（Borrowing）：

```rust
fn main() {
    let mut v = vec![1, 2, 3];
    let first = v[0]; // 复制值（i32 实现 Copy）
    v.push(4);
    println!("{first}");
}
```

**知识点**：`Vec::push` 可能触发重新分配，因此 Rust 禁止在存在元素引用时修改 `Vec`。[→ 集合类型详解](../05_collections/08_collections.md)

</details>

---

### Q10. 以下代码能否编译？解释 `Rc` 的作用

```rust
use std::rc::Rc;

fn main() {
    let data = Rc::new(String::from("shared"));
    let data2 = Rc::clone(&data);
    println!("{} {}", data, data2);
    println!("{}", Rc::strong_count(&data));
}
```

<details>
<summary>💡 点击展开答案与解析</summary>

**答案**：✅ 能编译。

**输出**：

```
shared shared
2
```

**解析**：

- `Rc<T>`（Reference Counted）提供**单线程共享所有权（Ownership）**
- `Rc::clone(&data)` 不克隆底层数据，仅增加引用计数
- 当最后一个 `Rc` 离开作用域时，引用计数归零，数据被 drop

**限制**：`Rc` 不提供内部可变性。如需修改共享数据，需配合 `RefCell<T>` 或 `Mutex<T>`。

**知识点**：`Rc` 是 Rust 所有权（Ownership）系统的**补充**而非替代——它通过运行时（Runtime）引用计数允许有限的共享所有权，代价是只能用于单线程场景。→ 智能指针（Smart Pointer）详解

</details>

---

## 五、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 10/10 | 🏆 所有权（Ownership）系统已内化 | 直接进阶至 [L2 智能指针（Smart Pointer）](../../02_intermediate/02_memory_management/03_memory_management.md) |
| 7–9/10 | ✅ 核心概念掌握 | 强化 [L1 练习](../../exercises/src/ownership_borrowing)，关注错题对应的概念文件 |
| 4–6/10 | 🔄 需巩固基础 | 重读 [Ownership](../01_ownership_borrow_lifetime/01_ownership.md) · [Borrowing](../01_ownership_borrow_lifetime/02_borrowing.md) · [Lifetimes](../01_ownership_borrow_lifetime/03_lifetimes.md)，完成 rustlings 对应章节 |
| 0–3/10 | 📚 建议重新开始 | 从 [Ownership](../01_ownership_borrow_lifetime/01_ownership.md) 逐节阅读，配合 [crates/c01_ownership_borrow_scope](../../crates/c01_ownership_borrow_scope) 可编译示例 |

---

## 六、试点说明

> **文件性质**：本文件为 **L1 概念层嵌入式互动测验试点**，验证 `"概念文件 + 嵌入式自测 + 可编译练习"` 的三层学习闭环可行性。
>
> **技术实现**：采用标准 Markdown `<details>` 标签，无需额外构建步骤，在所有 Markdown 渲染器（GitHub、VS Code、mdBook）中均可交互。
>
> **扩展计划**：若试点效果良好，可向以下主题推广：
>
> - L1: 类型系统（Type System）、集合、错误处理（Error Handling）
> - L2: Trait、泛型（Generics）、智能指针（Smart Pointer）
> - L3: 并发、异步（Async）、Unsafe
>
> **反馈收集**：请在使用后通过本文件所在目录的 GitHub Issue 反馈体验（题目难度、解析清晰度、交互流畅度）。

---

> **对应 Crate**: [`c01_ownership_borrow_scope`](../../crates/c01_ownership_borrow_scope)
> **对应练习**: [`exercises/src/ownership_borrowing/`](../../exercises/src/ownership_borrowing) · [`exercises/rustlings_style/ex01_borrow_fix`](../../exercises/rustlings_style/ex01_borrow_fix)

---

> **权威来源**:
> [The Rust Programming Language — Ch4 Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html) ·
> [The Rust Programming Language — Ch10 Lifetimes](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html) ·
> [Rust Reference — Ownership](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html)

## 嵌入式测验（Embedded Quiz）

### 测验 1：本文件是 测验：所有权、借用与生命周期（试点） 的专项测验集。这类测验文件的主要作用是什么？（理解层）

**题目**: 本文件是 测验：所有权（Ownership）、借用（Borrowing）与生命周期（Lifetimes）（试点） 的专项测验集。这类测验文件的主要作用是什么？

<details>
<summary>✅ 答案与解析</summary>

集中提供大量针对特定主题的练习题，帮助学习者系统检验和巩固对该主题的掌握程度，补充概念文件中的嵌入式测验。
</details>

---

### 测验 2：在 测验：所有权、借用与生命周期（试点） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？（理解层）

**题目**: 在 测验：所有权（Ownership）、借用与生命周期（Lifetimes）（试点） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？

<details>
<summary>✅ 答案与解析</summary>

先尝试独立作答，然后对照答案解析理解错误原因，最后回到对应的概念文件重新阅读相关章节，形成"测验-反馈-复习"的闭环。
</details>

---

### 测验 3：专项测验与概念文件末尾的嵌入式测验有什么区别？（理解层）

**题目**: 专项测验与概念文件末尾的嵌入式测验有什么区别？

<details>
<summary>✅ 答案与解析</summary>

专项测验题量更大、覆盖更全面，通常按难度分层；嵌入式测验更精简，直接关联刚阅读的概念内容，用于即时检验理解。
</details>
