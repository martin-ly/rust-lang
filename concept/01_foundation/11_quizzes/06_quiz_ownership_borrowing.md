> **内容分级**: [综述级]

# 测验：所有权、借用与生命周期（试点）
>
> **EN**: Ownership
> **Summary**: Ownership — An interactive quiz checking ownership, borrowing, and lifetime fundamentals.
>
> ```rust,compile_fail
> fn main() { let s1 = String::from("hello"); let s2 = s1; println!("{s1}"); }
> ```
>
> <details> <summary>💡 点击展开答案与解析</summary> **答案**：❌ 不能编译。
> **错误信息**：`borrow of moved value: s1` **解析**：`String` 未实现 `Copy` trait，赋值 `let s2 = s1` 会**移动（move）**ownership。`s1` 在移动后变为未初始化状态，不能再使用。
> **知识点**：Rust 中每个值有且只有一个所有者
> **受众**: [初学者]
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **权威来源**: 本文件为 `concept/` 权威页。
> **定理链**: N/A — 测验性/互动性文档，不涉及形式化定理链
> **后置概念**: [Borrowing](../01_ownership_borrow_lifetime/02_borrowing.md)
---

> **来源**:
>
> · [自测题库](../../00_meta/04_navigation/12_self_assessment.md)
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

> **Bloom 层级**: L2-L3
> **难度图例**: 🟢 基础（概念直接考察）｜ 🟡 进阶（需理解深层原理）｜ 🔴 专家（多概念综合 / 边界情况）
> **题型构成**: 代码阅读题（能否编译 / 输出分析，本测验特色）+ 规范题型【单选】【多选】【判断】（按 mdbook-quiz 指南四级题型规范（`docs/02_learning/07_mdbook_quiz_guide.md`） 的 .md 落地形态组织，不引入 TOML 插件）
> **定位**:
> 本文件为**嵌入式互动测验试点**，采用 `<details>` 交互标签实现"自测-展开-核对"的轻量级学习闭环。
> 每道题均锚定于对应的 L1 核心概念文件，并链接至可编译练习代码。
> **使用方式**: 先独立思考答案，再点击展开核对解析。

---

## 一、所有权规则

理解「所有权（Ownership）规则」需要把握 Q1. 以下代码能否编译？若不能，原因是什么？、Q2. 以下代码能否编译？若不能，如何修改？与Q3. 为什么 `i32` 可以复制而 `String` 不能？，本节依次展开。

### Q1. 🟢 以下代码能否编译？若不能，原因是什么？

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

### Q2. 🟡 以下代码能否编译？若不能，如何修改？

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

### Q3. 🟢 为什么 `i32` 可以复制而 `String` 不能？

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

「借用（Borrowing）规则」涉及 Q4. 以下代码能否编译？若不能，原因是什么？、Q5. 以下代码能否编译？与Q6. 悬垂引用（Dangling Reference）在 Rust…，本节逐一说明其要点。

### Q4. 🟡 以下代码能否编译？若不能，原因是什么？

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

### Q5. 🟡 以下代码能否编译？

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

**知识点**：Rust 使用**非词法生命周期（NLL）**分析引用（Reference）的实际使用位置，而非仅依赖词法作用域。[→ NLL 与 Polonius](../../03_advanced/02_unsafe/03_nll_and_polonius.md)

</details>

---

### Q6. 🟡 悬垂引用（Dangling Reference）在 Rust 中是否可能？以下代码能否编译？

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

本节围绕「生命周期（Lifetimes）基础」展开，覆盖 Q7. 以下代码中，`result` 的生命周期由谁决定？ 与  Q8. 以下代码能否编译？ 两个方面。

### Q7. 🟡 以下代码中，`result` 的生命周期由谁决定？

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

### Q8. 🔴 以下代码能否编译？

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

本节围绕「综合应用」展开，覆盖 Q9. 以下代码的输出是什么？ 与  Q10. 以下代码能否编译？解释 `Rc` 的作用 两个方面。

### Q9. 🟡 以下代码的输出是什么？

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

**知识点**：`Vec::push` 可能触发重新分配，因此 Rust 禁止在存在元素引用（Reference）时修改 `Vec`。[→ 集合类型详解](../05_collections/01_collections.md)

</details>

---

### Q10. 🟡 以下代码能否编译？解释 `Rc` 的作用

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
- `Rc::clone(&data)` 不克隆底层数据，仅增加引用（Reference）计数
- 当最后一个 `Rc` 离开作用域时，引用（Reference）计数归零，数据被 drop

**限制**：`Rc` 不提供内部可变性。如需修改共享数据，需配合 `RefCell<T>` 或 `Mutex<T>`。

**知识点**：`Rc` 是 Rust 所有权（Ownership）系统的**补充**而非替代——它通过运行时（Runtime）引用（Reference）计数允许有限的共享所有权，代价是只能用于单线程场景。→ 智能指针（Smart Pointer）详解

</details>

---

## 五、规范题型补充：单选 · 多选 · 判断

> 本节按四级题型规范补充单选、多选与判断题，知识点与
> [Ownership](../01_ownership_borrow_lifetime/01_ownership.md)、
> [Borrowing](../01_ownership_borrow_lifetime/02_borrowing.md)、
> [Lifetimes](../01_ownership_borrow_lifetime/03_lifetimes.md) 权威页一致；
> 干扰项针对常见误解设计。

### Q11. 🟢【单选】以下哪组准确描述了 Rust 的所有权三条规则？

- A. 每个值有且仅有一个所有者；同一时刻只能有一个所有者；所有者离开作用域时值被丢弃
- B. 值可以被任意数量变量共享；垃圾回收器在不可达时回收
- C. 每个值可以有多个所有者，由引用计数决定何时释放
- D. 所有权（Ownership）由程序员用 `free` 显式归还

<details>
<summary>✅ 答案与解析</summary>

**答案：A**

**解析**：三条规则是：(1) 每个值都有一个称为**所有者**的变量；(2) 同一时间只能有一个所有者；(3) 所有者离开作用域时值被 drop。B 描述的是 GC 语言（Rust 无 GC）；C 描述的是 `Rc`/`Arc` 的**运行时（Runtime）共享所有权**，是补充机制而非默认规则；D 是 C 的手动管理，Rust 的释放是自动且确定性的。

</details>

---

### Q12. 🟡【单选】在什么条件下可以同时存在多个 `&mut` 可变引用？

- A. 任何情况下都不可以，编译器一律拒绝
- B. 当它们的实际使用区间（NLL 分析下）互不重叠时
- C. 只要它们指向不同的变量就可以
- D. 包在 `unsafe` 块中就可以

<details>
<summary>✅ 答案与解析</summary>

**答案：B**

**解析**：独占性约束针对的是**同一数据的重叠使用**。在非词法生命周期（NLL）下，前一个 `&mut` 最后一次使用之后即可创建新的 `&mut`（顺序使用合法）。C 有教学价值：指向**不同**数据的 `&mut` 本来就互不干扰，规则从不是"全程序只能有一个"；D 错：`unsafe` 不放宽借用（Borrowing）检查，借用规则在安全 Rust 与 unsafe Rust 中同样由编译器强制执行。

</details>

---

### Q13. 🟡【多选】关于生命周期标注（`'a`），下列说法正确的有？（选出所有正确项）

- A. 标注不改变任何运行时（Runtime）行为，只向编译器描述引用间的有效关系
- B. 给引用标注更长的生命周期（Lifetimes）可以让被引用的值活得更久
- C. 标注表达的是约束：输出引用的有效期不超过相关输入引用
- D. 函数返回引用时，总是必须手写生命周期标注

<details>
<summary>✅ 答案与解析</summary>

**答案：A、C**

**解析**：生命周期标注是**描述性**的而非**指令性**的——它把代码中已存在的借用关系显式化，供编译器验证（A、C）。B 是经典误解：标注不能延长任何值的实际存活时间，值仍由其所有者作用域决定。D 错：生命周期省略（Lifetime Elision）规则（elision rules）覆盖了多数常见模式（如单输入引用、含 `&self` 的方法），只有编译器无法推断时才需显式标注。

</details>

---

### Q14. 🟢【判断】可变引用是独占的：在 `&mut T` 存活期间，不能通过其他任何路径（包括原变量本身）访问该数据。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：对**

**解析**：这是"可变借用（Mutable Borrow） = 独占访问"原则的直接推论：持有 `&mut s` 期间，连 `s` 本身也不能读（`println!("{s}")` 会被拒绝）。这一原则把"别名 + 可变"这对数据竞争/迭代器（Iterator）失效的根源在编译期彻底分离——同一时刻要么多个只读别名，要么一个独占可变访问，二者不可兼得。

</details>

---

### Q15. 🔴【判断】生命周期省略规则（elision rules）覆盖了所有情况，因此 Rust 代码中永远不需要手写生命周期标注。（对 / 错）

<details>
<summary>✅ 答案与解析</summary>

**答案：错**

**解析**：省略规则只处理三种模式（每个输入引用各自独立生命周期；单输入引用赋给输出；`&self`/`&mut self` 方法输出绑定到 self）。当输出引用依赖**多个**输入引用且无 `self` 时（如 `fn longest(x: &str, y: &str) -> &str`），编译器无法确定输出借用自谁，必须显式标注 `'a`。省略是"常见模式的便利"，不是"全情况自动推断"——否则就成了一个未解的全局程序分析问题。

</details>

---

## 六、评分参考

| 得分 | 评价 | 建议 |
|:---:|:---|:---|
| 10/10 | 🏆 所有权（Ownership）系统已内化 | 直接进阶至 [L2 智能指针（Smart Pointer）](../../02_intermediate/02_memory_management/01_memory_management.md) |
| 7–9/10 | ✅ 核心概念掌握 | 强化 [L1 练习](../../exercises/src/ownership_borrowing)，关注错题对应的概念文件 |
| 4–6/10 | 🔄 需巩固基础 | 重读 [Ownership](../01_ownership_borrow_lifetime/01_ownership.md) · [Borrowing](../01_ownership_borrow_lifetime/02_borrowing.md) · [Lifetimes](../01_ownership_borrow_lifetime/03_lifetimes.md)，完成 rustlings 对应章节 |
| 0–3/10 | 📚 建议重新开始 | 从 [Ownership](../01_ownership_borrow_lifetime/01_ownership.md) 逐节阅读，配合 [crates/c01_ownership_borrow_scope](../../crates/c01_ownership_borrow_scope) 可编译示例 |

---

## 七、试点说明

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

本节从测验 1：本文件是 测验：所有权、借用与生命周期（试点） 的专项测验集…、测验 2：在 测验：所有权、借用与生命周期（试点） 的测验中，若遇到不…与测验 3：专项测验与概念文件末尾的嵌入式测验有什么区别？（理解层）切入，剖析「嵌入式测验（Embedded Quiz）」的核心内容。

### 测验 1：🟢 本文件是 测验：所有权、借用与生命周期（试点） 的专项测验集。这类测验文件的主要作用是什么？（理解层）

**题目**: 本文件是 测验：所有权（Ownership）、借用（Borrowing）与生命周期（Lifetimes）（试点） 的专项测验集。这类测验文件的主要作用是什么？

<details>
<summary>✅ 答案与解析</summary>

集中提供大量针对特定主题的练习题，帮助学习者系统检验和巩固对该主题的掌握程度，补充概念文件中的嵌入式测验。
</details>

---

### 测验 2：🟢 在 测验：所有权、借用与生命周期（试点） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？（理解层）

**题目**: 在 测验：所有权（Ownership）、借用（Borrowing）与生命周期（Lifetimes）（试点） 的测验中，若遇到不确定答案的题目，最佳的学习策略是什么？

<details>
<summary>✅ 答案与解析</summary>

先尝试独立作答，然后对照答案解析理解错误原因，最后回到对应的概念文件重新阅读相关章节，形成"测验-反馈-复习"的闭环。
</details>

---

### 测验 3：🟢 专项测验与概念文件末尾的嵌入式测验有什么区别？（理解层）

**题目**: 专项测验与概念文件末尾的嵌入式测验有什么区别？

<details>
<summary>✅ 答案与解析</summary>

专项测验题量更大、覆盖更全面，通常按难度分层；嵌入式测验更精简，直接关联刚阅读的概念内容，用于即时检验理解。
</details>
