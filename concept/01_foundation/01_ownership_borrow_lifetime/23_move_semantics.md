> **内容分级**: [综述级]
>
# Move 语义：C++ 与 Rust 的资源转移模型
>
> **EN**: Move Semantics
> **Summary**: A focused comparison of move semantics in C++ (move constructors, xvalues, moved-from state) and Rust (ownership transfer, Copy/Clone, compiler-enforced invalidation).
>
> **受众**: [初学者]
> **层级**: L1 基础概念
> **A/S/P 标记**: C+S — Comparison + Structure
> **双维定位**: C×Ana
> **前置概念**: [Ownership](01_ownership.md) · [Variable Model](../03_values_and_references/20_variable_model.md) · [Borrowing](02_borrowing.md) · [学习指南](../../00_meta/learning_guide.md)
> **后置概念**: [Rust vs C++](../../05_comparative/01_rust_vs_cpp.md) · [Construction](../../02_intermediate/00_traits/28_construction_and_initialization.md)
> **主要来源**: · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
>
> [TRPL Ch 4 — What is Ownership?](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html) ·
> [TRPL Ch 10 — Generic Types, Traits, and Lifetimes](https://doc.rust-lang.org/book/ch10-00-generics.html) ·
> [Rust Reference — Moved and Copied Types](https://doc.rust-lang.org/reference/expressions.html#moved-and-copied-types) ·
> [cppreference — Move Constructors](https://en.cppreference.com/w/cpp/language/move_constructor) ·
> [cppreference — Move assignment operator](https://en.cppreference.com/w/cpp/language/move_assignment) ·
> [cppreference — Value categories](https://en.cppreference.com/w/cpp/language/value_category) ·
> [Brown CRP — Copy and Move Constructors](https://cel.cs.brown.edu/crp/idioms/constructors/copy_and_move_constructors.html) ·
> [StackOverflow — How does Rust provide move semantics?](https://stackoverflow.com/questions/27922584/how-does-rust-provide-move-semantics) ·
> [The Coded Message — C++ Move Semantics Considered Harmful](https://thecodedmessage.com/posts/cpp-move-harmful/) ·
> [Stroustrup — The C++ Programming Language, 4th ed.](https://www.stroustrup.com/4th.html)
>
---

> **Bloom 层级**: 理解 → 分析

---

## 认知路径

> **认知路径**: 本节从 "Move 语义" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Move 语义 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 Move 语义 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与Move 语义的适用边界。
5. **迁移应用**: 将 Move 语义 与前置/后置概念链接，形成跨层知识网络。

---

> **过渡**: 从 Move 语义 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 Move 语义 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 Move 语义 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: Move 语义 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 Move 语义 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 Move 语义 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

---

## 反命题决策树

> **反命题 1**: "Move 语义 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 Move 语义 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 Move 语义 规则被违反的直接信号。

> **反命题 3**: "其他语言对 Move 语义 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 Move 语义 具有语言特有的形态。

---

> **反向推理 1**: 如果程序在 Move 语义 相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。
>
> **反向推理 2**: 如果某段代码在运行时（Runtime）表现出非预期行为且与 Move 语义 有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。

## 一、核心命题

> **Move 语义解决同一个问题：如何在不复制大量数据的情况下转移资源所有权（Ownership）。
> 但 C++ 和 Rust 的解决方案完全不同：
> C++ 的 move 是一种特殊的构造函数，允许程序员手动转移资源，并留下一个"有效但未指定"的源对象；
> Rust 的 move 是所有权（Ownership）系统的基本操作，只是 bitwise copy + 编译期标记源变量无效。**

---

## 二、C++ 的 Move 语义

### 2.1 `std::move` 与移动构造函数

```cpp
#include <string>
#include <utility>

std::string s1 = "hello";
std::string s2 = std::move(s1); // s1 变为 xvalue（将亡值）
// s2 调用移动构造函数，接管 s1 的内部缓冲区
// s1 仍处于"有效但未指定状态"
```

C++11 引入的 move 语义：

- `std::move(x)` 实际上只是把 `x` 转换为右值引用（Reference） `T&&`。
- 移动构造函数 `T(T&& other)` 负责转移资源。
- 移动后，源对象处于**有效但未指定状态（valid but unspecified state）**。

### 2.2 值类别

C++ 的值类别体系：

- **lvalue**：可定位的值（有名字、有地址）
- **xvalue**：将亡值（`std::move` 的结果）
- **prvalue**：纯右值（临时对象）
- **glvalue**：lvalue + xvalue
- **rvalue**：xvalue + prvalue

Move 语义依赖于这个复杂的值类别体系。

### 2.3 Moved-from 状态

```cpp
std::string s = "hello";
auto s2 = std::move(s);
// s 仍然可以调用 .empty()、.clear() 等不依赖具体值的函数
// 但不能依赖 s 的内容
```

C++ 不禁止访问 moved-from 对象，只是其值未指定。

---

## 三、Rust 的 Move 语义

### 3.1 所有权转移

```rust
fn main() {
    let s1 = String::from("hello");
    let s2 = s1; // move：所有权从 s1 转移到 s2
    // println!("{}", s1); // ❌ 编译错误：borrow of moved value
    println!("{}", s2);   // ✅
}
```

Rust 的 move（Rust Reference: [Moved and Copied Types](https://doc.rust-lang.org/reference/expressions.html#moved-and-copied-types)）：

- 对于未实现 `Copy` 的类型，赋值 = 所有权（Ownership）转移。
- 转移是 bitwise copy（对于堆分配类型是复制指针/长度/容量）。
- 源变量在编译期被标记为无效，后续访问被禁止。

> StackOverflow 上的高票回答总结为：Rust 的 move 本质上是“shallow copy + 禁止再次使用源变量”，因此不需要 C++ 式的 moved-from 状态（[How does Rust provide move semantics?](https://stackoverflow.com/questions/27922584/how-does-rust-provide-move-semantics)）。

### 3.2 `Copy` vs `Clone`

```rust
#[derive(Clone, Copy, Debug)]
struct Point { x: f64, y: f64 }

fn main() {
    let p1 = Point { x: 1.0, y: 2.0 };
    let p2 = p1; // Copy：p1 仍然可用
    println!("{:?} {:?}", p1, p2);

    let s1 = String::from("hello");
    let s2 = s1.clone(); // 显式深拷贝
    println!("{} {}", s1, s2);
}
```

- `Copy`：隐式按位复制，原变量仍可用。
- `Clone`：显式复制，可能涉及深拷贝。
- 默认 move：对于非 `Copy` 类型，转移所有权（Ownership）。

---

## 四、核心对比

| 维度 | C++ | Rust |
|:---|:---|:---|
| Move 操作 | `std::move`（类型转换）+ 移动构造函数 | 赋值语句（语言级语义） |
| 实现位置 | 构造函数体内手动转移资源 | 编译器自动 bitwise copy + 标记无效 |
| 源对象状态 | 有效但未指定 | 编译期禁止访问 |
| 值类别 | lvalue/xvalue/prvalue/glvalue/rvalue | place expression / value expression |
| 空状态 | 某些类型有（如 `std::string`） | 无，变量要么有效要么不存在 |
| 默认行为 | 拷贝构造（深拷贝） | move（所有权（Ownership）转移） |
| 显式复制 | 拷贝构造函数 | `Clone::clone()` |
| 编译期保证 | 无 | moved-from 访问被编译器拒绝 |

---

## 五、RVO 与 Copy Elision

### 5.1 C++ 拷贝省略（RVO/NRVO）

```cpp
std::string make_string() {
    return std::string("hello"); // RVO 可能省略拷贝
}
```

C++ 的 RVO 是编译器优化，直到 C++17 的 guaranteed copy elision 之前都不是强制的（cppreference: [Copy elision](https://en.cppreference.com/w/cpp/language/copy_elision)）。

### 5.2 Rust 的保证省略

Rust 的设计哲学是：move 本身就是廉价的 bitwise copy，因此不需要复杂的拷贝省略优化。

```rust
fn make_string() -> String {
    String::from("hello") // 直接构造在调用者的栈空间
}
```

Rust 保证：返回局部值不会发生深拷贝，只是所有权转移。

---

## 六、三/五/零法则 vs Copy/Clone/Drop

C++ 中管理资源需要 Rule of Three/Five/Zero。

Rust 中，复合类型的行为由字段 trait 自动推导：

| C++ | Rust |
|:---|:---|
| 析构函数 | `Drop` trait |
| 拷贝构造函数 | `Clone` trait |
| 拷贝赋值 | `Clone` + 赋值 |
| 移动构造函数 | 语言级 move |
| 移动赋值 | 语言级 move |
| Rule of Zero | 字段自动实现 `Copy`/`Clone`/`Drop` |

```rust
struct Buffer {
    data: Vec<u8>, // Vec 已实现 Drop/Clone，Buffer 自动获得
}
```

---

## 七、形式化视角

C++ move 可以形式化为：

```text
move: T → T' × T_invalid
```

即 move 后产生一个有效的新对象和一个"仍然存在但状态未指定"的源对象。

Rust move 可以形式化为：

```text
move: T@src → T@dst
```

即资源从 `src` 的变量名重新绑定到 `dst`，`src` 从环境中移除。

> **关键洞察**：C++ 的 move 是"复制 + 使源对象进入特殊状态"；Rust 的 move 是"重新绑定资源标识符"。Rust 的模型更简单，因为它不需要 moved-from 状态的概念。

---

## 八、总结

- **L1**：C++ move 调用移动构造函数，源对象变为"有效但未指定"；Rust move 是赋值语句，源变量被编译器标记为无效。
- **L2**：Rust 的 `Copy`/`Clone` 替代了 C++ 的拷贝构造；Rust 的语言级 move 替代了 C++ 的移动构造；`Drop` 替代析构函数。
- **L3**：C++ move 是复杂值类别体系和特殊成员函数的产物；Rust move 是所有权系统的基本操作，消除了 moved-from 状态、双重释放和使用已释放对象等整类错误。

---

## 九、延伸阅读

- [TRPL: What Is Ownership?](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)
- [TRPL: Generic Types, Traits, and Lifetimes](https://doc.rust-lang.org/book/ch10-00-generics.html)
- [Rust Reference: Moved and Copied Types](https://doc.rust-lang.org/reference/expressions.html#moved-and-copied-types)
- [cppreference: Move Constructors](https://en.cppreference.com/w/cpp/language/move_constructor)
- [cppreference: Move Assignment Operator](https://en.cppreference.com/w/cpp/language/move_assignment)
- [cppreference: Value Categories](https://en.cppreference.com/w/cpp/language/value_category)
- [Brown CRP: Copy and Move Constructors](https://cel.cs.brown.edu/crp/idioms/constructors/copy_and_move_constructors.html)
- [StackOverflow: How does Rust provide move semantics?](https://stackoverflow.com/questions/27922584/how-does-rust-provide-move-semantics)
- [The Coded Message: C++ Move Semantics Considered Harmful](https://thecodedmessage.com/posts/cpp-move-harmful/)
- [Stroustrup — The C++ Programming Language, 4th ed.](https://www.stroustrup.com/4th.html)
