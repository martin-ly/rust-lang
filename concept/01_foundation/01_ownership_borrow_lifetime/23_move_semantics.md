> **内容分级**: [综述级]
>
# Move 语义：C++ 与 Rust 的资源转移模型
>
> **EN**: Move Semantics
> **Summary**: A focused comparison of move semantics in C++ (move constructors, xvalues, moved-from state) and Rust (ownership transfer, Copy/Clone, compiler-enforced invalidation).
>
> **受众**: [初学者]
> **权威来源**: 本文件为 `concept/` 权威页。
> **层级**: L1 基础概念
> **A/S/P 标记**: C+S — Comparison + Structure
> **双维定位**: C×Ana
> **前置概念**: [Ownership](01_ownership.md) · [Variable Model](../03_values_and_references/20_variable_model.md) · [Borrowing](02_borrowing.md) · [学习指南](../../00_meta/04_navigation/learning_guide.md)
> **后置概念**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) · [Construction](../../02_intermediate/00_traits/28_construction_and_initialization.md)
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

> **Bloom 层级**: L1-L4

---
> **权威来源**: [Rust Reference — Moved and Copied Types](https://doc.rust-lang.org/reference/expressions.html#moved-and-copied-types) · [TRPL — What is Ownership?](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html) · [TRPL — References and Borrowing](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html)
>
> **权威来源对齐变更日志**: 2026-07-10 补充权威来源标注（Rust Reference、TRPL）

---
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

Rust 保证：返回局部值不会发生深拷贝，只是所有权（Ownership）转移。

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
- **L3**：C++ move 是复杂值类别体系和特殊成员函数的产物；Rust move 是所有权（Ownership）系统的基本操作，消除了 moved-from 状态、双重释放和使用已释放对象等整类错误。

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

---

## 国际权威参考 / International Authority References（P1 学术 · P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [Learn Rust With Entirely Too Many Linked Lists](https://rust-unofficial.github.io/too-many-lists/)
