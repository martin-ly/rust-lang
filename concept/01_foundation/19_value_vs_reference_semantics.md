> **内容分级**: [综述级]
>
# 值语义 vs 引用语义：从 C++、Java、Python 到 Rust
>
> **EN**: Value Semantics vs Reference Semantics
> **Summary**: A cross-language comparison of value semantics and reference semantics, positioning Rust's ownership model as an extreme form of value semantics.
>
> **受众**: [初学者]
> **层级**: L1 基础概念
> **A/S/P 标记**: C+S — Comparison + Structure
> **双维定位**: C×Ana
> **前置概念**: [Ownership](01_ownership.md) · [Variable Model](20_variable_model.md) · [学习指南](../00_meta/learning_guide.md)
> **后置概念**: [Move Semantics](23_move_semantics.md) · [Borrowing](02_borrowing.md)
> **主要来源**: · [Rust Reference — Pointer Types](https://doc.rust-lang.org/reference/types/pointer.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/)
>
> [Pierce — TAPL, §13](https://www.cis.upenn.edu/~bcpierce/tapl/) ·
> [Cardelli & Wegner 1985 — On Understanding Types, Data Abstraction, and Polymorphism](https://doi.org/10.1145/6041.6042) ·
> [TRPL Ch 4 — What is Ownership?](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html) ·
> [cppreference — Value categories](https://en.cppreference.com/w/cpp/language/value_category) ·
> [Bjarne Stroustrup — New Value Terminology](https://www.stroustrup.com/terminology.pdf) ·
> [CppCon 2023 — Mateusz Pusz, Value Categories](https://www.youtube.com/watch?v=U7xx6gyaiio)
>
---

> **Bloom 层级**: 理解 → 分析


---

## 认知路径

> **认知路径**: 本节从 "值语义 vs 引用（Reference）语义" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 值语义 vs 引用（Reference）语义 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 值语义 vs 引用语义 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与值语义 vs 引用语义的适用边界。
5. **迁移应用**: 将 值语义 vs 引用语义 与前置/后置概念链接，形成跨层知识网络。


---

## 反命题决策树

> **反命题 1**: "值语义 vs 引用语义 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 值语义 vs 引用语义 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 值语义 vs 引用语义 规则被违反的直接信号。

> **反命题 3**: "其他语言对 值语义 vs 引用语义 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 值语义 vs 引用语义 具有语言特有的形态。


## 一、核心命题

> **变量赋值时，传递的到底是"值的副本"还是"引用（Reference）的副本"？
> 这个问题的答案把编程语言分成两大阵营：
> C++ 和 Rust 倾向于值语义；Java 和 Python 倾向于引用语义。
> Rust 的所有权（Ownership）系统把值语义推向了极致：默认转移所有权，显式借用（Borrowing），编译期防止别名冲突。**

---

## 二、值语义（Value Semantics）

### 2.1 定义

> **值语义**：变量绑定的是值本身。赋值、传参时复制的是值的内容。

```cpp
// C++
int a = 42;
int b = a;  // b 是 a 的副本
b = 100;    // 不影响 a
std::cout << a; // 42
```

```rust
// Rust
let a = 42;
let b = a;  // b 是 a 的副本（i32 实现 Copy）
let b = 100; // 不影响 a
println!("{}", a); // 42
```

### 2.2 值语义的语言

- **C**：基本类型和 struct 都是值语义。
- **C++**：默认值语义，但可以通过指针/引用实现引用语义。
- **Swift**：结构体（Struct）是值语义，类是引用语义。
- **Rust**：几乎所有类型默认都是值语义（包括 `String`、`Vec` 等堆分配类型，只是它们的 move 转移了所有权（Ownership））。

---

## 三、引用语义（Reference Semantics）

### 3.1 定义

> **引用语义**：变量绑定的是对象的引用（地址）。赋值、传参时复制的是引用，多个变量可以指向同一个对象。

```python
# Python
a = [1, 2, 3]
b = a   # b 和 a 指向同一个列表对象
b[0] = 99
print(a)  # [99, 2, 3]
```

```java
// Java
List<Integer> a = new ArrayList<>(Arrays.asList(1, 2, 3));
List<Integer> b = a; // b 和 a 指向同一个对象
b.set(0, 99);
System.out.println(a); // [99, 2, 3]
```

### 3.2 引用语义的语言

- **Java**：对象都是引用语义，基本类型是值语义。
- **Python**：变量都是对象的引用。
- **JavaScript**：对象/数组是引用语义，基本类型是值语义。
- **Ruby**：所有变量都是对象的引用。

---

## 四、Rust：值语义的极致

### 4.1 默认行为

```rust
let s1 = String::from("hello");
let s2 = s1; // 不是复制，而是 move：所有权从 s1 转移到 s2
// println!("{}", s1); // ❌ 编译错误
```

Rust 的 `String` 看起来像引用语义语言中的对象，但行为完全不同（Rust Reference: [Moved and Copied Types](https://doc.rust-lang.org/reference/expressions.html#moved-and-copied-types)）：

- 赋值不复制数据，而是转移所有权（Ownership）。
- 不能有两个所有者同时存在。
- 如果需要共享，必须显式使用 `&T` / `&mut T` / `Rc<T>` / `Arc<T>`。

### 4.2 显式引用

```rust
let s1 = String::from("hello");
let s2 = &s1; // 显式借用
println!("{} {}", s1, s2); // ✅ 都可用
```

Rust 把"引用"从默认行为变成了显式选择，并通过生命周期（Lifetimes）和借用（Borrowing）规则保证安全。

---

## 五、核心对比

| 维度 | 值语义（C++/Rust） | 引用语义（Java/Python） | Rust 所有权 |
|:---|:---|:---|:---|
| 赋值含义 | 复制值 / 转移所有权 | 复制引用 | 转移所有权（默认） |
| 别名问题 | 无（每个变量独立） | 有（多个引用指向同一对象） | 编译期禁止可变别名 |
| 默认共享 | 不可共享 | 可共享 | 不可共享，需显式借用（Borrowing） |
| 内存管理 | RAII / 所有权 | 垃圾回收 | 所有权 + RAII |
| 性能特征 | 可能复制大数据 | 只复制引用 | move 是 cheap，clone 是显式 |
| 安全性 | 复制开销，但无别名 bug | 可能有别名/数据竞争 | 编译期排除别名 bug |

---

## 六、值语义谱系

```text
C struct ............... 纯值语义，按位复制
C++ class .............. 值语义 + 拷贝/移动构造函数
Swift struct ........... 值语义，写时复制优化
Rust owned type ........ 值语义 + 所有权转移
Rust &T / &mut T ....... 显式受限引用
Java/Python object ..... 引用语义
```

> **关键洞察**：Rust 的独特之处在于，它把"值语义"从"复制数据"推进到"转移所有权"，从而在不使用垃圾回收的情况下，同时获得值语义的可预测性和引用语义的共享能力（通过显式借用）。

---

## 七、总结

- **L1**：值语义传递副本，引用语义传递引用；Rust 默认是值语义，`!Copy` 类型通过 move 转移所有权。
- **L2**：Rust 的所有权系统消除了引用语义语言中常见的别名 bug，同时通过显式借用提供可控的共享。
- **L3**：Rust 把值语义推向了"所有权转移"的极端，用编译期约束替代了运行时（Runtime）的垃圾回收和手动同步，这是其在系统编程中实现内存安全（Memory Safety）的核心设计。

---

## 八、延伸阅读

- [TRPL: What Is Ownership?](https://doc.rust-lang.org/book/ch04-01-what-is-ownership.html)
- [TRPL: References and Borrowing](https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html)
- [Rust Reference: Place Expressions and Value Expressions](https://doc.rust-lang.org/reference/expressions.html#place-expressions-and-value-expressions)
- [Pierce TAPL, §13 — References](https://www.cis.upenn.edu/~bcpierce/tapl/)
- [Cardelli & Wegner — On Understanding Types, Data Abstraction, and Polymorphism](https://dl.acm.org/doi/10.1145/6041.6042)
- [cppreference: Value Categories](https://en.cppreference.com/w/cpp/language/value_category)
- [Bjarne Stroustrup — New Value Terminology](https://www.stroustrup.com/terminology.pdf)
- [CppCon 2023 — Mateusz Pusz: Value Categories](https://www.youtube.com/watch?v=U7xx6gyaiio)
