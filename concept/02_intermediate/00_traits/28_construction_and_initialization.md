> **内容分级**: [参考级]
>
# 构造与初始化：C++ 的构造函数 vs Rust 的结构体字面量
>
> **EN**: Construction and Initialization
> **Summary**: Comparison of object construction and initialization between C++ (constructors, initializer lists, copy/move semantics) and Rust (struct literals, associated functions, Default, const fn).
>
> **受众**: [进阶]
> **层级**: L2 进阶概念
> **A/S/P 标记**: C+S — Comparison + Structure
> **双维定位**: C×Ana
> **前置概念**: [Variable Model](../../01_foundation/03_values_and_references/20_variable_model.md) · [Type System](../../01_foundation/02_type_system/04_type_system.md) · [Ownership](../../01_foundation/01_ownership_borrow_lifetime/01_ownership.md)
> **后置概念**: [Rust vs C++](../../05_comparative/01_systems_languages/01_rust_vs_cpp.md) · [C++ Surface Features](../../05_comparative/00_paradigms/16_cpp_rust_surface_features.md)
> **主要来源**: · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
>
> [TRPL Ch 5 — Using Structs](https://doc.rust-lang.org/book/ch05-00-structs.html) ·
> [Rust Reference — const fn](https://doc.rust-lang.org/reference/const_eval.html#const-functions) ·
> [cppreference — Constructors](https://en.cppreference.com/w/cpp/language/constructor) ·
> [cppreference — Default constructor](https://en.cppreference.com/w/cpp/language/default_constructor) ·
> [cppreference — Copy constructor](https://en.cppreference.com/w/cpp/language/copy_constructor) ·
> [cppreference — Move constructor](https://en.cppreference.com/w/cpp/language/move_constructor) ·
> [Brown CRP — Copy and Move Constructors](https://cel.cs.brown.edu/crp/idioms/constructors/copy_and_move_constructors.html) ·
> [Stroustrup — The C++ Programming Language, 4th ed.](https://www.stroustrup.com/4th.html)
>
---

> **Bloom 层级**: 理解 → 分析

---

## 认知路径

> **认知路径**: 本节从 "构造与初始化" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 构造与初始化 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 构造与初始化 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与构造与初始化的适用边界。
5. **迁移应用**: 将 构造与初始化 与前置/后置概念链接，形成跨层知识网络。

---

> **过渡**: 从 构造与初始化 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 构造与初始化 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 构造与初始化 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: 构造与初始化 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 构造与初始化 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 构造与初始化 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

---

## 反命题决策树

> **反命题 1**: "构造与初始化 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 构造与初始化 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 构造与初始化 规则被违反的直接信号。

> **反命题 3**: "其他语言对 构造与初始化 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 构造与初始化 具有语言特有的形态。

---

> **反向推理 1**: 如果程序在 构造与初始化 相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。
>
> **反向推理 2**: 如果某段代码在运行时（Runtime）表现出非预期行为且与 构造与初始化 有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。

## 一、核心命题

> **对象如何被创建，决定了一门语言如何管理资源、如何表达不变量、如何防止未初始化状态。
> C++ 把构造视为一种特殊的语言机制：构造函数、初始化列表、拷贝/移动构造函数、转换构造函数等；
> Rust 把构造去语法化：结构体（Struct）字面量、关联函数、`Default`、`const fn` 和 Builder 模式共同承担构造职责。**

---

## 二、C++ 的构造体系

### 2.1 构造函数与初始化列表

```cpp
class Point {
    double x_, y_;
public:
    Point(double x, double y) : x_(x), y_(y) {}
};

Point p{1.0, 2.0}; // 列表初始化
```

C++ 提供丰富的构造机制：

- **默认构造函数**：无参构造
- **拷贝构造函数**：`T(const T&)`
- **移动构造函数**：`T(T&&)`
- **委托构造函数**：一个构造函数调用另一个
- **转换构造函数**：单参数构造函数可导致隐式转换
- **初始化列表**：在构造函数体之前初始化成员

### 2.2 聚合初始化

```cpp
struct Point { double x, y; };
Point p{1.0, 2.0}; // 聚合初始化
```

C++11 起的聚合初始化让 POD/聚合类型可以用类似 C 的语法初始化。

### 2.3 三/五/零法则（Rule of Three/Five/Zero）

| 法则 | 含义 | 示例 |
|:---|:---|:---|
| **Rule of Three** | 若自定义析构/拷贝构造/拷贝赋值任一，三者都需自定义 | 管理动态内存的类 |
| **Rule of Five** | C++11 增加移动构造/移动赋值 | 高性能资源管理类 |
| **Rule of Zero** | 让编译器自动生成，不自定义任何特殊成员 | 使用智能指针（Smart Pointer）的现代类 |

---

## 三、Rust 的初始化模型

### 3.1 结构体字面量

```rust
struct Point { x: f64, y: f64 }

let p = Point { x: 1.0, y: 2.0 };
let q = Point { x: 0.0, ..p }; // 结构体更新语法
```

Rust 没有构造函数语言特性。创建对象使用结构体（Struct）字面量或关联函数。

### 3.2 `new` 约定与关联函数

```rust
impl Point {
    fn new(x: f64, y: f64) -> Self {
        Point { x, y }
    }

    fn origin() -> Self {
        Point { x: 0.0, y: 0.0 }
    }
}

let p = Point::new(1.0, 2.0);
let o = Point::origin();
```

`new` 不是关键字，只是约定。一个类型可以有多个构造关联函数。

### 3.3 `Default` trait

```rust
#[derive(Default)]
struct Config {
    timeout: u64,
    verbose: bool,
}

let cfg = Config::default();
```

`Default::default()` 提供零参数构造的等价物，与 C++ 默认构造函数对应。

### 3.4 `const fn` 编译期构造

```rust
struct Point { x: f64, y: f64 }

const fn origin() -> Point {
    Point { x: 0.0, y: 0.0 }
}

const ORIGIN: Point = origin();

fn main() {
    let _ = ORIGIN;
}
```

`const fn` 允许在编译期构造值，这是 C++ `constexpr` 构造函数的对应物。

---

## 四、核心对比

| 维度 | C++ | Rust |
|:---|:---|:---|
| 创建对象 | 构造函数（语言内建） | 结构体（Struct）字面量 / 关联函数 |
| 默认构造 | 默认构造函数 | `Default` trait / 结构体（Struct）字面量 |
| 初始化列表 | `:` 后的成员初始化列表 | 结构体（Struct）字面量 `{}` / 更新语法 `..` |
| 拷贝/移动 | 拷贝/移动构造函数 | `Copy`/`Clone` trait / 所有权（Ownership）移动 |
| 隐式转换 | 单参数构造函数可导致 | 无隐式转换 |
| 编译期构造 | `constexpr` 构造函数 | `const fn` |
| 未初始化 | 可能（如默认初始化 POD） | 禁止，所有变量必须初始化 |

---

## 五、C++ 三/五/零法则 vs Rust

C++ 需要 Rule of Three/Five 是因为手动管理资源。Rust 通过所有权（Ownership）系统消除了这个问题：

```rust
struct Buffer {
    data: Vec<u8>,
}

// 不需要写析构函数、拷贝构造函数、移动构造函数
// Vec 的 Drop/Clone 会自动处理
```

在 Rust 中，只要字段实现了正确的 trait，复合类型自动获得对应能力：

- 所有字段 `Copy` → 整体可 `Copy`
- 所有字段 `Clone` → 整体可 `Clone`
- 任一字段需要 `Drop` → 整体自动 `Drop`

这等价于 C++ 的 Rule of Zero，但由类型系统（Type System）强制执行。

---

## 六、形式化视角

C++ 构造函数可以形式化为**从参数到对象状态的偏函数**：

```text
construct_T: Args → T ∪ ⊥
```

异常或失败时返回 ⊥。

Rust 的构造可以形式化为**结构体（Struct）字段的元组构造**：

```text
Point::new(x, y) = Point { x, y }
```

没有特殊的构造语义，只是普通的函数返回。

> **关键洞察**：C++ 的构造函数是对象生命周期（Lifetimes）管理的特权语法；Rust 把构造降级为普通函数调用 + 结构体（Struct）组合，从而让所有构造行为都受相同的类型系统（Type System）规则约束。

---

## 七、总结

- **L1**：Rust 没有 C++ 的构造函数，用结构体字面量和关联函数（如 `new`）创建对象。
- **L2**：Rust 的 `Default`、`Clone`、`Copy`、`Drop` trait 替代了 C++ 的默认/拷贝/移动构造函数和析构函数；不需要 Rule of Three/Five。
- **L3**：Rust 去语法化的构造模型让所有对象创建行为都受类型系统（Type System）和所有权（Ownership）规则约束，消除了 C++ 中因构造函数特权语法导致的隐式转换、未初始化、异常安全等复杂问题。

---

## 八、延伸阅读

- [TRPL: Using Structs](https://doc.rust-lang.org/book/ch05-00-structs.html)
- [Rust Reference: Struct Expressions](https://doc.rust-lang.org/reference/expressions/struct-expr.html)
- [Rust Reference: const fn](https://doc.rust-lang.org/reference/const_eval.html#const-functions)
- [std::default::Default](https://doc.rust-lang.org/std/default/trait.Default.html)
- [cppreference: Constructors](https://en.cppreference.com/w/cpp/language/constructor)
- [cppreference: Default constructor](https://en.cppreference.com/w/cpp/language/default_constructor)
- [cppreference: Copy constructor](https://en.cppreference.com/w/cpp/language/copy_constructor)
- [cppreference: Move constructor](https://en.cppreference.com/w/cpp/language/move_constructor)
- [Brown CRP: Copy and Move Constructors](https://cel.cs.brown.edu/crp/idioms/constructors/copy_and_move_constructors.html)
- [Stroustrup — The C++ Programming Language, 4th ed.](https://www.stroustrup.com/4th.html)
