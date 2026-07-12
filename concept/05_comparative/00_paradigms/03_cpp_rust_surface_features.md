> **内容分级**: [研究级]
>
# C++ vs Rust：构造、运算符、RTTI、友元
>
> **EN**: C++ vs Rust: Construction, Operators, RTTI, and Friends
> **Summary**: A focused comparison of C++ and Rust surface-level object-oriented features: constructors/initialization, operator overloading, RTTI, and access control (friend vs module privacy).
> **Rust 版本**: 1.97.0+ (Edition 2024)
>
> **受众**: [进阶]
> **权威来源**: 本文件为 `concept/` 权威页。
> **层级**: L3 进阶对比
> **A/S/P 标记**: **S+A** — Structure + Application
> **双维定位**: C×Ana
> **前置概念**: [Rust vs C++](../01_systems_languages/01_rust_vs_cpp.md) · [Variable Model](../../01_foundation/03_values_and_references/03_variable_model.md) · [RTTI](../../02_intermediate/04_types_and_conversions/05_rtti_and_dynamic_typing.md) · [所有权（Ownership）形式化](../../04_formal/01_ownership_logic/02_ownership_formal.md)
> **后置概念**: [C++ ABI Object Model](../01_systems_languages/02_cpp_abi_object_model.md) · [Traits](../../02_intermediate/00_traits/01_traits.md)
> **主要来源**: [Stroustrup — The C++ Programming Language, 4th ed.](https://www.stroustrup.com/4th.html) · [TRPL Ch 5 — Using Structs](https://doc.rust-lang.org/book/ch05-00-structs.html) · [TRPL Ch 19 — Advanced Features](https://doc.rust-lang.org/book/ch19-00-advanced-features.html) · [Rust Reference — Operators and Overloading](https://doc.rust-lang.org/reference/items/implementations.html#trait-implementations) · [Rust Reference — std::ops](https://doc.rust-lang.org/std/ops/index.html) · [Rust Reference — Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html) · [cppreference — Constructors](https://en.cppreference.com/w/cpp/language/constructor) · [cppreference — typeid](https://en.cppreference.com/w/cpp/language/typeid) · [cppreference — dynamic_cast](https://en.cppreference.com/w/cpp/language/dynamic_cast) · [cppreference — Friend](https://en.cppreference.com/w/cpp/language/friend) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
---

> **Bloom 层级**: L3-L5

---

## 一、核心命题

> **C++ 和 Rust 在"如何表达对象行为"上走了两条不同的路。
> C++ 通过构造函数、运算符重载、RTTI、`friend` 等语言内建机制，把面向对象能力直接嵌入语法；
> Rust 则把这些能力拆散到类型系统（Type System）、trait、模块（Module）可见性和标准库中，用显式约束替代隐式规则。**

---

## 二、构造与初始化

「构造与初始化」部分按 C++：构造函数与初始化列表、Rust：结构体字面量 + `new` 约定与对比表的顺序逐层展开。

### 2.1 C++：构造函数与初始化列表

```cpp
struct Point {
    int x;
    int y;

    Point(int x_, int y_) : x(x_), y(y_) {}
};

Point p{3, 4}; // 列表初始化
```

C++ 提供多种初始化语法（`()`、`{}`、`=`、默认初始化、值初始化），并允许：

- 多个构造函数重载
- 默认参数构造函数
- 拷贝/移动构造函数
- 委托构造函数
- `explicit` 防止隐式转换

### 2.2 Rust：结构体字面量 + `new` 约定

Rust 没有传统意义上的"构造函数"语言特性：

```rust
struct Point { x: i32, y: i32 }

impl Point {
    fn new(x: i32, y: i32) -> Self {
        Point { x, y }
    }
}

let p = Point::new(3, 4);
let q = Point { x: 1, ..p }; // 结构体更新语法
```

- 字段默认不可外部访问，除非标记为 `pub`。
- 创建对象使用结构体（Struct）字面量或关联函数（通常是 `new`）。
- 不存在隐式转换，因此不需要 `explicit`。
- 拷贝/移动由 `Copy`/`Clone` trait 控制，不是构造函数。

### 2.3 对比表

| 维度 | C++ | Rust |
|:---|:---|:---|
| 构造函数 | 语言内建，支持重载 | 普通关联函数（约定 `new`） |
| 初始化列表 | `:` 后的成员初始化列表 | 结构体（Struct）字面量 `{}` |
| 默认初始化 | 可能不初始化（未定义行为） | 所有变量必须初始化 |
| 隐式转换 | 单参数构造函数可导致隐式转换 | 无隐式转换 |
| 拷贝/移动 | 拷贝/移动构造函数 | `Copy`/`Clone` trait |
| RAII | 构造函数获取资源，析构函数释放 | `Drop` trait 释放资源 |

---

## 三、运算符重载

> **详细讨论见 [类型系统（Type System）基础：运算符重载](../../01_foundation/02_type_system/01_type_system.md)。
> 本节只给出 C++ vs Rust 的速查对比。**

| 维度 | C++ | Rust |
|:---|:---|:---|
| 机制 | 语言内建运算符重载 | 标准库 trait（`std::ops::Add` 等） |
| 位置 | 成员函数或自由函数 | `impl Trait for Type` |
| 可重载运算符 | 大量（含 `new`、`delete`、`->`） | 有限集合（算术/位运算/索引/解引用（Reference）等） |
| 返回类型约束 | 无 | 由 trait 关联类型 `Output` 约束 |
| 隐式调用风险 | 高（尤其与隐式转换结合） | 低（无隐式转换，参数类型严格） |
| 类型检查 | 重载决议 | trait bound 求解 |

---

## 四、RTTI

C++ 与 Rust 的 RTTI 对比已在 [RTTI 与动态类型识别](../../02_intermediate/04_types_and_conversions/05_rtti_and_dynamic_typing.md) 中详细讨论。本节仅给出速查：

| 能力 | C++ | Rust |
|:---|:---|:---|
| 获取类型信息 | `typeid(x)` | `TypeId::of::<T>()` |
| 安全向下转换 | `dynamic_cast<T*>(p)` | `Any::downcast_ref::<T>()` |
| 类型擦除 | `void*` / 多态基类 | `dyn Any` / trait objects |
| 多态要求 | 需要虚函数 | 不需要 |

---

## 五、友元 vs 模块可见性

理解「友元 vs 模块可见性」需要把握 C++ `friend`、Rust 模块可见性与对比，本节依次展开。

### 5.1 C++ `friend`

```cpp
class Wallet {
private:
    int balance = 0;
public:
    friend class Auditor; // Auditor 可访问私有成员
};
```

`friend` 破坏了类的封装边界，允许指定类或函数访问私有成员。

### 5.2 Rust 模块可见性

Rust 没有 `friend`，用模块（Module）系统控制可见性：

```rust
mod wallet {
    pub struct Wallet { balance: i32 }

    impl Wallet {
        pub fn new() -> Self { Wallet { balance: 0 } }
        pub(super) fn balance(&self) -> i32 { self.balance } // 对父模块可见
    }
}
```

- `pub`：完全公开
- `pub(crate)`：crate 内可见
- `pub(super)`：父模块（Module）可见
- `pub(in path)`：指定路径可见
- 默认私有

### 5.3 对比

| 维度 | C++ `friend` | Rust 模块（Module）可见性 |
|:---|:---|:---|
| 机制 | 授予外部类/函数私有访问权 | 通过模块（Module）层级控制可见性 |
| 封装影响 | 显式破坏封装 | 封装保持完整，边界清晰 |
| 测试支持 | 依赖 `friend` 或 `protected` | 使用 `pub(crate)` 或 `#[cfg(test)]` |
| 可审计性 | 分散的 `friend` 声明难以追踪 | 模块（Module）树 + 可见性修饰符一目了然 |

---

## 六、形式化视角

C++ 的 OO 特性是**语法内建**的：构造函数、运算符、`friend` 都是编译器直接识别的特殊语法。Rust 把这些能力**去语法化**，全部表达为类型系统（Type System）或库机制：

- 构造 → 关联函数/结构体（Struct）字面量
- 运算符 → trait
- RTTI → `Any` trait
- 友元 → 模块可见性

> **关键洞察**：Rust 的设计哲学是"没有特权语法"——同样的类型系统（Type System）规则同时约束普通代码和"面向对象"代码，从而减少意外行为和隐式依赖。

---

## 七、总结

- **L1**：Rust 没有 C++ 的构造函数、运算符重载、`friend`、RTTI 语法，但用 `new` 约定、标准库 trait、模块可见性、`Any` trait 实现了等价能力。
- **L2**：C++ 的这些特性更灵活但也更危险（隐式转换、封装破坏）；Rust 通过显式约束降低了误用风险。
- **L3**：Rust 把 OO 表面特性"去语法化"，全部纳入统一的类型系统（Type System），这是其"无特权语法"设计哲学的体现。

---

## 八、延伸阅读

- [TRPL: Method Syntax](https://doc.rust-lang.org/book/ch05-03-method-syntax.html)
- [TRPL: Advanced Features](https://doc.rust-lang.org/book/ch19-00-advanced-features.html)
- [Rust Reference: Operators and Overloading](https://doc.rust-lang.org/std/ops/index.html)
- [Rust Reference: Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html)
- [cppreference: Constructors](https://en.cppreference.com/w/cpp/language/constructor)
- [cppreference: typeid](https://en.cppreference.com/w/cpp/language/typeid)
- [cppreference: dynamic_cast](https://en.cppreference.com/w/cpp/language/dynamic_cast)
- [cppreference: Friend](https://en.cppreference.com/w/cpp/language/friend)
- [RTTI 与动态类型识别](../../02_intermediate/04_types_and_conversions/05_rtti_and_dynamic_typing.md)
- [C 预处理器 vs Rust 宏（Macro）](../../02_intermediate/06_macros_and_metaprogramming/05_c_preprocessor_vs_rust_macros.md)
- [异常安全](../../02_intermediate/03_error_handling/04_exception_safety_rust_cpp.md)
- [构造与初始化](../../02_intermediate/00_traits/05_construction_and_initialization.md)
- [友元 vs 模块隐私](../../02_intermediate/05_modules_and_visibility/02_friend_vs_module_privacy.md)
- [Rust vs C++](../01_systems_languages/01_rust_vs_cpp.md)

---

> **Checklist**: 已覆盖 构造/初始化 · 运算符重载 · RTTI · 友元 / 提供 C++ vs Rust 对照 / 衔接既有专门文件。

---

## 权威来源（References · 跨语言国际权威对齐）

> 仅追加被对比语言的官方权威入口与 Rust 对照，闭合跨语言对标覆盖；不改本文正文（AGENTS.md §2）。

- **cppreference**: <https://en.cppreference.com/>
- **C++ Core Guidelines**: <https://isocpp.github.io/CppCoreGuidelines/CppCoreGuidelines.html>
- **Rust Reference（对照）**: <https://doc.rust-lang.org/reference/>
- **TRPL（对照）**: <https://doc.rust-lang.org/book/title-page.html>

---

## 国际权威参考 / International Authority References（P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [docs.rs/bindgen — 生态权威 API 文档（C/C++ 接口绑定的 Rust 侧生态工具）](https://docs.rs/bindgen)（2026-07-12 验证 HTTP 200）
