> **内容分级**: [参考级]
>
# C 预处理器 vs Rust 宏：从文本替换到语法树
>
> **EN**: C Preprocessor vs Rust Macros
> **Summary**: Comparison between the C preprocessor (textual substitution) and Rust macros (hygienic syntax-tree metaprogramming), covering conditional compilation, include guards, and macro hygiene.
>
> **受众**: [进阶]
> **层级**: L2 进阶概念
> **A/S/P 标记**: C+S — Comparison + Structure
> **双维定位**: C×Ana
> **前置概念**: [Macros](../03_advanced/04_macros.md) · [Generics](02_generics.md) · [Traits](01_traits.md)
> **后置概念**: [Proc Macro](../03_advanced/07_proc_macro.md) · [DSL and Embedding](13_dsl_and_embedding.md)
> **主要来源**: · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [System F](https://en.wikipedia.org/wiki/System_F) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Brown Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/)
>
> [TRPL Ch 19.5 — Macros](https://doc.rust-lang.org/book/ch19-06-macros.html) ·
> [Rust Reference — macro_rules!](https://doc.rust-lang.org/reference/macros-by-example.html) ·
> [The Little Book of Rust Macros](https://veykril.github.io/tlborm/) ·
> [C Preprocessor (cppreference)](https://en.cppreference.com/w/c/preprocessor) ·
> [Rust Reference — Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html)
>
---

> **Bloom 层级**: 理解 → 分析


---

## 认知路径

> **认知路径**: 本节从 "C 预处理器 vs Rust 宏（Macro）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 C 预处理器 vs Rust 宏（Macro） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 C 预处理器 vs Rust 宏 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与C 预处理器 vs Rust 宏的适用边界。
5. **迁移应用**: 将 C 预处理器 vs Rust 宏 与前置/后置概念链接，形成跨层知识网络。


---

> **过渡**: 从 C 预处理器 vs Rust 宏 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 C 预处理器 vs Rust 宏 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 C 预处理器 vs Rust 宏 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。


---

> **定理 1** [Tier 2]: C 预处理器 vs Rust 宏 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 C 预处理器 vs Rust 宏 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 C 预处理器 vs Rust 宏 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。


---

## 反命题决策树

> **反命题 1**: "C 预处理器 vs Rust 宏 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 C 预处理器 vs Rust 宏 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 C 预处理器 vs Rust 宏 规则被违反的直接信号。

> **反命题 3**: "其他语言对 C 预处理器 vs Rust 宏 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 C 预处理器 vs Rust 宏 具有语言特有的形态。


---

> **反向推理 1**: 如果程序在 C 预处理器 vs Rust 宏 相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。
>
> **反向推理 2**: 如果某段代码在运行时（Runtime）表现出非预期行为且与 C 预处理器 vs Rust 宏 有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。


## 一、核心命题

> **C 预处理器和 Rust 宏（Macro）都叫"宏"，但本质上是两个时代的产物。
> C 预处理器在文本层面做替换，不感知语法、类型和作用域；
> Rust 宏在 token 流 / AST 层面操作，受卫生性（hygiene）约束，展开后仍受类型系统（Type System）检查。**

---

## 二、C 预处理器：文本替换模型

### 2.1 `#define`：简单文本替换

```c
#define SQUARE(x) ((x) * (x))

int a = SQUARE(5);      // 展开为 ((5) * (5))
int b = SQUARE(2 + 3);  // 展开为 ((2 + 3) * (2 + 3))
```

由于纯文本替换，必须加括号防止优先级问题。

### 2.2 副作用陷阱

```c
#define MAX(a, b) ((a) > (b) ? (a) : (b))

int x = 5;
int m = MAX(x++, 3); // x++ 可能被求值两次
```

C 宏对求值次数、副作用、作用域一无所知。

### 2.3 条件编译与头文件保护

```c
#ifndef FOO_H
#define FOO_H
// ... declarations ...
#endif
```

条件编译基于符号是否被 `#define`，用于跨平台代码、调试开关、头文件包含保护。

---

## 三、Rust 宏：语法树与卫生性

### 3.1 声明宏 `macro_rules!`

```rust
macro_rules! square {
    ($x:expr) => {
        $x * $x
    };
}

let a = square!(5);
let b = square!(2 + 3);
```

`macro_rules!` 匹配 token 模式并生成 token 树，展开后进入 AST 解析和类型检查。

### 3.2 卫生性（Hygiene）

```rust
macro_rules! make_var {
    ($name:ident, $val:expr) => {
        let $name = $val;
    };
}

fn main() {
    make_var!(x, 42);
    println!("{}", x); // ✅ 可以访问
}
```

Rust 宏内部引入的标识符不会与外部冲突，反之亦然。这由 hygiene 系统保证。

### 3.3 条件编译：`cfg` 属性

Rust 的条件编译不是宏，而是编译器内置的属性系统：

```rust
#[cfg(target_os = "linux")]
fn linux_only() {}

#[cfg(feature = "serde")]
impl Serialize for MyType {}
```

对比 C：

| 能力 | C | Rust |
|:---|:---|:---|
| 条件编译 | `#ifdef` / `#ifndef` | `#[cfg(...)]` |
| 头文件保护 | `#ifndef HEADER_H` | 模块（Module）系统天然解决 |
| 平台适配 | `#ifdef _WIN32` | `cfg(target_os = ...)` |
| 功能开关 | `#define FEATURE_X` | Cargo features + `cfg(feature = ...)` |

---

## 四、核心对比

| 维度 | C 预处理器 | Rust 宏 |
|:---|:---|:---|
| 操作对象 | 文本字符串 | Token 流 / AST |
| 类型感知 | 无 | 展开后受类型系统（Type System）检查 |
| 作用域/卫生性 | 无 | 有 hygiene，避免变量捕获 |
| 副作用风险 | 高（多次求值） | 低（参数按表达式传入） |
| 调试难度 | 高（展开后难以阅读） | 中（`cargo expand` 可查看） |
| 条件编译 | `#ifdef` | `#[cfg]` |
| 头文件包含 | `#include` | 模块（Module）系统 + `use` |
| 元编程能力 | 有限 | 声明宏（Declarative Macro） + 过程宏（Procedural Macro）完整覆盖 |

---

## 五、迁移思维

### 5.1 什么时候用 `macro_rules!` 替代 `#define`

- 需要重复代码模式 → `macro_rules!`
- 需要表达式级别的抽象 → `macro_rules!` + `expr` fragment
- 需要类型安全 → `macro_rules!` 生成代码后仍受类型检查

### 5.2 什么时候不需要宏

Rust 的泛型、trait、const generics 可以替代很多 C 宏使用场景：

```rust
// 替代 C 的泛型宏
fn max<T: Ord>(a: T, b: T) -> T {
    if a > b { a } else { b }
}
```

### 5.3 什么时候用过程宏

- `#[derive(...)]` 自动生成 trait 实现
- 自定义属性宏修改函数/结构体（Struct）
- 编译期 DSL 解析

详见 [Proc Macro](../03_advanced/07_proc_macro.md)。

---

## 六、形式化视角

C 预处理器的语义可以形式化为**文本重写系统**：

```text
#define M(x) E
M(t)  ⟶  E[x/t]
```

Rust `macro_rules!` 的语义可以形式化为**hygienic 树重写系统**：

```text
macro_rules! M($x:expr) => { E };
M!(t)  ⟶  E[x := α(t)]
```

其中 `α(t)` 表示对 `t` 中绑定标识符进行 α-重命名，以保持 hygiene。

---

## 七、总结

- **L1**：C 预处理器做文本替换；Rust 宏在语法树层面操作，更安全。
- **L2**：Rust 用 `macro_rules!`、过程宏（Procedural Macro）和 `#[cfg]` 分别替代 C 的 `#define`、模板代码生成和 `#ifdef`。
- **L3**：Rust 宏的 hygiene 和类型检查使其成为一种"受限但安全"的元编程工具，而 C 预处理器是一种无约束的文本预处理。

---

## 八、延伸阅读

- [TRPL: Macros](https://doc.rust-lang.org/book/ch19-06-macros.html)
- [Rust Reference: Macros by Example](https://doc.rust-lang.org/reference/macros-by-example.html)
- [The Little Book of Rust Macros](https://veykril.github.io/tlborm/)
- [Rust Reference: Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html)
- [cppreference: C preprocessor](https://en.cppreference.com/w/c/preprocessor)
- [rustify.rs: Glossary — Macro hygiene](https://rustify.rs/glossary)
