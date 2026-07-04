# 属性（Attributes）

> **EN**: Attributes
> **Summary**: Rust 属性系统：内置属性分类（测试、derive、诊断、代码生成、限制、类型系统（Type System）、调试器）及其在 item、表达式、语句上的应用规则。 Rust attribute system: built-in attribute categories and application rules on items, expressions, and statements.
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×App — 规范应用
> **前置依赖**: [Items Reference](46_items_reference.md) · [Macros](../03_advanced/04_macros.md)
> **后置概念**: [Conditional Compilation](../03_advanced/28_conditional_compilation.md) · [Derive Traits](../02_intermediate/00_traits/31_derive_traits.md)
> **定理链**: Attribute → Metadata → Compiler Behavior
>
> **来源**: [Rust Reference — Attributes](https://doc.rust-lang.org/reference/attributes.html) · [Aho, Sethi & Ullman — Compilers: Principles, Techniques, and Tools](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

---


---

## 认知路径

> **认知路径**: 本节从 "属性（Attributes）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 属性（Attributes） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 属性（Attributes） 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与属性（Attributes）的适用边界。
5. **迁移应用**: 将 属性（Attributes） 与前置/后置概念链接，形成跨层知识网络。


---

## 反命题决策树

> **反命题 1**: "属性（Attributes） 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 属性（Attributes） 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 属性（Attributes） 规则被违反的直接信号。

> **反命题 3**: "其他语言对 属性（Attributes） 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 属性（Attributes） 具有语言特有的形态。


## 一、属性语法

属性以 `#[...]`（外层属性）或 `#![...]`（内层属性）形式出现：

- 外层属性作用于其后的 item。
- 内层属性作用于包含它的 item 或 crate。

```rust
#![allow(dead_code)] // 内层：作用于当前模块/crate

#[derive(Debug)]     // 外层：作用于结构体
struct Point { x: i32, y: i32 }
```

## 二、属性分类

| 类别 | 主要属性 | 作用 |
|:---|:---|:---|
| 测试 | `#[test]`, `#[bench]`, `#[should_panic]` | 标记测试函数 |
| Derive | `#[derive(Trait)]` | 自动生成 trait 实现 |
| 诊断 | `#[allow]`, `#[warn]`, `#[deny]`, `#[forbid]`, `#[deprecated]` | 控制 lint 与弃用 |
| 代码生成 | `#[inline]`, `#[cold]`, `#[no_mangle]`, `#[repr(...)]` | 影响代码生成 |
| 限制 | `#[allow(...)]`, `#[feature(...)]`（nightly） | 能力开关 |
| 类型系统（Type System） | `#[non_exhaustive]`, `#[must_use]` | 影响类型/接口语义 |
| 调试器 | `#[debugger_visualizer]` | 调试器可视化 |

## 三、条件编译属性

`#[cfg(...)]` 与 `cfg_attr(...)` 在编译期决定是否包含代码或属性。

```rust
#[cfg(target_os = "linux")]
fn linux_only() {}

#[cfg_attr(feature = "serde", derive(serde::Serialize))]
struct Data;
```

详见 [Conditional Compilation](../03_advanced/28_conditional_compilation.md)。

## 四、文档注释

文档注释 `///` 与 `//!` 本质上是 `#[doc = "..."]` 属性的语法糖。

```rust
/// A point in 2D space.
struct Point;
```

等价于：

```rust
#[doc = " A point in 2D space."]
struct Point;
```

## 五、与宏的关系

过程宏（procedural macro）和声明宏（Declarative Macro）（`macro_rules!`）都可生成属性。属性宏在宏展开阶段执行，可读取或替换被装饰的 item。

---

> **权威来源**: [Rust Reference — Attributes](https://doc.rust-lang.org/reference/attributes.html) · [Rust Reference — Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)
> **内容分级**: [研究级]
