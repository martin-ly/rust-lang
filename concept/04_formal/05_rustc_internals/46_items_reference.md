# 条目参考（Items Reference）

> **EN**: Items Reference
> **Summary**: Rust 语言中所有 item 种类的规范定义：模块（Module）、extern crate、use 声明、函数、类型别名、结构体（Struct）、枚举（Enum）、联合体、常量、静态项、trait、实现、外部块、泛型（Generics）参数与关联项。
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Crates and Source Files](../../01_foundation/07_modules_and_items/38_crates_and_source_files.md) · [Modules and Paths](../../01_foundation/07_modules_and_items/11_modules_and_paths.md) · [Visibility and Privacy](../../03_advanced/06_low_level_patterns/34_visibility_and_privacy.md)
> **后置概念**: [Attributes](47_attributes.md) · [Generics](../../02_intermediate/01_generics/02_generics.md) · [Traits](../../02_intermediate/00_traits/01_traits.md)
> **定理链**: Crate → Module → Item → Declaration
>
> **来源**: [Rust Reference — Items](https://doc.rust-lang.org/reference/items.html) · [Aho, Sethi & Ullman — Compilers: Principles, Techniques, and Tools](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

---

---

## 认知路径

> **认知路径**: 本节从 "条目参考（Items Reference）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 条目参考（Items Reference） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 条目参考（Items Reference） 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与条目参考（Items Reference）的适用边界。
5. **迁移应用**: 将 条目参考（Items Reference） 与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "条目参考（Items Reference） 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 条目参考（Items Reference） 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 条目参考（Items Reference） 规则被违反的直接信号。

> **反命题 3**: "其他语言对 条目参考（Items Reference） 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 条目参考（Items Reference） 具有语言特有的形态。

## 一、Item 概述

**Item（条目）** 是 Rust 模块（Module）中的声明单元，构成 crate 的静态结构。每个 item 都有名称、可见性和作用域。

主要 item 类别：

| Item | 声明关键字 | 说明 |
|:---|:---|:---|
| 模块（Module） | `mod` | 命名空间容器 |
| Extern crate | `extern crate` | 引入外部 crate（2018 edition 后多数场景隐式） |
| Use 声明 | `use` | 名称重绑定与重导出 |
| 函数 | `fn` | 可调用代码单元 |
| 类型别名 | `type` | 现有类型的同义名 |
| 结构体（Struct） | `struct` | 命名字段复合类型 |
| 枚举（Enum） | `enum` | 带变体的代数数据类型 |
| 联合体 | `union` | 类似 C union 的内存共享类型 |
| 常量 | `const` | 编译期常量 |
| 静态项 | `static` | 全局生命周期（Lifetimes）变量 |
| Trait | `trait` | 抽象接口 |
| 实现 | `impl` | trait 实现或固有实现 |
| 外部块 | `extern` | FFI 声明块 |
| 泛型（Generics）参数 | `<T>` | 类型/生命周期（Lifetimes）/const 参数 |
| 关联项 | `type` / `const` / `fn` | trait/impl 内部的从属 item |

## 二、模块与路径

模块（Module）通过 `mod name { ... }` 声明，可嵌套。`pub use` 可重导出外部名称，改变名称在模块树中的可见路径。

```rust
mod inner {
    pub fn helper() {}
}

pub use inner::helper;
```

## 三、泛型参数

泛型（Generics）参数分为三类：

| 参数 | 示例 | 约束位置 |
|:---|:---|:---|
| 类型参数 | `T` | `T: Trait` |
| 生命周期（Lifetimes）参数 | `'a` | `'a: 'b` |
| const 泛型（Generics） | `const N: usize` | 类型签名中 |

## 四、关联项

Trait 和 impl 块内部可声明：

- **关联类型** `type Output;`
- **关联常量** `const MAX: usize;`
- **关联函数** `fn method();`

关联项通过 `T::Assoc` 或 `<T as Trait>::Assoc` 访问。

## 五、外部块与 ABI

```rust
extern "C" {
    fn c_function(x: i32) -> i32;
}
```

外部块声明由其他语言或外部 crate 提供的符号，调用处必须在 `unsafe` 块中。

## 六、与属性的关系

几乎所有 item 都可接受属性，如 `#[derive(...)]`、`#[repr(...)]`、`#[cfg(...)]`。详见 [Attributes](47_attributes.md)。

---

> **权威来源**: [Rust Reference — Items](https://doc.rust-lang.org/reference/items.html) · [Rust Reference — Modules](https://doc.rust-lang.org/reference/items/modules.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)
> **内容分级**: [研究级]
