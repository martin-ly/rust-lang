# 名字参考（Names Reference）

> **EN**: Names Reference
> **Summary**: Rust 名字系统的规范：命名空间、作用域、prelude、路径、名字解析规则，以及可见性如何与命名空间交互。 Normative description of Rust names: namespaces, scopes, prelude, paths, resolution rules, and visibility interaction.
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Modules and Paths](../01_foundation/11_modules_and_paths.md) · [Names and Resolution](40_names_and_resolution.md) · [Visibility and Privacy](../03_advanced/34_visibility_and_privacy.md)
> **后置概念**: [Items Reference](46_items_reference.md) · [Patterns Reference](49_patterns_reference.md)
> **定理链**: Source File → Module Tree → Namespace → Scope → Name Resolution
>
> **来源**: [Rust Reference — Names](https://doc.rust-lang.org/reference/names.html) · [Aho, Sethi & Ullman — Compilers: Principles, Techniques, and Tools](https://en.wikipedia.org/wiki/Compilers:_Principles,_Techniques,_and_Tools) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

---

## 一、命名空间

Rust 将名字分为多个命名空间：

| 命名空间 | 包含 |
|:---|:---|
| 类型命名空间 | `struct`, `enum`, `union`, `trait`, `type`, `mod` |
| 值命名空间 | `fn`, `const`, `static`, 绑定，关联函数 |
| 宏命名空间 | `macro_rules!`, 过程宏 |
| 生命周期命名空间 | 生命周期参数 `'a` |

同一作用域内，不同类型空间的名字可以同名；同一空间内不可重复。

## 二、作用域

作用域决定名字在何处可见：

| 作用域类型 | 说明 |
|:---|:---|
| 模块作用域 | 整个模块可见 |
| 块作用域 | 仅在 `{}` 内可见 |
| 函数参数作用域 | 函数体可见 |
| 模式作用域 | `match` 分支或 `let` 绑定后可见 |
| 实现作用域 | `impl` 块内可见 |

## 三、Prelude

Prelude 是自动导入的名字集合：

- `std::prelude::rust_2024`
- 包含 `Option`, `Result`, `Vec`, `String`, `Drop`, `Copy` 等核心 trait 和类型。

详见 [Preludes](../01_foundation/35_preludes.md)。

## 四、路径

路径用于定位名字：

| 路径形式 | 示例 | 说明 |
|:---|:---|:---|
| 相对路径 | `foo::bar` | 从当前模块开始 |
| 绝对路径 | `::crate::foo::bar` | 从 crate 根开始 |
| 自我路径 | `self::foo`, `super::bar` | 当前模块 / 父模块 |
| `Self` 路径 | `Self::Assoc` | 当前实现类型 |
| `crate` 路径 | `crate::foo` | 2018+ edition 的 crate 根 |

## 五、名字解析过程

1. 根据路径前缀确定搜索起点。
2. 在对应命名空间中逐级查找。
3. 应用可见性规则过滤私有项。
4. 处理 `use` 重导出和 `pub use` 的别名。

## 六、与可见性的交互

可见性规则决定名字是否能被特定路径访问。公共项（`pub`）可被外部访问；私有项默认仅对当前模块及子模块可见。

详见 [Visibility and Privacy](../03_advanced/34_visibility_and_privacy.md)。

---

> **权威来源**: [Rust Reference — Names](https://doc.rust-lang.org/reference/names.html) · [Rust Reference — Namespaces and Scopes](https://doc.rust-lang.org/reference/names/namespaces.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/)
> **内容分级**: [研究级]
