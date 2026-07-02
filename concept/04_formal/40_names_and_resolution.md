# 名称、作用域与解析（Names, Scopes and Resolution）

> **EN**: Names, Scopes and Resolution
> **Summary**: Rust 名称系统的权威概述：实体、声明、作用域、命名空间、路径、名称解析与可见性规则。
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Modules and Paths](../01_foundation/11_modules_and_paths.md) · [Attributes and Macros](../01_foundation/12_attributes_and_macros.md)
> **后置概念**: [Name Resolution and HIR](35_name_resolution_and_hir.md) · [Linkage](../03_advanced/27_linkage.md) · [Visibility and Privacy](../05_comparative/04_safety_boundaries.md)
> **定理链**: Entity → Declaration → Scope → Namespace → Path → Resolution
> **主要来源**: [Rust Reference — Names](https://doc.rust-lang.org/reference/names.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)

>
> **来源**: [Rust Reference — Names](https://doc.rust-lang.org/reference/names.html) · [Rust Reference — Namespaces](https://doc.rust-lang.org/reference/namespaces.html) · [Rust Reference — Scopes](https://doc.rust-lang.org/reference/scopes.html) · [Rust Reference — Paths](https://doc.rust-lang.org/reference/paths.html) · [Rust Reference — Name Resolution](https://doc.rust-lang.org/reference/name-resolution.html) · [Rust Reference — Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html)

---

## 一、实体与声明

**实体（entity）** 是源代码中可以被引用的语言构造，例如类型、项（item）、泛型参数、变量绑定、循环标签、生命周期、字段、属性和 lint。

**声明（declaration）** 是引入名称以引用实体的语法构造。实体名称在**作用域（scope）**内有效，即源代码中可以引用该名称的区域。

### 显式声明的实体

- 项：模块、外部 crate、`use` 声明、函数与参数、类型别名、结构体/联合体/枚举及其字段、`const`/`static`、trait 及关联项、外部块项、`macro_rules`、实现关联项等。
- 表达式：闭包参数、`while let`/`for`/`if let`/`match` 模式绑定、循环标签。
- 泛型参数、高阶 trait bound、`let` 语句模式绑定。
- `macro_use` / `macro_export` 属性引入的宏名称。

### 隐式声明的实体

- 语言 prelude：`bool`、`char`、`str`、整数类型、浮点类型、`usize`/`isize`。
- 内置属性、标准库 prelude 项/属性/宏、标准库 crate、外部链接 crate、工具属性、lint、derive 辅助属性。
- `'static` 生命周期。

---

## 二、命名空间（Namespaces）

名称被划分到不同的**命名空间**，允许不同命名空间中的实体共享同一名称而不冲突。Rust 主要有：

- 值命名空间（value namespace）
- 类型命名空间（type namespace）
- 宏命名空间（macro namespace）
- 生命周期命名空间（lifetime namespace）

例如，可以同时定义一个名为 `Foo` 的模块和一个名为 `Foo` 的函数，因为它们处于不同命名空间。

---

## 三、作用域（Scopes）

作用域是源代码区域，在该区域内某个名称可以被引用。Rust 中的作用域包括：

- 整个 crate
- 模块体
- 块表达式
- 函数/闭包体
- `match` 臂
- 循环体
- `if let` / `while let` 条件绑定的作用域

作用域可以嵌套，内层作用域可以遮蔽（shadow）外层同名绑定。

---

## 四、路径（Paths）

**路径（path）** 用于引用实体，可能位于另一个模块或类型中。路径形式包括：

- 简单路径：`foo`、`Foo`
- 限定路径：`crate::module::Item`、`self::foo`、`super::bar`
- 类型相关路径：`<Type as Trait>::Assoc`

生命周期和循环标签使用以单引号 `'` 开头的专用语法。

---

## 五、名称解析（Name Resolution）

**名称解析**是编译期将路径、标识符和标签绑定到实体声明的过程。解析规则包括：

- 从内到外搜索作用域链。
- 遵循命名空间隔离。
- 处理 `use` 声明引入的别名和重导出。
- 处理 prelude 注入的名称。

名称解析失败会导致编译错误。

---

## 六、可见性与隐私（Visibility and Privacy）

访问某些名称可能受到**可见性（visibility）**限制。Rust 的可见性修饰符包括：

- `pub`：公开可见
- `pub(crate)`：当前 crate 内可见
- `pub(super)`：父模块可见
- `pub(in path)`：指定路径内可见
- 默认：私有，仅当前模块及其子模块可见

可见性规则控制模块边界外的代码能否引用某名称。

---

## 七、关联概念

| 概念 | 关系 |
|:---|:---|
| [Modules and Paths](../01_foundation/11_modules_and_paths.md) | 模块系统是路径与可见性的基础 |
| [Preludes](../01_foundation/35_preludes.md) | prelude 注入隐式声明的名称 |
| [Name Resolution and HIR](35_name_resolution_and_hir.md) | 编译器内部名称解析与 HIR 表示 |
| [Linkage](../03_advanced/27_linkage.md) | 名称解析影响链接器可见符号 |
| [Attributes and Macros](../01_foundation/12_attributes_and_macros.md) | 宏展开可以引入新名称 |
