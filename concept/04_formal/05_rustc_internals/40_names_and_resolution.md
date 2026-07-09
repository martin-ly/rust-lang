# 名称、作用域与解析（Names, Scopes and Resolution）

> **EN**: Names, Scopes and Resolution
> **Summary**: Rust 名称系统的权威概述：实体、声明、作用域、命名空间、路径、名称解析与可见性。 Authoritative overview of the Rust name system: entities, declarations, scopes, namespaces, paths, name resolution, and visibility.
>
> **受众**: [研究者]
> **内容分级**: [研究级]
> **Bloom 层级**: 理解 → 分析
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×Ana — 规范分析
> **前置依赖**: [Modules and Paths](../../01_foundation/07_modules_and_items/11_modules_and_paths.md) · [Attributes and Macros](../../01_foundation/09_macros_basics/12_attributes_and_macros.md)
> **后置概念**: [Name Resolution and HIR](35_name_resolution_and_hir.md) · [Linkage](../../03_advanced/04_ffi/27_linkage.md) · [Names Reference](51_names_reference.md)
> **定理链**: Entity → Declaration → Scope → Namespace → Path → Resolution
> **主要来源**: [Rust Reference — Names](https://doc.rust-lang.org/reference/names.html) · [rustc-dev-guide — Name Resolution](https://rustc-dev-guide.rust-lang.org/name-resolution.html) · [Pierce — Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/) · [Jung et al. — RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)

>
> **来源**: [Rust Reference — Names](https://doc.rust-lang.org/reference/names.html) · [Rust Reference — Namespaces](https://doc.rust-lang.org/reference/names/namespaces.html) · [Rust Reference — Scopes](https://doc.rust-lang.org/reference/names/scopes.html) · [Rust Reference — Paths](https://doc.rust-lang.org/reference/paths.html) · [Rust Reference — Name Resolution](https://doc.rust-lang.org/reference/names/name-resolution.html) · [Rust Reference — Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html)

---

---

## 认知路径

> **认知路径**: 本节从 "名称、作用域与解析（Names, Scopes and Resolution）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么名称、作用域与解析在 Rust 中值得关注？路径歧义、命名冲突、可见性错误和宏（Macro）展开顺序问题都直接源于名称解析规则。
2. **概念建立**: 掌握实体、声明、作用域、命名空间、路径和名称解析的核心定义与形式化记号。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与名称、作用域与解析的适用边界。
5. **迁移应用**: 将名称、作用域与解析与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "名称、作用域与解析在所有场景下都适用" ⟹ 不成立。`unsafe` 块、FFI 符号、过程宏（Procedural Macro）生成的名称可能绕过常规解析规则。

> **反命题 2**: "忽略名称、作用域与解析的细节也能写出正确代码" ⟹ 不成立。编译错误 E0425、E0433、E0603 等通常是名称解析或可见性规则被违反的直接信号。

> **反命题 3**: "其他语言对名称、作用域与解析的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的模块（Module）系统、命名空间分离和 `use` 重导出机制具有语言特有的形态。

## 一、实体与声明

**实体（entity）** 是源代码中可以被引用（Reference）的语言构造，例如类型、项（item）、泛型（Generics）参数、变量绑定、循环标签、生命周期（Lifetimes）、字段、属性和 lint。

**声明（declaration）** 是引入名称以引用（Reference）实体的语法构造。实体名称在**作用域（scope）**内有效，即源代码中可以引用该名称的区域。

### 显式声明的实体

- 项：模块（Module）（`mod`）、外部 crate（`extern crate`）、`use` 声明、函数与参数、类型别名、结构体（Struct）/联合体/枚举（Enum）及其字段、`const`/`static`、trait 及关联项、外部块项、`macro_rules`、实现关联项等。
- 表达式：闭包（Closures）参数、`while let`/`for`/`if let`/`match` 模式绑定、循环标签。
- 泛型（Generics）参数、高阶 trait bound、`let` 语句模式绑定。
- `macro_use` / `macro_export` 属性引入的宏（Macro）名称。

### 隐式声明的实体

- 语言 prelude：`bool`、`char`、`str`、整数类型、浮点类型、`usize`/`isize`。
- 内置属性、标准库 prelude 项/属性/宏、标准库 crate、外部链接 crate、工具属性、lint、derive 辅助属性。
- `'static` 生命周期（Lifetimes）。

### 形式化表示

```bnf
Declaration ::= ItemDecl | LetDecl | GenericParam | Label | UseDecl
ItemDecl    ::= ModDecl | ExternCrate | UseDecl | FnDecl
              | TypeAlias | StructDecl | EnumDecl | UnionDecl
              | ConstDecl | StaticDecl | TraitDecl | ImplDecl
              | ExternBlock | MacroRules
```

## 二、命名空间（Namespaces）

名称被划分到不同的**命名空间**，允许不同命名空间中的实体共享同一名称而不冲突。Rust 主要有：

| 命名空间 | 包含实体 | 示例冲突规则 |
|:---|:---|:---|
| 值命名空间（value namespace） | 函数、变量、`const`、`static`、关联函数 | 同一作用域不可重复 |
| 类型命名空间（type namespace） | 结构体（Struct）、枚举（Enum）、trait、类型别名、模块 | 可与值命名空间同名 |
| 宏命名空间（macro namespace） | `macro_rules!`、过程宏（Procedural Macro） | 通过 `name!()` 调用 |
| 生命周期命名空间（lifetime namespace） | 生命周期参数 `'a` | 独立解析 |

例如，可以同时定义一个名为 `Foo` 的模块和一个名为 `Foo` 的函数，因为它们处于不同命名空间：

```rust
mod Foo { pub const X: i32 = 1; }
fn Foo() {}

fn main() {
    let _ = Foo::X; // 类型/值命名空间
    Foo();          // 值命名空间
}
```

## 三、作用域（Scopes）

作用域是源代码区域，在该区域内某个名称可以被引用。Rust 中的作用域包括：

| 作用域类型 | 范围 | 典型示例 |
|:---|:---|:---|
| Crate 作用域 | 整个 crate | prelude 注入 |
| 模块作用域 | 模块体 | `mod foo { ... }` |
| 块作用域 | 块表达式 | `{ let x = 1; ... }` |
| 函数/闭包（Closures）体作用域 | 函数或闭包体 | `fn f() { ... }` |
| `match` 臂作用域 | 单个分支 | `1 => { ... }` |
| 循环体作用域 | 循环内部 | `loop { ... }` |
| `if let` / `while let` 条件作用域 | 条件与对应块 | `if let Some(x) = opt { ... }` |

作用域可以嵌套，内层作用域可以遮蔽（shadow）外层同名绑定。

## 四、路径（Paths）

**路径（path）** 用于引用实体，可能位于另一个模块或类型中。路径形式包括：

```bnf
Path          ::= SimplePath | QualifiedPath
SimplePath    ::= PathRoot? PathSegment ("::" PathSegment)*
PathRoot      ::= "crate" | "self" | "super" | "::"
PathSegment   ::= Identifier | "Self" | "super" | "self"
QualifiedPath ::= "<" Type ("as" TraitRef)? ">" "::" PathSegment
```

| 路径形式 | 语法 | 说明 |
|:---|:---|:---|
| 简单路径 | `foo`、`Foo` | 当前作用域查找 |
| 限定路径 | `crate::module::Item` | 从 crate 根开始 |
| 自我路径 | `self::foo`、`super::bar` | 当前/父模块 |
| 类型相关路径 | `<Type as Trait>::Assoc` | 关联项解析 |
| `Self` 路径 | `Self::Assoc` | 当前 impl 类型 |

生命周期和循环标签使用以单引号 `'` 开头的专用语法。

## 五、名称解析（Name Resolution）

**名称解析**是编译期将路径、标识符和标签绑定到实体声明的过程。解析规则包括：

- 从内到外搜索作用域链。
- 遵循命名空间隔离。
- 处理 `use` 声明引入的别名和重导出。
- 处理 prelude 注入的名称。

### 解析算法概要

```text
resolve(name, namespace, start_scope):
    for scope in chain(start_scope, root):
        if name in scope.namespace:
            candidate = scope.namespace[name]
            if is_visible(candidate, start_scope):
                return candidate
    if name in prelude.namespace:
        return prelude.namespace[name]
    error E0425 / E0433
```

名称解析失败会导致编译错误，如：

| 错误码 | 含义 |
|:---|:---|
| E0425 | 未解析的名称 |
| E0433 | 未解析的导入 |
| E0603 | 模块私有 |

## 六、可见性与隐私（Visibility and Privacy）

访问某些名称可能受到**可见性（visibility）**限制。Rust 的可见性修饰符包括：

| 修饰符 | 可见范围 |
|:---|:---|
| `pub` | 公开可见 |
| `pub(crate)` | 当前 crate 内可见 |
| `pub(super)` | 父模块可见 |
| `pub(in path)` | 指定路径内可见 |
| 默认 | 私有，仅当前模块及其子模块可见 |

可见性规则控制模块边界外的代码能否引用某名称。

## 七、`use` 声明与重导出

`use` 声明创建别名或重导出名称：

```rust
mod inner {
    pub fn helper() {}
}

pub use inner::helper as public_helper; // 重导出并改名
```

`use` 的解析受可见性和版本影响：2018 edition 后，`use crate::foo::bar` 从 crate 根开始，而 2015 edition 默认从当前模块开始。

## 八、关联概念

| 概念 | 关系 |
|:---|:---|
| [Modules and Paths](../../01_foundation/07_modules_and_items/11_modules_and_paths.md) | 模块系统是路径与可见性的基础 |
| [Preludes](../../01_foundation/07_modules_and_items/35_preludes.md) | prelude 注入隐式声明的名称 |
| [Name Resolution and HIR](35_name_resolution_and_hir.md) | 编译器内部名称解析与 HIR 表示 |
| [Linkage](../../03_advanced/04_ffi/27_linkage.md) | 名称解析影响链接器可见符号 |
| [Attributes and Macros](../../01_foundation/09_macros_basics/12_attributes_and_macros.md) | 宏展开可以引入新名称 |
| [Unsafe Rust](../../03_advanced/02_unsafe/03_unsafe.md) | `unsafe` 块中的外部符号解析有特殊规则 |

---

> **权威来源**: [Rust Reference — Names](https://doc.rust-lang.org/reference/names.html) · [Rust Reference — Namespaces](https://doc.rust-lang.org/reference/names/namespaces.html) · [Rust Reference — Scopes](https://doc.rust-lang.org/reference/names/scopes.html) · [Rust Reference — Paths](https://doc.rust-lang.org/reference/paths.html) · [Rust Reference — Name Resolution](https://doc.rust-lang.org/reference/names/name-resolution.html) · [Rust Reference — Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html) · [rustc-dev-guide — Name Resolution](https://rustc-dev-guide.rust-lang.org/name-resolution.html)
> **内容分级**: [研究级]

## 过渡段

> **过渡**: 从实体与声明过渡到作用域与命名空间，可以理解 Rust 如何在同一 crate 内区分不同种类的名称。
>
> **过渡**: 从作用域规则过渡到路径与解析算法，可以建立“名字如何被找到”的系统性理解。
>
> **过渡**: 从名称解析过渡到 HIR 与链接，可以理解前端语义分析如何为后续编译阶段提供基础。
>
