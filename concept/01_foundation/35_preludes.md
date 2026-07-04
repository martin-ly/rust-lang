> **内容分级**: [综述级]
>
# Preludes（预导入模块）

> **EN**: Preludes
> **Summary**: Rust 中自动进入每个模块（Module）作用域的名字集合：标准库 prelude、extern prelude、language prelude、macro_use prelude 与 tool prelude。
>
> **受众**: [初学者] / [进阶]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S** — Specification / Language semantics
> **双维定位**: S×Lang — 语言名称解析机制
> **前置依赖**: [Modules and Paths](11_modules_and_paths.md) · [Attributes and Macros](12_attributes_and_macros.md) · [Terminology Glossary](../00_meta/terminology_glossary.md)
> **后置概念**: [Unsafe Rust](../03_advanced/03_unsafe.md) · [Linkage](../03_advanced/27_linkage.md)
> **定理链**: N/A — 语言规范/综述性文档
> **主要来源**: [Rust Reference — Preludes](https://doc.rust-lang.org/reference/names/preludes.html) · [Kohlbecker et al. — Hygienic Macro Expansion](https://doi.org/10.1145/41625.41632) · [Flatt — Binding as Sets of Scopes](https://doi.org/10.1145/2814304.2814305) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [TRPL — Packages and Crates](https://doc.rust-lang.org/book/ch07-01-packages-and-crates.html) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/)

>
> **来源**: [Rust Reference — Preludes](https://doc.rust-lang.org/reference/names/preludes.html) · [Rust Reference — `no_std`](https://doc.rust-lang.org/reference/names/preludes.html#the-no_std-attribute) · [Rust Reference — `no_implicit_prelude`](https://doc.rust-lang.org/reference/names/preludes.html#the-no_implicit_prelude-attribute)

---

---

---

> **过渡**: 从 Preludes（预导入模块（Module）） 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 Preludes（预导入模块（Module）） 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 Preludes（预导入模块） 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **反向推理 1**: 如果程序在 Preludes（预导入模块） 相关代码处出现编译错误 ⟸ 应首先检查所有权（Ownership）、生命周期（Lifetimes）或类型约束是否被违反。
>
> **反向推理 2**: 如果某段代码在运行时（Runtime）表现出非预期行为且与 Preludes（预导入模块） 有关 ⟸ 应回溯到其形式化语义或安全边界假设，定位隐式契约。

## 认知路径

> **认知路径**: 本节从 "Preludes（预导入模块）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 Preludes（预导入模块） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 Preludes（预导入模块） 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与Preludes（预导入模块）的适用边界。
5. **迁移应用**: 将 Preludes（预导入模块） 与前置/后置概念链接，形成跨层知识网络。

---

## 反命题决策树

> **反命题 1**: "Preludes（预导入模块） 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 Preludes（预导入模块） 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 Preludes（预导入模块） 规则被违反的直接信号。

> **反命题 3**: "其他语言对 Preludes（预导入模块） 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 Preludes（预导入模块） 具有语言特有的形态。

## 一、什么是 Prelude

**Prelude** 是一组在每个 crate 的每个模块中**自动进入作用域**的名字。它们不是当前模块的成员，因此在名称解析时被隐式查询，但不能通过 `self::Box` 这类路径引用（Reference）。

> **关键性质**
>
> - Prelude 名字在模块作用域中可见。
> - Prelude 名字**不是**模块成员，因此不能通过 `self::` 引用（Reference）。
> - 存在多种 prelude，分别由语言、标准库、外部 crate、宏（Macro）和工具提供。

---

## 二、标准库 Prelude（Standard library prelude）

每个 crate 都有一个标准库 prelude，内容由单个标准库模块决定：

| 条件 | 使用的模块 |
|:---|:---|
| 默认（Edition 2018+，无 `no_std`） | `std::prelude::rust_YYYY`（YYYY 为当前 Edition） |
| 使用 `#![no_std]` | `core::prelude::rust_YYYY` |

### `#![no_std]` 属性

- `#![no_std]` 阻止 `std` crate 被自动链接，并将标准库 prelude 切换为 `core` prelude。
- `#![no_std]` **只能**用于 crate root。
- `#![no_std]` 不阻止通过 `extern crate std` 手动引入 `std`。

```rust
#![no_std]

// 此时 Box、Vec 等不在 prelude 中，但 core 中的类型仍可用
use core::cell::RefCell;
```

> **常见用途**：嵌入式目标、操作系统内核、WASM 裸目标等不支持或不希望使用标准库的场景。

---

## 三、外部 Prelude（Extern prelude）

通过以下方式引入的外部 crate 会进入 **extern prelude**：

- `extern crate foo;`（根模块中）
- 编译器参数 `--extern foo=...`（Cargo 默认会为依赖 crate 传入）
- 使用别名时：`extern crate orig as new` 会将 `new` 加入 extern prelude

### 默认行为

- `core` crate 始终在外部 prelude 中。
- 只要未指定 `#![no_std]`，`std` crate 也会加入外部 prelude。

### Edition 差异

- **2015 Edition**：外部 prelude 中的 crate 不能通过 `use` 引用（Reference），通常需要显式 `extern crate`。
- **2018 Edition+**：`use foo::bar;` 可以直接引用外部 prelude 中的 crate，`extern crate` 被视为非惯用写法。

> **注意**：`alloc`、`test` 等随 `rustc` 一起发布的 crate 不会自动进入外部 prelude（即使 2018+），需要显式 `extern crate alloc;`。

---

## 四、语言 Prelude（Language prelude）

语言 prelude 中的名字由语言内置，**始终**在作用域中，且不受 `#![no_implicit_prelude]` 影响。

### 类型命名空间

- 布尔类型：`bool`
- 字符类型：`char`
- 字符串切片（String Slice）类型：`str`
- 有符号整数：`i8`, `i16`, `i32`, `i64`, `i128`
- 无符号整数：`u8`, `u16`, `u32`, `u64`, `u128`
- 机器相关整数：`isize`, `usize`
- 浮点类型：`f32`, `f64`

### 宏命名空间

- 内建属性（built-in attributes）
- 内建派生宏（built-in derive macros）

---

## 五、`macro_use` Prelude

`macro_use` prelude 包含通过 `#[macro_use] extern crate foo;` 从外部 crate 导入的宏（Macro）。

```rust
#[macro_use]
extern crate serde;

// serde 中的宏现在在当前 crate 的所有模块中可用
```

---

## 六、工具 Prelude（Tool prelude）

工具 prelude 在类型命名空间中包含**外部工具名**，主要用于工具属性（tool attributes），例如 `rustfmt`、`clippy` 等。

```rust
#![allow(clippy::needless_return)]
```

---

## 七、`no_implicit_prelude` 属性

`no_implicit_prelude` 用于阻止隐式 prelude 进入作用域。

### 作用范围

- 应用于 crate root：影响整个 crate。
- 应用于模块：影响该模块及其后代模块。

### 阻止的 prelude

- 标准库 prelude
- 外部 prelude
- `macro_use` prelude
- 工具 prelude

### 不阻止的 prelude

- **语言 prelude** 始终保留。

### Edition 差异

- **2015 Edition**：`no_implicit_prelude` 不阻止 `macro_use` prelude，标准库导出的宏（Macro）仍然可用。
- **2018 Edition+**：`no_implicit_prelude` 也会移除 `macro_use` prelude。

```rust
#![no_implicit_prelude]

mod example {
    // 本模块及其子模块中没有 std/extern/macro_use/tool prelude
    // 但 bool、i32 等语言内置类型仍然可用
}
```

---

## 八、实践建议

1. **大多数代码不需要关注 prelude**：日常 Rust 代码依赖 `std::prelude` 自动导入的常用类型（`Option`、`Result`、`Vec`、`String` 等）。
2. **使用 `#![no_std]` 时记得 `extern crate alloc`**：如果需要 `Box`、`Vec`、`Rc`、`Arc` 等堆分配类型，必须显式引入 `alloc`。
3. **库 crate 谨慎使用 `no_implicit_prelude`**：它会使代码变得冗长，通常只在特定宏生成或教学场景中使用。
4. **2018 Edition+ 优先用 `use crate_name::item;`**：避免不必要的 `extern crate` 声明。

---

## 九、与其他概念的关联

| 概念 | 关系 |
|:---|:---|
| [Modules and Paths](11_modules_and_paths.md) | prelude 决定哪些名字在模块作用域中默认可见 |
| [Attributes and Macros](12_attributes_and_macros.md) | `#[macro_use]` 和工具属性与 macro_use/tool prelude 相关 |
| [Unsafe Rust](../03_advanced/03_unsafe.md) | `#![no_std]` 常与裸机/unsafe 代码一起使用 |
| [Linkage](../03_advanced/27_linkage.md) | `extern crate` 和 `--extern` 影响外部 prelude 和链接行为 |
