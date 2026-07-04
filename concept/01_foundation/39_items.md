# 项（Items）

> **EN**: Items
> **Summary**: Rust crate 的组成单元：模块（Module）、`use` 声明、函数、类型定义、常量、static、trait、实现、`extern` 块等项的分类与作用域规则。
>
> **受众**: [初学者]
> **内容分级**: [综述级]
> **Bloom 层级**: 理解 → 应用
> **A/S/P 标记**: **S** — Specification
> **双维定位**: S×App — 规范应用
> **前置依赖**: [Modules and Paths](11_modules_and_paths.md) · [Crates and Source Files](38_crates_and_source_files.md)
> **后置概念**: [Traits](../02_intermediate/01_traits.md) · [Generics](../02_intermediate/02_generics.md) · [Unsafe Rust](../03_advanced/03_unsafe.md) · [Linkage](../03_advanced/27_linkage.md)
> **定理链**: Crate → Module → Item → Scope
> **主要来源**: [Rust Reference — Items](https://doc.rust-lang.org/reference/items.html) · [TRPL — Packages and Crates](https://doc.rust-lang.org/book/ch07-01-packages-and-crates.html) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Brown Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)

>
> **来源**: [Rust Reference — Items](https://doc.rust-lang.org/reference/items.html)

---


> **跨层回溯**: [学习方法论](../00_meta/methodology.md) · [术语表](../00_meta/terminology_glossary.md)

---

## 认知路径

> **认知路径**: 本节从 "项（Items）" 的核心问题出发，依次建立直观理解、形式化模型与工程实践之间的联系。

1. **问题识别**: 为什么 项（Items） 在 Rust 中值得关注？它与日常编程中的哪些痛点相关？
2. **概念建立**: 掌握 项（Items） 的核心定义、关键术语与类型系统（Type System）/运行时（Runtime）边界。
3. **机制推理**: 通过 ⟹ 定理链将语法规则、编译期检查与运行时（Runtime）语义串联起来。
4. **边界辨析**: 借助反命题/反例理解常见错误与项（Items）的适用边界。
5. **迁移应用**: 将 项（Items） 与前置/后置概念链接，形成跨层知识网络。


---

## 反命题决策树

> **反命题 1**: "项（Items） 在所有场景下都适用" ⟹ 不成立。存在特定的边界条件（如 `unsafe`、FFI、递归类型）会使常规推理失效。

> **反命题 2**: "忽略 项（Items） 的细节也能写出正确代码" ⟹ 不成立。编译错误通常是 项（Items） 规则被违反的直接信号。

> **反命题 3**: "其他语言对 项（Items） 的处理方式可以直接迁移到 Rust" ⟹ 不成立。Rust 的所有权（Ownership）和借用（Borrowing）约束使 项（Items） 具有语言特有的形态。


## 一、什么是 Item

**项（item）** 是 crate 的组成部分。项通过嵌套的模块集合在 crate 中组织。每个 crate 都有一个最外层的匿名模块；crate 中的所有其他项都位于该 crate 模块树的路径中。

项的特性：

- 完全在编译期确定。
- 执行期间通常保持不变。
- 可能驻留在只读内存中。

---

## 二、Item 的种类

Rust 中的 item 包括：

| 类别 | 说明 |
|:---|:---|
| Modules | 模块声明，组织代码命名空间 |
| `extern crate` declarations | 外部 crate 声明 |
| `use` declarations | 引入或重导出名称 |
| Function definitions | 函数定义 |
| Type alias definitions | 类型别名 |
| Struct definitions | 结构体定义 |
| Enumeration definitions | 枚举（Enum）定义 |
| Union definitions | 联合体定义 |
| Constant items | `const` 常量 |
| Static items | `static` 静态项 |
| Trait definitions | trait 定义 |
| Implementations | `impl` 实现块 |
| `extern` blocks | 外部函数声明块 |

---

## 三、Item 的声明位置

Item 可以声明在：

- crate 根（crate root）
- 模块内部
- 块表达式（block expression）内部

---

## 四、关联项与外部项

### 关联项（Associated items）

- 可以声明在 **trait** 和 **实现（implementations）** 内部的项子集。
- 包括关联函数、关联类型、关联常量。

参见 [Traits](../02_intermediate/01_traits.md) 与 [Advanced Traits](../02_intermediate/19_advanced_traits.md)。

### 外部项（External items）

- 可以声明在 **`extern` 块** 内部的项子集。
- 用于声明来自其他语言（通常是 C）的函数和变量。

参见 [FFI](../03_advanced/05_rust_ffi.md) 与 [FFI Advanced](../03_advanced/09_ffi_advanced.md)。

---

## 五、Item 的顺序

Item 可以按任意顺序定义，但 **`macro_rules`** 具有自己独立的作用域行为。

名称解析允许 item 在模块或块中先于或后于其被引用（Reference）的位置定义。

---

## 六、关联概念

| 概念 | 关系 |
|:---|:---|
| [Modules and Paths](11_modules_and_paths.md) | item 通过模块树组织 |
| [Crates and Source Files](38_crates_and_source_files.md) | crate 由 item 组成 |
| [Traits](../02_intermediate/01_traits.md) | trait 定义与实现是 item 的重要类别 |
| [Unsafe Rust](../03_advanced/03_unsafe.md) | `extern` 块、`unsafe` trait 等属于 unsafe 相关 item |
| [Linkage](../03_advanced/27_linkage.md) | item 的可见性影响链接器符号 |
