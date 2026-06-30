# Rust 模块系统规范 {#rust-模块系统规范}

> **概念族**: 形式化模块

> **内容分级**: [归档级]

>

> **分级**: [B]

> **Bloom 层级**: L5-L6 (分析/评价/创造)

> **创建日期**: 2026-06-29

> **最后更新**: 2026-06-29

> **Rust 版本**: 1.96.0+ (Edition 2024)

> **状态**: ✅ 新建完成 / 权威国际化来源对齐完成

---

## 目录 {#目录}

- [Rust 模块系统规范](#rust-模块系统规范)
  - [目录](#目录)
  - [研究目标](#研究目标)
  - [概念定义](#概念定义)
  - [属性关系](#属性关系)
  - [解释与论证](#解释与论证)
    - [模块树为何是树而非 DAG](#模块树为何是树而非-dag)
    - [`pub(in path)` 的形式化语义](#pubin-path-的形式化语义)
    - [`pub use` 的封装意义](#pub-use-的封装意义)
  - [Rust 示例](#rust-示例)
    - [1. 基本模块结构](#1-基本模块结构)
    - [2. 使用 `pub(in path)`](#2-使用-pubin-path)
    - [3. `pub use` 重导出](#3-pub-use-重导出)
  - [反例与边界](#反例与边界)
  - [权威来源对照表](#权威来源对照表)
  - [学术/社区来源参考](#学术社区来源参考)

---

## 研究目标 {#研究目标}

精确梳理 Rust 模块系统的静态结构规则，建立 crate、module、path、use 与 visibility 五要素之间的可推导关系，为名称解析、可见性检查和形式化封装边界提供基础定义。

---

## 概念定义 {#概念定义}

| 术语 | 定义 |

| :--- | :--- |

| **Crate** | Rust 编译器一次独立编译的产物单元，分为二进制 crate（`bin`）与库 crate（`lib`）。每个 crate 拥有自己的 crate root 与全局唯一的 crate 名称空间。 |

| **Module** | crate 内部的命名空间容器，用于组织 items（`fn`、`struct`、`trait` 等）。可通过文件系统目录（`mod.rs` 或 `module_name.rs`）或内联 `mod name { ... }` 声明创建。 |

| **Path** | 访问 item 的限定名称，形式包括相对路径 `self::`、`super::`、`crate::`，以及绝对路径通过 `::crate_name` 引用外部 crate。 |

| **Use** | 通过 `use` 将路径绑定到当前作用域的别名，实现名称引入与重导出（`pub use`）。 |

| **Visibility** | item 的可见范围，`pub` / `pub(crate)` / `pub(super)` / `pub(in path)` 分别表示公开、crate 内、父模块内、指定路径内可见。 |

> **来源:** [Rust Reference – Items and Modules](https://doc.rust-lang.org/reference/items/modules.html)

>

> **来源:** [Rust Reference – Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html)

>

> **来源:** [The Rust Programming Language – Packages, Crates, and Modules](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html)

---

## 属性关系 {#属性关系}

```text

Crate

├── Crate Root (src/main.rs 或 src/lib.rs)

│   └── 形成隐式根模块 "crate"

├── Module Tree

│   ├── 内联模块: mod name { items }

│   ├── 文件模块: src/name.rs

│   └── 目录模块: src/name/mod.rs

├── Visibility Lattice

│   ├── pub               → 无限制

│   ├── pub(crate)        → 当前 crate

│   ├── pub(super)        → 父模块

│   └── pub(in path)      → path 所限定的祖先模块

└── Use Tree

    ├── use path::item    → 私有引入

    └── pub use path::item → 重导出（改变可见性入口）

```

**关键关系：**

1. **可见性是偏序关系**：`pub` ⊇ `pub(crate)` ⊇ `pub(super)` ⊇ `pub(in path)` ⊇ 默认私有。越靠近 crate root，`pub(in path)` 的实际范围越大。

2. **use 不改变定义位置，只改变引用名称**：`use` 引入的是 item 的别名入口，真正的可见性仍由原 item 的 visibility 决定；`pub use` 只是把入口提升到新的作用域。

3. **路径解析受可见性约束**：即使路径在语法上存在，若目标 item 对当前模块不可见，则产生 `E0603`（private）错误。

> **来源:** [Rust Reference – Use Declarations](https://doc.rust-lang.org/reference/items/use-declarations.html)

---

## 解释与论证 {#解释与论证}

### 模块树为何是树而非 DAG {#模块树为何是树而非-dag}

Rust 的模块层级严格由 `mod` 声明与文件系统共同决定，一个子模块只能有一个父模块。`use` 和 `pub use` 虽然可以在不同分支创建别名引用，但 **模块的父子关系仍是树形**，这保证了名称解析的确定性和可见性检查的单向传播。

### `pub(in path)` 的形式化语义 {#pubin-path-的形式化语义}

`pub(in path)` 表示 item 对 `path` 所指向的模块及其所有后代模块可见。这里的 `path` 必须是当前模块的祖先模块（ancestor），否则编译器报错。它本质上是把可见性上限锁定到某个祖先节点，形成一种“受限公开”。

### `pub use` 的封装意义 {#pub-use-的封装意义}

`pub use` 允许内部模块结构对外隐藏，同时把稳定 API 暴露到 crate root 或任意公共模块。这是 Rust 中“门面模式（facade）”的核心机制，使得内部重构不影响外部 API。

> **来源:** [Rust API Guidelines – Re-export types used in public API](https://rust-lang.github.io/api-guidelines/naming.html)

---

## Rust 示例 {#rust-示例}

### 1. 基本模块结构 {#1-基本模块结构}

```rust

// src/lib.rs

pub mod outer {

    pub mod inner {

        pub fn public_fn() {}

        fn private_fn() {} // 默认仅 inner 内可见

    }



    pub(crate) fn crate_visible_fn() {}

    pub(super) fn parent_visible_fn() {}

}

```

### 2. 使用 `pub(in path)` {#2-使用-pubin-path}

```rust

// src/lib.rs

pub mod a {

    pub mod b {

        // 仅 a 及其子模块可见，b 自身内部当然可见

        pub(in crate::a) fn restricted_fn() {}

    }



    pub fn call_restricted() {

        crate::a::b::restricted_fn(); // OK：a 是限定路径

    }

}



pub mod c {

    pub fn call_restricted() {

        // crate::a::b::restricted_fn(); // ERROR E0603

    }

}

```

### 3. `pub use` 重导出 {#3-pub-use-重导出}

```rust

// src/lib.rs

mod internal {

    pub struct InnerStruct;

}



pub use internal::InnerStruct as PublicStruct; // 对外暴露

```

---

## 反例与边界 {#反例与边界}

| 场景 | 代码 | 结果 |

| :--- | :--- | :--- |

| `pub(in path)` 指向非祖先 | `pub(in crate::sibling) fn f() {}` | 编译错误：`E0742`，路径不是祖先 |

| 越级访问私有 item | `crate::outer::inner::private_fn()` | 编译错误：`E0603` |

| `pub use` 提升不可见 item | `pub use private_mod::PrivateItem;` | 若 `PrivateItem` 非 `pub`，对外仍不可见 |

| 循环模块依赖 | `mod a; mod b;` 中互相 `use` | 允许，只要无循环类型定义；模块树本身无环 |

> **来源:** [Rust Reference – Name Resolution](https://doc.rust-lang.org/reference/names/name-resolution.html)

---

## 权威来源对照表 {#权威来源对照表}

| 概念 | Rust Reference | TRPL | 备注 |

| :--- | :--- | :--- | :--- |

| `mod` 声明与文件系统映射 | [Items and Modules](https://doc.rust-lang.org/reference/items/modules.html) | ch07-01 ~ ch07-05 | Reference 精确，TRPL 教学化 |

| Visibility 规则 | [Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html) | ch07-02 | `pub(in path)` 在 Reference 中定义最完整 |

| `use` 与重导出 | [Use Declarations](https://doc.rust-lang.org/reference/items/use-declarations.html) | ch07-04 | `pub use` 的 facade 模式常见于 API 设计 |

| 名称解析 | [Name Resolution](https://doc.rust-lang.org/reference/names/name-resolution.html) | — | 包含 macro、glob import 的解析细节 |

---

> **权威来源**: [Rust Reference – Items and Modules](https://doc.rust-lang.org/reference/items/modules.html) | [Rust Reference – Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html) | [Rust Reference – Use Declarations](https://doc.rust-lang.org/reference/items/use-declarations.html) | [TRPL – Managing Growing Projects](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html)

---

## 学术/社区来源参考 {#学术社区来源参考}

> **来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/)
> **来源**: [Aeneas](https://aeneas-verification.github.io/)
> **来源**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)
