# 模块系统与路径：Rust 的代码组织哲学

> **Bloom 层级**: 记忆 → 应用
> **定位**: 系统讲解 Rust **模块系统**——从 `mod`、`use`、`pub` 的语法到文件系统映射、工作空间组织，揭示 Rust 如何通过模块系统实现代码封装、可见性控制和大型项目组织。
> **前置概念**: [Ownership](./01_ownership.md) · [Type System](./04_type_system.md)
> **后置概念**: [Crate Ecosystem](../06_ecosystem/03_core_crates.md) · [Workspace](../06_ecosystem/01_toolchain.md)

---

> **来源**: [Rust Reference — Modules](https://doc.rust-lang.org/reference/items/modules.html) ·
> [TRPL — Packages, Crates, Modules](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html) ·
> [Cargo Book — Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html) ·
> [Rust API Guidelines — Naming](https://rust-lang.github.io/api-guidelines/naming.html) ·
> [RFC 2126 — Uniform Paths](https://rust-lang.github.io/rfcs/2126-path-clarity.html)

## 📑 目录
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

- [模块系统与路径：Rust 的代码组织哲学](#模块系统与路径rust-的代码组织哲学)
  - [📑 目录](#-目录)
  - [一、核心概念](#一核心概念)
    - [1.1 模块层次结构](#11-模块层次结构)
    - [1.2 可见性系统](#12-可见性系统)
    - [1.3 路径解析](#13-路径解析)
  - [二、技术细节](#二技术细节)
    - [2.1 文件系统映射](#21-文件系统映射)
    - [2.2 use 语句与重导出](#22-use-语句与重导出)
    - [2.3 工作空间（Workspace）](#23-工作空间workspace)
  - [三、设计模式矩阵](#三设计模式矩阵)
  - [四、反命题与边界分析](#四反命题与边界分析)
    - [4.1 反命题树](#41-反命题树)
    - [4.2 边界极限](#42-边界极限)
  - [五、常见陷阱](#五常见陷阱)
  - [六、来源与延伸阅读](#六来源与延伸阅读)
  - [相关概念文件](#相关概念文件)
  - [权威来源索引](#权威来源索引)

---

## 一、核心概念
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 1.1 模块层次结构
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```text
Rust 模块系统的核心实体:

  Package（包）:
  ├── 一个 Cargo.toml 定义
  ├── 包含一个或多个 Crate
  └── 对应一个代码仓库

  Crate（ crate）:
  ├── 一个编译单元
  ├── 可以是二进制（bin）或库（lib）
  └── 生成一个 .rlib 或可执行文件

  Module（模块）:
  ├── 代码的逻辑分组
  ├── 控制可见性边界
  ├── 可以嵌套
  └── 映射到文件或目录

  层级关系:
  Package
  └── Crate (binary / library)
      └── Module (root)
          ├── Module (child)
          │   └── Module (grandchild)
          └── Module (sibling)

  示例结构:
  my_project/
  ├── Cargo.toml          # Package 定义
  └── src/
      ├── main.rs         # 二进制 crate root
      └── lib.rs          # 或库 crate root
          ├── mod front_of_house;    // 声明子模块
          │   └── front_of_house.rs  // 模块实现
          └── mod back_of_house;
              └── back_of_house/
                  ├── mod.rs        // 目录模块
                  └── hosting.rs    // 子模块
```

> **认知功能**: Rust 的模块系统与**文件系统解耦**——`mod` 声明显式控制哪些文件被包含，不同于 Python/JS 的自动文件映射。
> [来源: [TRPL — Modules](https://doc.rust-lang.org/book/ch07-02-defining-modules-to-control-scope-and-privacy.html)]

---

### 1.2 可见性系统
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```rust,ignore
// Rust 的可见性修饰符

mod outer {
    // 默认: 私有（仅当前模块及子模块可见）
    fn private_fn() {}

    // pub: 对所有模块可见
    pub fn public_fn() {}

    // pub(crate): 对整个 crate 可见
    pub(crate) fn crate_fn() {}

    // pub(super): 对父模块可见
    pub(super) fn super_fn() {}

    // pub(in path): 对指定路径可见
    pub(in crate::outer) fn restricted_fn() {}

    pub mod inner {
        // 子模块可以访问父模块的私有项
        pub fn call_parent_private() {
            // super::private_fn(); // ✅ 可以访问！
        }
    }
}

// 可见性对比:
┌────────────────┬─────────────────────────────────────────┐
│ 修饰符         │ 可见范围                                │
├────────────────┼─────────────────────────────────────────┤
│ (无)           │ 当前模块 + 所有子模块                   │
│ pub            │ 任何地方                                │
│ pub(crate)     │ 当前 crate                              │
│ pub(super)     │ 父模块                                  │
│ pub(in path)   │ 指定的模块路径                          │
│ pub(self)      │ 等同于私有（显式）                      │
└────────────────┴─────────────────────────────────────────┘
```

> **可见性洞察**: Rust 的**默认私有**设计遵循"最小权限原则"——与 Python/JavaScript 的默认公开形成鲜明对比。
> [来源: [Rust Reference — Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html)]

---

### 1.3 路径解析
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

```rust,ignore
// 路径类型

// 绝对路径: 从 crate root 开始
crate::front_of_house::hosting::add_to_waitlist();

// 相对路径: 从当前模块开始
front_of_house::hosting::add_to_waitlist();
self::front_of_house::hosting::add_to_waitlist();

// 父模块
super::some_function();

// Edition 2018+ 的变更:
// - 外部 crate 直接使用 crate_name::...
// - 不再需要 extern crate
// - use 路径更清晰

use std::collections::HashMap;           // 导入具体项
use std::collections::*;                 // 通配符导入
use std::io::{self, Write};              // 重命名 + 多导入
use std::io::Result as IoResult;         // 别名

// use 的嵌套语法（减少重复）
use std::{
    collections::HashMap,
    io::{self, Write, Read},
    fs::File,
};

// pub use: 重导出（重构 API 表面）
pub use self::hosting::add_to_waitlist;  // 外部可见
```

> **路径洞察**: Rust 的**Uniform Paths**（统一路径）在 2018 Edition 中引入，消除了 `extern crate` 的需要，使路径系统更直观。
> [来源: [RFC 2126 — Path Clarity](https://rust-lang.github.io/rfcs/2126-path-clarity.html)]

---

## 二、技术细节
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

### 2.1 文件系统映射
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```text
模块到文件的映射规则:

  单文件模块:
  ├── mod foo; 在 lib.rs 中
  └── 对应 foo.rs 文件

  目录模块:
  ├── mod foo; 在 lib.rs 中
  └── 对应 foo/mod.rs 文件
  └── foo/ 目录下可包含其他模块文件

  2021 Edition 新增:
  ├── foo.rs 可以直接作为模块文件
  └── foo/ 目录下的文件作为子模块
  └── (无需 foo/mod.rs)

  示例 (2021 Edition):
  src/
  ├── lib.rs
  ├── front_of_house.rs      // front_of_house 模块
  └── front_of_house/        // front_of_house 的子模块
      ├── hosting.rs
      └── serving.rs

  传统方式 (2018 Edition):
  src/
  ├── lib.rs
  └── front_of_house/
      ├── mod.rs             // 必须
      ├── hosting.rs
      └── serving.rs
```

> **文件映射洞察**: 2021 Edition 的**模块系统改进**消除了 `mod.rs` 的需要，使文件结构更清晰（类似 Python 的 `__init__.py`）。
> [来源: [Rust Edition Guide — 2021](https://doc.rust-lang.org/edition-guide/rust-2021/index.html)]

---

### 2.2 use 语句与重导出
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust,ignore
// 重导出（Re-export）模式

// 场景: 重构内部模块结构，但保持外部 API 不变

// internal/implementation.rs
pub fn complex_operation() {}

// internal/mod.rs
pub mod implementation;

// lib.rs
// 内部结构复杂，但对外暴露简洁 API
mod internal;

// 重导出: 外部用户只需 use mycrate::complex_operation;
pub use internal::implementation::complex_operation;

// 预lude 模式: 自动导入常用项
pub mod prelude {
    pub use crate::MyTrait;
    pub use crate::MyStruct;
}

// 用户: use mycrate::prelude::*;

// 扁平化导出: 将深层模块项提升到顶层
pub use self::{
    config::Config,
    error::Error,
    client::Client,
};
```

> **重导出洞察**: `pub use` 是 Rust **API 设计**的核心工具——它允许内部模块保持清晰结构，同时对外暴露简洁的 API 表面。
> [来源: [Rust API Guidelines — Re-exports](https://rust-lang.github.io/api-guidelines/naming.html#casing-conforms-to-rfc-430-c-casing)]

---

### 2.3 工作空间（Workspace）
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```toml
# Cargo.toml (workspace root)
[workspace]
members = [
    "my_app",
    "my_lib",
    "my_utils",
]
resolver = "2"

# 共享依赖
[workspace.dependencies]
tokio = { version = "1", features = ["full"] }
serde = { version = "1", features = ["derive"] }
```

```text
工作空间结构:

  my_workspace/
  ├── Cargo.toml          # Workspace 定义（无 [package]）
  ├── my_app/
  │   └── Cargo.toml      # 依赖 my_lib 和 my_utils
  ├── my_lib/
  │   └── Cargo.toml      # 可能依赖 my_utils
  └── my_utils/
      └── Cargo.toml      # 基础工具 crate

  工作空间的优势:
  ├── 共享 Cargo.lock（统一依赖版本）
  ├── 共享 target 目录（减少磁盘使用）
  ├── 跨 crate 编译优化
  ├── cargo test --workspace 运行所有测试
  └── 适合大型项目/微服务架构

  常见模式:
  ├── bin + lib 分离: app 调用 library
  ├── 多 bin: 同一仓库多个可执行文件
  ├── 分层架构: core → domain → application
  └── 单体工作空间: 所有微服务在一个仓库
```

> **工作空间洞察**: Cargo Workspace 是 Rust **大型项目组织**的标准方式——它将单一代码库（monorepo）的优势与 crate 的模块化结合。
> [来源: [Cargo Book — Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html)]

---

## 三、设计模式矩阵
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

```text
场景 → 模式 → 实现

创建库 API:
  → 内部模块组织实现细节
  → pub use 重导出公开 API
  → prelude 模块简化导入

大型项目组织:
  → Workspace 分 crate
  → 每个 crate 有清晰的职责边界
  → 依赖关系形成有向无环图

测试私有函数:
  → #[cfg(test)] mod tests { use super::*; }
  → 测试模块作为子模块访问私有项
  → 或使用 integration tests（tests/ 目录）

条件编译:
  → #[cfg(feature = "async")]
  → mod async_impl;
  → 特性控制模块包含
```

> **模式矩阵**: Rust 的模块系统与**Cargo 特性**（features）结合，实现强大的**条件编译和可选依赖**管理。
> [来源: [Cargo Book — Features](https://doc.rust-lang.org/cargo/reference/features.html)]

---

## 四、反命题与边界分析
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

### 4.1 反命题树
>
> **[来源: [crates.io](https://crates.io/)]**

```mermaid
graph TD
    ROOT["命题: 所有项都应 pub"]
    ROOT --> Q1{"是否是公共 API?"}
    Q1 -->|是| PUB["✅ pub"]
    Q1 -->|否| Q2{"是否跨模块使用?"}
    Q2 -->|是| PUB_CRATE["✅ pub(crate)"]
    Q2 -->|否| PRIVATE["✅ 私有"]

    style PUB fill:#c8e6c9
    style PUB_CRATE fill:#fff3e0
    style PRIVATE fill:#c8e6c9
```

> **认知功能**: 可见性的**核心决策**是"谁需要访问"——默认私有，按需放宽。
> [来源: [Rust API Guidelines — Exposure](https://rust-lang.github.io/api-guidelines/naming.html)]

---

### 4.2 边界极限
>
> **[来源: [docs.rs](https://docs.rs/)]**

```text
边界 1: 循环依赖
├── Crate A 不能依赖 Crate B，同时 B 依赖 A
├── 编译器拒绝循环依赖
├── 需要重构为三个 crate（提取公共部分）
└── 或者使用 trait 解耦

边界 2: 可见性的编译期特性
├── 可见性完全是编译期概念
├── 无运行时检查开销
├── 无法通过反射绕过
└── 这是安全保证的一部分

边界 3: 集成测试的限制
├── tests/ 目录下的测试是外部 crate
├── 只能测试 pub 项
├── 需要 #[cfg(test)] 内联测试来测试私有项
└── 或者使用 pub(crate) 妥协

边界 4: 宏与模块的交互
├── 宏展开在模块解析之后
├── 宏生成的代码受相同可见性规则约束
├── 复杂宏可能产生意外的路径问题
└── 缓解: 使用 $crate 引用当前 crate

边界 5: 路径冲突
├── use std::result::Result; 与自定义 Result 冲突
├── 需要显式路径或别名
└── 缓解: 使用 fully qualified syntax
```

> **边界要点**: 模块系统的边界主要与**循环依赖**、**集成测试限制**、**宏交互**和**路径冲突**相关。
> [来源: [Rust Reference — Modules](https://doc.rust-lang.org/reference/items/modules.html)]

---

## 五、常见陷阱
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [TRPL](https://doc.rust-lang.org/book/)]

```text
陷阱 1: mod 和文件不同步
  ❌ lib.rs: mod foo;
     // 但文件名为 bar.rs
     // 编译错误: cannot find module file

  ✅ mod foo; → foo.rs (或 foo/mod.rs)

陷阱 2: 忘记 pub
  ❌ mod inner { fn helper() {} }
     // 外部无法调用 helper

  ✅ mod inner { pub fn helper() {} }
     // 或者 pub(crate) 根据需要

陷阱 3: use 和 mod 混淆
  ❌ use foo;  // 导入外部 crate
     // 但 foo 是本地模块

  ✅ mod foo;  // 声明本地模块
     // use foo::Bar;  // 导入模块中的项

陷阱 4: 循环模块依赖
  ❌ mod a { use crate::b::B; }
     mod b { use crate::a::A; }
     // 编译错误（如果形成循环）

  ✅ 重构为共享模块或使用 trait

陷阱 5: Workspace 中版本不一致
  ❌ crate A 依赖 tokio 1.0
     crate B 依赖 tokio 1.5
     // 工作空间可能有两个 tokio 版本

  ✅ 在 workspace.dependencies 中统一管理
```

> **陷阱总结**: 模块系统的陷阱主要与**文件命名**、**可见性**、**use/mod 混淆**、**循环依赖**和**workspace 版本管理**相关。
> [来源: [TRPL — Common Module Issues](https://doc.rust-lang.org/book/ch07-05-separating-modules-into-different-files.html)]

---

## 六、来源与延伸阅读
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

| 来源 | 可信度 | 说明 |
|:---|:---:|:---|
| [Rust Reference — Modules](https://doc.rust-lang.org/reference/items/modules.html) | ✅ 一级 | 模块系统参考 |
| [TRPL — Packages, Crates, Modules](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html) | ✅ 一级 | 基础教程 |
| [Cargo Book — Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html) | ✅ 一级 | 工作空间 |
| [RFC 2126 — Path Clarity](https://rust-lang.github.io/rfcs/2126-path-clarity.html) | ✅ 一级 | 路径改进 |
| [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/naming.html) | ✅ 一级 | API 设计 |

---

## 相关概念文件
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]
>
> [来源: [Rust Reference](https://doc.rust-lang.org/reference/)]

- [Ownership](./01_ownership.md) — 所有权系统
- [Type System](./04_type_system.md) — 类型系统
- [Crate Ecosystem](../06_ecosystem/03_core_crates.md) — 核心 crate
- [Toolchain](../06_ecosystem/01_toolchain.md) — 工具链

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/)
>
> **权威来源对齐变更日志**: 2026-05-22 创建 [来源: Authority Source Sprint Batch 10]

**文档版本**: 1.0
**对应 Rust 版本**: 1.96.0+ (Edition 2024)
**最后更新**: 2026-05-22
**状态**: ✅ 概念文件创建完成

---

## 权威来源索引

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**
