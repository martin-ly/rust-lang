# 模块系统代码实践模式 {#模块系统代码实践模式}

> **EN**: Module Patterns And Refactoring
> **Summary**: 模块系统代码实践模式 Module Patterns And Refactoring.
> **内容分级**: [核心级]
> **层级**: L5 (代码实践)
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **概念族**: 形式化模块 / 代码实践
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [模块系统代码实践模式 {#模块系统代码实践模式}](#模块系统代码实践模式-模块系统代码实践模式)
  - [目录 {#目录}](#目录-目录)
  - [1. 按职责分层组织 crate {#1-按职责分层组织-crate}](#1-按职责分层组织-crate-1-按职责分层组织-crate)
    - [目标 {#目标-4}](#目标-目标-4)
    - [推荐结构 {#推荐结构}](#推荐结构-推荐结构)
    - [`lib.rs` 示例 {#librs-示例}](#librs-示例-librs-示例)
  - [2. `pub use` 重导出稳定 API {#2-pub-use-重导出稳定-api}](#2-pub-use-重导出稳定-api-2-pub-use-重导出稳定-api)
    - [目标 {#目标-4}](#目标-目标-4-1)
    - [示例 {#示例-1}](#示例-示例-1)
    - [好处 {#好处}](#好处-好处)
  - [3. Sealed trait 与私有 supertrait {#3-sealed-trait-与私有-supertrait}](#3-sealed-trait-与私有-supertrait-3-sealed-trait-与私有-supertrait)
    - [目标 {#目标-4}](#目标-目标-4-2)
    - [模式实现 {#模式实现}](#模式实现-模式实现)
  - [4. 内部模块封装 unsafe {#4-内部模块封装-unsafe}](#4-内部模块封装-unsafe-4-内部模块封装-unsafe)
    - [目标 {#目标-4}](#目标-目标-4-3)
    - [示例 {#示例-1}](#示例-示例-1-1)
  - [5. Workspace 多 crate 共享 {#5-workspace-多-crate-共享}](#5-workspace-多-crate-共享-5-workspace-多-crate-共享)
    - [目标 {#目标-4}](#目标-目标-4-4)
    - [`Cargo.toml` {#cargotoml}](#cargotoml-cargotoml)
    - [子 crate 依赖 {#子-crate-依赖}](#子-crate-依赖-子-crate-依赖)
    - [注意事项 {#注意事项}](#注意事项-注意事项)
  - [6. 重构示例：从扁平模块到分层 {#6-重构示例从扁平模块到分层}](#6-重构示例从扁平模块到分层-6-重构示例从扁平模块到分层)
    - [重构前 {#重构前}](#重构前-重构前)
    - [重构后 {#重构后}](#重构后-重构后)
    - [验证清单 {#验证清单}](#验证清单-验证清单)
  - [总结 {#总结}](#总结-总结)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术/社区来源参考 {#学术社区来源参考}](#学术社区来源参考-学术社区来源参考)

---

## 1. 按职责分层组织 crate {#1-按职责分层组织-crate}

### 目标 {#目标-4}

将 crate 内部按**输入/处理/输出**或**公开 API / 领域逻辑 / 适配器**分层，降低模块间耦合。

### 推荐结构 {#推荐结构}

```text
my_parser/
├── Cargo.toml
└── src/
    ├── lib.rs          // 公开 API 门面
    ├── ast.rs          // L3 领域概念：抽象语法树
    ├── lexer.rs        // L4 实现机制：词法分析
    ├── parser.rs       // L4 实现机制：语法分析
    └── error.rs        // L3 领域概念：错误类型
```

### `lib.rs` 示例 {#librs-示例}

```rust
//! MyParser —— 一个轻量级表达式解析器。

pub mod ast;
pub mod error;

// 实现细节不公开，但同一 crate 内可访问
mod lexer;
mod parser;

pub use ast::{Expr, Literal};
pub use error::ParseError;

use lexer::tokenize;
use parser::parse_tokens;

/// 公开入口：将源代码解析为 AST。
pub fn parse(input: &str) -> Result<Expr, ParseError> {
    let tokens = tokenize(input)?;
    parse_tokens(&tokens)
}
```

> **原则**：`pub` 项构成稳定 API；私有模块保留重构自由度。

---

## 2. `pub use` 重导出稳定 API {#2-pub-use-重导出稳定-api}

### 目标 {#目标-4}

让 crate 用户通过一个简洁的入口访问常用类型，同时内部结构可以演进。

### 示例 {#示例-1}

```rust
// src/lib.rs
mod core {
    pub mod engine;
    pub mod types;
}

mod adapters {
    pub mod http;
    pub mod db;
}

// 重导出用户最常用的类型
pub use core::engine::Engine;
pub use core::types::{Config, Request, Response};

// 高级用户仍可访问完整内部路径
pub mod adapters;
```

### 好处 {#好处}

- 内部重构（如拆分 `core::types`）不影响大多数用户。
- 版本升级时可通过重导出标记 deprecated 路径。

---

## 3. Sealed trait 与私有 supertrait {#3-sealed-trait-与私有-supertrait}

### 目标 {#目标-4}

限制 trait 的下游实现，保持库内部不变量。

### 模式实现 {#模式实现}

```rust
// src/lib.rs

/// 私有模块，外部无法访问 `Sealed`。
mod private {
    pub trait Sealed {}
}

/// 公开 trait，但实现它要求实现私有的 `Sealed`，
/// 因此下游 crate 无法为自己类型实现 `StableTrait`。
pub trait StableTrait: private::Sealed {
    fn stable_method(&self);
}

// 只在当前 crate 内为具体类型实现 Sealed 与 StableTrait。
impl private::Sealed for MyType {}
impl StableTrait for MyType {
    fn stable_method(&self) {}
}
```

> **应用场景**：标准库中 `ExactSizeIterator`、`ToString` 等均使用类似 sealed trait 技术保证未来可扩展。

---

## 4. 内部模块封装 unsafe {#4-内部模块封装-unsafe}

### 目标 {#目标-4}

将 `unsafe` 操作限制在最小私有模块中，公开 API 强制通过安全包装调用。

### 示例 {#示例-1}

```rust
// src/lib.rs

mod raw {
    /// 内部 unsafe 实现：直接操作裸指针。
    /// 该函数仅在 crate 内部可见。
    pub(crate) unsafe fn swap_bytes(buf: *mut u8, len: usize) {
        // unsafe 不变量：buf 必须指向 len 个有效字节
        let slice = std::slice::from_raw_parts_mut(buf, len);
        slice.reverse();
    }
}

/// 安全公开 API：反转字节缓冲区。
pub fn reverse_buffer(buf: &mut [u8]) {
    // 所有前提条件在此处验证
    unsafe { raw::swap_bytes(buf.as_mut_ptr(), buf.len()) };
}
```

> **原则**：unsafe 代码块的正确性依赖调用处维持的不变量；将这些不变量封装在私有模块中，避免外部破坏。

---

## 5. Workspace 多 crate 共享 {#5-workspace-多-crate-共享}

### 目标 {#目标-4}

使用 Cargo workspace 将大型项目拆分为多个 crate，同时保持统一构建与依赖管理。

### `Cargo.toml` {#cargotoml}

```toml
[workspace]
members = ["my_parser", "my_cli", "my_wasm"]
resolver = "3"

[workspace.dependencies]
thiserror = "2"
serde = { version = "1", features = ["derive"] }
```

### 子 crate 依赖 {#子-crate-依赖}

```toml
# my_cli/Cargo.toml {#my_clicargotoml}
[package]
name = "my_cli"
version = "0.1.0"
edition = "2024"

[dependencies]
my_parser = { path = "../my_parser" }
serde = { workspace = true }
```

### 注意事项 {#注意事项}

- 一个 package 只能有一个 `lib`，但可以有多个 `bin`。
- `path` 依赖不会自动发布到 crates.io，发布时需要指定版本。
- Workspace 中共享 `resolver = "3"` 避免依赖解析差异。

---

## 6. 重构示例：从扁平模块到分层 {#6-重构示例从扁平模块到分层}

### 重构前 {#重构前}

```rust
// src/lib.rs (扁平结构)
pub mod lexer;
pub mod parser;
pub mod ast;
pub mod error;
pub mod utils;
```

问题：

- 用户必须了解内部模块才能找到 API。
- 所有内部结构都暴露，重构困难。

### 重构后 {#重构后}

```rust
// src/lib.rs (门面模式)
pub mod ast;
pub mod error;

mod lexer;
mod parser;
mod utils;

pub use ast::{Expr, Literal};
pub use error::ParseError;

pub fn parse(input: &str) -> Result<Expr, ParseError> {
    // ...
}
```

### 验证清单 {#验证清单}

- [ ] `cargo check` 通过。
- [ ] `cargo doc --no-deps` 生成的公开 API 页面只包含预期项。
- [ ] 使用 `cargo public-api`（可选工具）检查 API 变化。

---

## 总结 {#总结}

| 模式 | 解决的问题 | 可见性关键字 | 典型应用 |
|------|------------|--------------|----------|
| 职责分层 | 降低模块耦合 | `pub` / 私有 | 中大型 crate |
| `pub use` 重导出 | 提供稳定门面 | `pub use` | 库公开 API |
| Sealed trait | 防止外部实现 | 私有 supertrait | 可扩展 trait |
| unsafe 封装 | 安全边界 | `pub(crate)` / 私有 | FFI、裸指针 |
| Workspace | 多 crate 协作 | workspace 配置 | 大型项目 |

> **权威来源**: [Rust Reference – Items and Modules](https://doc.rust-lang.org/reference/items.html) | [Rust Reference – Visibility and Privacy](https://doc.rust-lang.org/reference/visibility-and-privacy.html) | [The Rust Programming Language – Ch 7](https://doc.rust-lang.org/book/ch07-00-managing-growing-projects-with-packages-crates-and-modules.html) | [Cargo Book – Workspaces](https://doc.rust-lang.org/cargo/reference/workspaces.html) | [API Guidelines – Sealed Traits](https://rust-lang.github.io/api-guidelines/future-proofing.html)
>
> **可运行代码示例**: [examples/module_system_patterns.rs](../../../examples/module_system_patterns.rs)（包含门面分层、sealed trait、unsafe 封装三种模式的编译运行示例）

## 相关概念 {#相关概念}

- [模块系统规范](10_module_system_specification.md)
- [模块系统反例与边界案例](60_module_counterexamples.md)
- [Linkage 与符号](20_linkage_and_symbols.md)
- [模块系统与安全抽象](40_module_safety_abstraction.md)
- [知识图谱索引](../10_knowledge_graph_index.md)

---

## 学术/社区来源参考 {#学术社区来源参考}

> **来源**: [RustBelt](https://plv.mpi-sws.org/rustbelt/)
> **来源**: [Aeneas](https://aeneas-verification.github.io/)
> **来源**: [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)
