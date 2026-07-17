> **内容分级**: [综述级]

# Rust 起步指南

> **EN**: Getting Started with Rust
> **Summary**: A practical starting guide for Rust beginners: installation, toolchain setup, first Cargo project, essential commands, editor configuration, and the learning path into ownership, types, modules, error handling, and testing.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **受众**: [初学者]
> **Bloom 层级**: L1-L2
> **权威来源**: 本文件为 `concept/` 权威页。
> **定位**: Rust 学习路径的起点。本文档假设你没有任何 Rust 背景，只需基本的命令行操作经验。
> **预计阅读时间**: 25 分钟
> **对应练习**: [exercises/src/ownership_borrowing/ex01_hello_move.rs](../../exercises/src/ownership_borrowing)
>
> **来源**:
>
> [TRPL — Getting Started](https://doc.rust-lang.org/book/ch01-00-getting-started.html) ·
> [Rust Installation](https://www.rust-lang.org/tools/install) ·
> [学习指南](../../00_meta/04_navigation/07_learning_guide.md) ·
> [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) ·
> [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/)
>
> **前置概念**: N/A
> **后置概念**:
>
> [所有权（Ownership）](../01_ownership_borrow_lifetime/01_ownership.md) ·
> [借用（Borrowing）](../01_ownership_borrow_lifetime/02_borrowing.md) ·
> [类型系统（Type System）](../02_type_system/01_type_system.md) ·
> [模块（Module）与路径](../07_modules_and_items/01_modules_and_paths.md) ·
> [错误处理（Error Handling）基础](../08_error_handling/01_error_handling_basics.md) ·
> [测试基础](../10_testing_basics/01_testing_basics.md)
---

## 认知路径

1. **问题识别**: 为什么 Rust 需要一套专门的起步流程？它与编译型、垃圾回收型语言在项目结构和工具链上有何不同？
2. **概念建立**: 掌握 `rustup`、`cargo`、`rustc` 的角色，理解 crate、模块（Module）、依赖与版本控制的基本关系。
3. **机制推理**: 通过 ⟹ 定理链将安装、构建、测试、文档生成串联为可重复的开发工作流。
4. **边界辨析**: 借助反命题/反例理解 `stable`/每日构建 通道、单 crate 与 workspace 等常见选择误区。
5. **迁移应用**: 将起步知识与 [所有权（Ownership）](../01_ownership_borrow_lifetime/01_ownership.md)、[类型系统（Type System）](../02_type_system/01_type_system.md)、[错误处理（Error Handling）](../08_error_handling/01_error_handling_basics.md) 等后置概念链接。

---

## 反命题决策树

> **反命题 1**: "Rust 起步只需要安装一个编译器即可" ⟹ 不成立。`rustup` 管理工具链版本，`cargo` 管理项目生命周期（Lifetimes），二者缺一不可。
> **反命题 2**: "任何 Rust 项目都必须从 `cargo new` 开始" ⟹ 不成立。单文件脚本、workspace、已有代码库都可以作为起点，选择取决于交付形态。
> **反命题 3**: "初学者应该直接使用每日构建版以获取最新特性" ⟹ 不成立。Stable 通道提供最佳兼容性与学习资料，每日构建版仅在学习高级/实验特性时使用。

---

## 安装 Rust

> (Source: [TRPL — Getting Started](https://doc.rust-lang.org/book/ch01-00-getting-started.html))

Rust 通过 [rustup](https://rustup.rs/) 管理工具链和版本。

```bash
# Windows (PowerShell)
irm https://rustup.rs | iex

# macOS / Linux
 curl --proto '=https' --tlsv1.2 -sSf https://rustup.rs | sh
```

验证安装：

```bash
rustc --version   # 应输出 1.97.0 或更高
cargo --version
rustup show
```

---

## 配置工具链

> (Source: [rustup.rs](https://rustup.rs/))

对于团队项目，建议在仓库根目录放置 `rust-toolchain.toml`：

```toml
[toolchain]
channel = "stable"
components = ["rustfmt", "clippy", "rust-src"]
profile = "default"
```

| 字段 | 作用 |
|:---|:---|
| `channel` | 工具链通道：`stable`、`beta`、每日构建频道 或具体版本号 |
| `components` | 额外组件：格式化、lint、源码、文档生成等 |
| `profile` | 预置组件集合：`minimal`、`default`、`complete` |

---

## 第一个 Cargo 项目

```bash
cargo new hello --bin
cd hello
cargo run
```

`cargo new` 生成的项目结构：

```text
hello/
├── Cargo.toml      # 项目配置：元数据、依赖、编译选项
├── Cargo.lock      # 依赖精确版本（可提交）
└── src/
    └── main.rs     # 可执行文件入口
```

典型的 `Cargo.toml`：

```toml
[package]
name = "hello"
version = "0.1.0"
edition = "2024"
rust-version = "1.85"

[dependencies]
```

| 字段 | 说明 |
|:---|:---|
| `name` | crate 名称，用于发布与依赖引用（Reference） |
| `version` | 遵循 SemVer 的项目版本 |
| `edition` | Rust 语言版本：2015/2018/2021/2024 |
| `rust-version` | 最低支持的 `rustc` 版本 |

---

## Cargo 基本操作

> (Source: [Cargo Book](https://doc.rust-lang.org/cargo/index.html))

| 命令 | 作用 |
|:---|:---|
| `cargo new <name>` | 创建新项目 |
| `cargo init` | 在现有目录初始化 Cargo 项目 |
| `cargo build` | 编译项目（`target/debug/`）|
| `cargo run` | 编译并运行默认可执行文件 |
| `cargo test` | 运行单元测试、集成测试与文档测试 |
| `cargo check` | 快速类型检查（不生成二进制，速度最快）|
| `cargo fmt` | 自动格式化代码 |
| `cargo clippy` | 运行 lint 与静态分析 |
| `cargo doc --open` | 生成并打开本地文档 |
| `cargo add <crate>` | 添加依赖 |

---

## 第一个程序：Hello World

```rust
// src/main.rs
fn main() {
    println!("Hello, Rust!");
}
```

`cargo run` 会先编译再执行；`cargo build --release` 生成优化后的二进制，位于 `target/release/`。

---

## 如何选择项目起点

```mermaid
flowchart TD
    A[开始学习或验证想法] --> B{需要独立 crate?}
    B -->|是| C["cargo new <name>"]
    B -->|否| D["cargo init" 在现有目录]
    C --> E{需要多个 crate?}
    E -->|是| F[使用 Cargo workspace]
    E -->|否| G[单 crate 项目]
    D --> G
    G --> H[添加 rust-toolchain.toml 与 CI]
```

| 场景 | 推荐命令 | 说明 |
|:---|:---|:---|
| 从零开始的新项目 | `cargo new` | 生成标准目录结构 |
| 已有源码目录 | `cargo init` | 原地生成 `Cargo.toml` |
| 多个相关 crate | workspace | 统一依赖、统一构建 |
| 临时脚本 | `cargo script` / `.rs` 单文件 | 快速验证小片段 |

---

## VS Code 配置建议

- 安装 [rust-analyzer](https://marketplace.visualstudio.com/items?itemName=rust-lang.rust-analyzer) 扩展。
- 推荐在 `.vscode/settings.json` 中启用 Clippy：

```json
{
    "rust-analyzer.checkOnSave.command": "clippy",
    "rust-analyzer.cargo.features": "all"
}
```

- 使用 `Even Better TOML` 扩展编辑 `Cargo.toml`。

---

## 下一步

完成安装后，进入 Rust 最核心的概念：

1. [所有权（Ownership）与移动语义](../01_ownership_borrow_lifetime/01_ownership.md)
2. [借用（Borrowing）与引用（Reference）](../01_ownership_borrow_lifetime/02_borrowing.md)
3. [类型系统（Type System）](../02_type_system/01_type_system.md)

随后再学习 [模块（Module）系统](../07_modules_and_items/01_modules_and_paths.md)、
[错误处理（Error Handling）](../08_error_handling/01_error_handling_basics.md) 与 [测试](../10_testing_basics/01_testing_basics.md)。

---
> **权威来源**:
>
> [TRPL — Getting Started](https://doc.rust-lang.org/book/ch01-00-getting-started.html) ·
> [Rust Installation](https://www.rust-lang.org/tools/install) ·
> [Cargo Book](https://doc.rust-lang.org/cargo/index.html) ·
> [rustup.rs](https://rustup.rs/)
>
> **权威来源对齐变更日志**: 2026-07-10 补充权威来源标注（TRPL、Cargo Book、rustup.rs）

## 相关概念

| 概念 | 关系 |
|:---|:---|
| [所有权](../01_ownership_borrow_lifetime/01_ownership.md) | Rust 最核心的内存管理规则 |
| [类型系统](../02_type_system/01_type_system.md) | 编译期保证程序行为的基础 |
| [Cargo 入门](../../06_ecosystem/01_cargo/15_cargo_getting_started.md) | 更完整的包管理与发布指南 |
| [模块与路径](../07_modules_and_items/01_modules_and_paths.md) | 组织 crate 内部代码的方式 |
| [错误处理基础](../08_error_handling/01_error_handling_basics.md) | 学习 `Result` 与 `?` 的起点 |
| [测试基础](../10_testing_basics/01_testing_basics.md) | `cargo test` 的详细用法 |

---

## 嵌入式测验

「嵌入式测验」涉及测验
1：本知识体系将 Rust 学习路径分为几个层级？（理解层）、测验
2：在开始学习 Rust 之前，建议先掌握哪些前置技能？（理解层）与测验
3：`cargo check` 与 `cargo build`…，本节逐一说明其要点。

### 测验 1：本知识体系将 Rust 学习路径分为几个层级？（理解层）

**题目**: 本知识体系将 Rust 学习路径分为几个层级？

<details>
<summary>✅ 答案与解析</summary>

分为 L0-L7 共 8 个层级：L0 前置知识、L1 基础、L2 进阶、L3 高级、L4 形式化、L5 比较、L6 生态、L7 未来。
</details>

---

### 测验 2：在开始学习 Rust 之前，建议先掌握哪些前置技能？（理解层）

**题目**: 在开始学习 Rust 之前，建议先掌握哪些前置技能？

<details>
<summary>✅ 答案与解析</summary>

建议具备：1) 至少一门编程语言基础；2) 基本命令行操作；3) 理解程序编译和运行的基本概念。无需预先掌握系统编程或函数式编程经验。
</details>

---

### 测验 3：`cargo check` 与 `cargo build` 的主要区别是什么？（应用层）

**题目**: 为什么日常开发中更推荐频繁使用 `cargo check`？

<details>
<summary>✅ 答案与解析</summary>

`cargo check` 只进行类型检查与借用（Borrowing）检查，不生成机器码，因此比 `cargo build` 快得多，适合快速发现编译错误。`cargo build` 会生成可执行文件或库，用于运行与发布。
</details>

## 过渡段

> **过渡**: 从安装 rustup 到创建第一个 cargo 项目，可以理解 Rust 工具链如何将源码、依赖与构建流程统一为可重复的工作流。
>
> **过渡**: 从基本命令过渡到编辑器配置，可以建立“工具链 + IDE”协同的高效开发环境。
>
> **过渡**: 从开发环境过渡到所有权与类型系统，可以形成从“能运行”到“能理解”的渐进学习路径。
>

## 反向推理

> **反向推理**: 无法运行 `cargo build` 且提示命令未找到 ⟸ 说明 Rust 工具链未正确安装或环境变量未配置。
>
> **反向推理**: 新手对 borrow checker 报错感到困惑 ⟸ 说明需要从 00_start 过渡到所有权概念进行系统学习。
>

---

## 国际权威参考 / International Authority References（P2 生态）

> 依据 `AGENTS.md` §2「对齐网络国际化权威内容」补充：仅追加已验证可达的权威链接，不改动正文事实。

- **P2 生态/社区**: [This Week in Rust — Rust 社区官方周刊（生态动态与学习资源入口）](https://this-week-in-rust.org/)（2026-07-12 验证 HTTP 200）

## 🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((Rust 起步指南))
    安装 Rust
    配置工具链
    第一个 Cargo 项目
    Cargo 基本操作
    第一个程序
```

## ⚠️ 反例与陷阱

**陷阱（move 后使用，E0382）**：新手最常见的第一道编译错误——`String` 不是按值复制的类型，赋值即移动：

```rust,compile_fail
fn main() {
    let s = String::from("hello");
    let t = s;            // s 的所有权移动给 t
    println!("{s}");      // error[E0382]: borrow of moved value: `s`
}
```

**修正对照**（借用或显式克隆，编译通过）：

```rust
fn main() {
    let s = String::from("hello");
    let t = &s;           // 借用：s 仍有效
    println!("{s} {t}");
    let u = s.clone();    // 需要两个独立值时显式 clone
    println!("{s} {u}");
}
```

> 规则速记：默认移动（move）、`Copy` 类型才复制、需要共享就借用（`&`/`&mut`）。
