> **内容分级**: [初学者]

# Rust 起步指南

> **EN**: Getting Started with Rust
> **Summary**: Getting Started with Rust: core Rust concepts, syntax, and examples.
> **受众**: [初学者]
> **Bloom 层级**: 记忆 → 理解
> **定位**: Rust 学习路径的起点。本文档假设你没有任何 Rust 背景，只需基本的命令行操作经验。
> **预计阅读时间**: 20 分钟
> **对应练习**: [exercises/src/ownership_borrowing/ex01_hello_move.rs](../../exercises/src/ownership_borrowing)
>
> **来源**: [TRPL — Getting Started](https://doc.rust-lang.org/book/ch01-00-getting-started.html) · [Rust Installation](https://www.rust-lang.org/tools/install) · [学习指南](../00_meta/learning_guide.md) · [RustBelt — POPL 2018](https://plv.mpi-sws.org/rustbelt/popl18/) · [O'Hearn — Separation Logic and Shared Mutable Data](https://doi.org/10.1017/S0960129501001003) · [Brown University — Concepts in Rust Programming](https://cel.cs.brown.edu/crp/) · [Brown Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Rust Reference](https://doc.rust-lang.org/reference/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> **前置概念**: N/A
> **后置概念**: N/A
---

## 安装 Rust

Rust 通过 [rustup](https://rustup.rs/) 管理工具链和版本。

```bash
# Windows (PowerShell)
irm https://rustup.rs | iex

# macOS / Linux
curl --proto '=https' --tlsv1.2 -sSf https://rustup.rs | sh
```

验证安装：

```bash
rustc --version   # 应输出 1.96.1 或更高
cargo --version
```

---

## 第一个程序：Hello World

```bash
cargo new hello
cd hello
cargo run
```

`cargo new` 生成的项目结构：

```text
hello/
├── Cargo.toml      # 项目配置：依赖、元数据
└── src/
    └── main.rs     # 程序入口
```

---

## Cargo 基本操作

| 命令 | 作用 |
|:---|:---|
| `cargo new <name>` | 创建新项目 |
| `cargo build` | 编译项目（`target/debug/`）|
| `cargo run` | 编译并运行 |
| `cargo test` | 运行测试 |
| `cargo check` | 快速检查（不生成二进制）|
| `cargo doc --open` | 生成并打开文档 |

---

## VS Code 配置建议

- 安装 [rust-analyzer](https://marketplace.visualstudio.com/items?itemName=rust-lang.rust-analyzer) 扩展
- 启用 `"rust-analyzer.checkOnSave.command": "clippy"`

---

## 下一步

完成安装后，进入 所有权（Ownership）与移动语义——Rust 最核心的概念。

## 嵌入式测验（Embedded Quiz）

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

### 测验 3：本知识体系中的概念文件为什么采用 L1-L7 的层级编号？（理解层）

**题目**: 本知识体系中的概念文件为什么采用 L1-L7 的层级编号？

<details>
<summary>✅ 答案与解析</summary>

层级编号帮助学习者根据自身水平选择合适内容，从基础语法到形式化验证逐步深入，形成结构化的学习路径。
</details>
