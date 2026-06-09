> **内容分级**: [初学者]

# Rust 起步指南

> **EN**: Getting Started with Rust
> **Summary**: 安装 Rust 工具链，运行第一个程序，理解 Cargo 基本操作。
> **受众**: [初学者]
> **Bloom 层级**: 记忆 → 理解
> **定位**: Rust 学习路径的起点。本文档假设你没有任何 Rust 背景，只需基本的命令行操作经验。
> **预计阅读时间**: 20 分钟
> **对应练习**: [exercises/src/ownership_borrowing/ex01_hello_move.rs](../../exercises/src/ownership_borrowing/)

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
rustc --version   # 应输出 1.96.0 或更高
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

完成安装后，进入 [所有权与移动语义](./01_ownership.md)——Rust 最核心的概念。
