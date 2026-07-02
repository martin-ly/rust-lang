> **内容分级**: [研究级]
>
# Rust 常用开发工具

> **EN**: Useful Development Tools
> **Summary**: Rust 官方/社区推荐的开发工具：rustfmt、rustfix/cargo fix、Clippy、rust-analyzer，以及它们在日常开发中的典型用法。
>
> **受众**: [初学者] / [中级]
> **Bloom 层级**: 记忆 → 应用
> **A/S/P 标记**: **P** — Practice
> **双维定位**: P×Tool — 工具链与工程实践
> **前置依赖**: [Toolchain](01_toolchain.md) · [Cargo Subcommands and Plugins](66_cargo_subcommands_and_plugins.md)
> **后置概念**: [Cargo Profiles and Lints](65_cargo_profiles_and_lints.md) · [Testing Basics](../01_foundation/16_testing_basics.md) · [Rust vs C++](../05_comparative/01_rust_vs_cpp.md)
> **定理链**: N/A — 工具/实践文档
> **主要来源**: [TRPL — Appendix D](https://doc.rust-lang.org/book/appendix-04-useful-development-tools.html) · [rust-analyzer](https://rust-analyzer.github.io/)

>
> **来源**: [TRPL — Appendix D: Useful Development Tools](https://doc.rust-lang.org/book/appendix-04-useful-development-tools.html) · [rustfmt](https://github.com/rust-lang/rustfmt) · [Clippy](https://doc.rust-lang.org/clippy/) · [rust-analyzer](https://rust-analyzer.github.io/)

---

## 一、代码格式化：`rustfmt`

`rustfmt` 按照社区代码风格自动格式化 Rust 代码。标准 Rust 安装已包含 `rustfmt` 和 `cargo fmt`。

```bash
# 格式化整个 Cargo 项目
cargo fmt

# 检查格式而不修改文件
cargo fmt -- --check
```

> `cargo fmt` 只改变代码风格，不改变代码语义。团队项目通常将其加入 CI，避免风格争论。

### 配置

通过项目根目录的 `rustfmt.toml` 或 `.rustfmt.toml` 自定义风格：

```toml
edition = "2024"
max_width = 100
tab_spaces = 4
```

---

## 二、自动修复：`cargo fix`

`cargo fix`（底层工具 `rustfix`）可以自动应用编译器建议的修复。

### 典型场景

1. **移除不必要的 `mut`**：

```rust
fn main() {
    let mut x = 42; // warning: variable does not need to be mutable
    println!("{x}");
}
```

运行 `cargo fix` 后：

```rust
fn main() {
    let x = 42;
    println!("{x}");
}
```

1. **Edition 迁移**：

```bash
# 将代码自动迁移到指定 Edition
cargo fix --edition
```

> `cargo fix` 只应用编译器明确建议的修复，执行前建议先提交代码或使用版本控制。

---

## 三、额外 Lint：Clippy

Clippy 是 Rust 的 lint 集合，用于捕获常见错误和改进代码质量。

```bash
# 运行 Clippy
cargo clippy

# 将警告视为错误（常用于 CI）
cargo clippy -- -D warnings

# 自动应用 Clippy 建议的修复
cargo clippy --fix
```

### 示例

```rust
fn main() {
    let x = 3.1415;
    let r = 8.0;
    println!("the area of the circle is {}", x * r * r);
}
```

Clippy 会提示：

```text
error: approximate value of `f{32, 64}::consts::PI` found
  = help: consider using the constant directly
```

修复后：

```rust
fn main() {
    let x = std::f64::consts::PI;
    let r = 8.0;
    println!("the area of the circle is {}", x * r * r);
}
```

### 常用 Clippy 配置

```rust
#![warn(clippy::pedantic)]      // 启用更多 lint
#![allow(clippy::needless_return)] // 禁用特定 lint
```

---

## 四、IDE 支持：`rust-analyzer`

`rust-analyzer` 是 Rust 官方推荐的 LSP（Language Server Protocol）实现，提供 IDE 功能：

- 自动补全
- 跳转到定义
- 类型提示
- 内联错误/警告
- 重命名重构
- 代码操作（code actions）

### 安装

通常通过 IDE 插件市场安装（如 VS Code 的 rust-analyzer 插件），或独立安装语言服务器：

```bash
rustup component add rust-analyzer
```

### 推荐 IDE/编辑器

| IDE/编辑器 | 插件 |
|:---|:---|
| VS Code | rust-analyzer |
| JetBrains IDE | RustRover / IntelliJ Rust |
| Vim/Neovim | rust-analyzer + LSP 客户端 |
| Emacs | rust-analyzer + lsp-mode / eglot |

---

## 五、工具组合工作流

```bash
# 1. 格式化代码
cargo fmt

# 2. 自动修复编译器警告
cargo fix

# 3. 运行 Clippy 检查
cargo clippy -- -D warnings

# 4. 运行测试
cargo test
```

> 推荐在提交前运行以上步骤，或在 CI 中强制执行。

---

## 六、关联概念

| 概念 | 关系 |
|:---|:---|
| [Toolchain](01_toolchain.md) | rustfmt、clippy、rust-analyzer 是工具链组件 |
| [Cargo Profiles and Lints](65_cargo_profiles_and_lints.md) | Clippy lint 与 Cargo lint 继承配合使用 |
| [Cargo Subcommands and Plugins](66_cargo_subcommands_and_plugins.md) | `cargo fmt`、`cargo clippy`、`cargo fix` 都是 Cargo 子命令 |
| [Testing Basics](../01_foundation/16_testing_basics.md) | 工具链最终服务于代码质量保证 |
