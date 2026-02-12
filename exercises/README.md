# 交互式练习 (Interactive Exercises)

> **最后更新**: 2026-02-12
> **目的**: 提供 Rust 交互式学习资源入口与对接指南
> **说明**: 本项目**无内置练习题**，本目录仅作为外部工具导航入口。

---

## 推荐工具

### 1. Rustlings

**Rustlings** 是官方的命令行交互式 Rust 学习工具，通过修复代码中的错误来学习语法。

```bash
# 安装 Rustlings
rustup update
cargo install rustlings

# 或克隆仓库
git clone https://github.com/rust-lang/rustlings
cd rustlings
cargo install --path .

# 运行练习
rustlings watch
```

**官方资源**: <https://github.com/rust-lang/rustlings>

### 2. Rust Playground

**Rust Playground** 是在线运行 Rust 代码的环境，无需本地安装。

- **网址**: <https://play.rust-lang.org/>
- **使用场景**: 快速验证代码片段、分享示例、学习语法

**与本项目对接**:

- 将 `crates/*/examples/` 中的示例复制到 Playground 运行
- 速查卡中的代码块可直接粘贴到 Playground 验证

### 3. 项目内示例

本项目各模块提供可运行示例：

```bash
# 运行 C01 所有权示例
cargo run -p c01_ownership_borrow_scope --example ownership_demo

# 运行 C06 异步示例
cargo run -p c06_async --example async_basic

# 运行所有测试
cargo test --workspace
```

---

## 学习路径建议

1. **入门**: Rustlings 前 20 题 → 本项目 C01 模块
2. **巩固**: 每学完一个模块，在 Playground 重写示例
3. **进阶**: 完成本项目各模块的 `cargo test` 后，尝试扩展测试用例

---

## 相关文档

- [guides/README.md](../guides/README.md) - 学习指南入口
- [docs/quick_reference/](../docs/quick_reference/) - 速查卡（含可运行示例）
