# 根级综合示例

> **说明**: 本目录包含跨模块综合示例，**非 Cargo workspace 成员**。

## 用途

这些 `.rs` 文件展示多模块协同用法，可作为参考代码学习。由于不在 workspace 中，无法通过 `cargo run` 直接运行。

## 使用方式

1. **复制到 Rust Playground** - 将代码复制到 [play.rust-lang.org](https://play.rust-lang.org/) 运行
2. **作为参考** - 阅读代码理解跨模块集成模式
3. **集成到项目** - 可将所需片段复制到你的 crate 中

## 文件说明

| 文件 | 内容 |
| :--- | :--- || `advanced_usage_examples.rs` | 高级所有权、并发、错误处理示例 |
| `comprehensive_integration_example.rs` | 综合多模块集成示例 |
| `module_complete_examples.rs` | 各模块完整用法示例 |
| `real_world_applications.rs` | 实际应用场景示例 |

## 可运行示例

各模块的 `crates/*/examples/` 为可运行示例，使用以下命令运行：

```bash
cargo run -p c01_ownership_borrow_scope --example <example_name>
cargo run -p c06_async --example async_basic
# 等等
```

查看 [PROJECT_STRUCTURE.md](../PROJECT_STRUCTURE.md) 了解完整项目结构。
