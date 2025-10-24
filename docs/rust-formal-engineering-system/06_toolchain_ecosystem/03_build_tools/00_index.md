

## 📊 目录

- [构建与脚本（Build Tools \& Scripts）索引](#构建与脚本build-tools--scripts索引)
  - [目的](#目的)
  - [推荐做法](#推荐做法)
  - [示例](#示例)
  - [相关条目](#相关条目)
  - [导航](#导航)


# 构建与脚本（Build Tools & Scripts）索引

## 目的

- 统一构建脚本、任务脚本与跨平台执行方式，减少环境差异。

## 推荐做法

- 首选 `cargo` 子命令与工作区脚本，不再依赖 `justfile`。
- 在 README 提供 Windows PowerShell 与 Unix Shell 的等价命令。
- 将长命令封装为 Cargo alias（`.cargo/config.toml`）。

## 示例

```bash
# 统一构建
cargo build --all-targets

# 常见任务
cargo fmt --all
cargo clippy -- -D warnings
```

## 相关条目

- 包管理：[`../02_package_manager/00_index.md`](../02_package_manager/00_index.md)
- 测试框架：[`../04_testing_frameworks/00_index.md`](../04_testing_frameworks/00_index.md)

## 导航

- 返回工具链：[`../00_index.md`](../00_index.md)
