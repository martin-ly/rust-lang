# CLI Tools - 命令行工具

## 📋 目录

- [概述](#概述)
- [cargo 子命令](#cargo-子命令)
- [实用工具](#实用工具)

---

## 概述

Rust 生态提供丰富的 CLI 工具来提升开发效率。

---

## cargo 子命令

### cargo-edit

```bash
# 安装
cargo install cargo-edit

# 添加依赖
cargo add tokio
cargo add serde --features derive

# 删除依赖
cargo rm tokio

# 升级依赖
cargo upgrade
```

### cargo-watch

```bash
# 安装
cargo install cargo-watch

# 自动重新编译
cargo watch -x check

# 自动运行测试
cargo watch -x test

# 自动运行程序
cargo watch -x run
```

### cargo-make

```toml
# Makefile.toml
[tasks.dev]
description = "开发环境"
command = "cargo"
args = ["run"]
watch = true

[tasks.test-all]
description = "运行所有测试"
command = "cargo"
args = ["test", "--all-features"]
```

```bash
# 安装
cargo install cargo-make

# 运行任务
cargo make dev
cargo make test-all
```

---

## 实用工具

### cargo-expand

```bash
# 展开宏
cargo install cargo-expand

# 查看展开后的代码
cargo expand
cargo expand module::function
```

### cargo-audit

```bash
# 安全审计
cargo install cargo-audit

# 检查漏洞
cargo audit
```

### cargo-outdated

```bash
# 检查过时依赖
cargo install cargo-outdated

cargo outdated
```

### cargo-tree

```bash
# 显示依赖树
cargo tree

# 查看特定依赖
cargo tree -p tokio
```

---

## 参考资源

- [Cargo Book](https://doc.rust-lang.org/cargo/)
- [cargo-edit GitHub](https://github.com/killercup/cargo-edit)

