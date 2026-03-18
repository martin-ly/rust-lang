# Cargo 基础

> **Rust 的包管理器和构建工具**

## 🎯 学习目标

- [ ] 管理项目依赖
- [ ] 使用 Cargo 构建项目
- [ ] 理解工作空间

## 常用命令

```bash
# 创建项目
cargo new project_name
cargo new --lib lib_name

# 构建
cargo build
cargo build --release
cargo build --all-targets

# 测试
cargo test
cargo test --doc
cargo test test_name

# 运行
cargo run
cargo run --release

# 检查
cargo check
cargo clippy
cargo fmt

# 文档
cargo doc
cargo doc --open

# 依赖管理
cargo add package_name
cargo update
cargo tree
```

## Cargo.toml 配置

```toml
[package]
name = "my_project"
version = "0.1.0"
edition = "2024"
rust-version = "1.94.0"

[dependencies]
serde = { version = "1.0", features = ["derive"] }
tokio = { version = "1.0", features = ["full"] }

[dev-dependencies]
mockall = "0.12"

[profile.release]
opt-level = 3
lto = true
```

---

**文档版本**: 1.0
**最后更新**: 2026-03-19
