# Packaging - 打包工具

## 📋 目录

- [概述](#概述)
- [二进制打包](#二进制打包)
- [库打包](#库打包)

---

## 概述

Rust 项目的打包、分发和版本管理工具。

---

## 二进制打包

### cargo-bundle

```toml
# Cargo.toml
[package.metadata.bundle]
name = "My App"
identifier = "com.example.myapp"
icon = ["icon.png"]
version = "1.0.0"
resources = ["assets/*"]
copyright = "Copyright (c) 2024"
```

```bash
# 安装
cargo install cargo-bundle

# 打包
cargo bundle --release
```

### cargo-deb (Debian 包)

```toml
# Cargo.toml
[package.metadata.deb]
maintainer = "Your Name <you@example.com>"
copyright = "2024, Your Name"
license-file = ["LICENSE", "4"]
extended-description = """\
My application description."""
depends = "$auto"
section = "utility"
priority = "optional"
assets = [
    ["target/release/my-app", "usr/bin/", "755"],
    ["README.md", "usr/share/doc/my-app/", "644"],
]
```

```bash
# 安装
cargo install cargo-deb

# 构建 .deb 包
cargo deb
```

---

## 库打包

### 发布到 crates.io

```bash
# 登录
cargo login <your-api-token>

# 打包检查
cargo package --list
cargo package --allow-dirty

# 发布
cargo publish
```

### Cargo.toml 最佳实践

```toml
[package]
name = "my-crate"
version = "0.1.0"
authors = ["Your Name <you@example.com>"]
edition = "2021"
license = "MIT OR Apache-2.0"
description = "A short description"
repository = "https://github.com/username/repo"
documentation = "https://docs.rs/my-crate"
homepage = "https://example.com"
readme = "README.md"
keywords = ["keyword1", "keyword2"]
categories = ["category1"]

[package.metadata.docs.rs]
all-features = true
rustdoc-args = ["--cfg", "docsrs"]
```

---

## 跨平台打包

### cross (交叉编译)

```bash
# 安装
cargo install cross

# 交叉编译
cross build --target x86_64-unknown-linux-musl
cross build --target aarch64-unknown-linux-gnu
cross build --target x86_64-pc-windows-gnu
```

---

## 参考资源

- [Cargo Book - Publishing](https://doc.rust-lang.org/cargo/reference/publishing.html)
- [cargo-bundle GitHub](https://github.com/burtonageo/cargo-bundle)
- [cargo-deb GitHub](https://github.com/kornelski/cargo-deb)

