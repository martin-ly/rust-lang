# 包管理（Package Management）

## 1. 工程原理与定义（Principle & Definition）

包管理是指通过工具自动化管理依赖、版本、发布和分发，提升软件复用性和可维护性。Rust 以cargo为核心，支持高效的包管理和依赖生态。
Package management refers to automating dependency, version, publishing, and distribution management via tools, improving software reusability and maintainability. Rust uses cargo as its core, supporting efficient package management and a rich dependency ecosystem.

## 2. Rust 1.88 新特性工程化应用

- cargo add/remove：命令行依赖管理。
- cargo publish/upgrade：自动化包发布与升级。
- cargo-audit：依赖安全检测。

## 3. 典型场景与最佳实践（Typical Scenarios & Best Practices）

- 用cargo add/remove管理依赖。
- 用cargo publish发布库到crates.io。
- 用cargo upgrade自动升级依赖。
- 用cargo-audit检测依赖安全。

**最佳实践：**

- 用cargo统一依赖与包管理。
- 用cargo-audit定期检测依赖安全。
- 用cargo upgrade保持依赖最新。
- 用CI集成自动化依赖检测。

## 4. 常见问题 FAQ

- Q: Rust如何管理依赖？
  A: 用cargo add/remove命令自动管理依赖。
- Q: 如何发布Rust库？
  A: 用cargo publish发布到crates.io。
- Q: 如何做依赖安全检测？
  A: 用cargo-audit自动检测依赖漏洞。

## 5. 参考与扩展阅读

- [cargo 官方文档](https://doc.rust-lang.org/cargo/)
- [cargo-audit 依赖安全检测](https://github.com/rustsec/rustsec/tree/main/cargo-audit)
- [crates.io 包仓库](https://crates.io/)
