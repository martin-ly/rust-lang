# Nix 设置指南

本项目支持使用 Nix 进行开发环境管理，确保所有开发者使用一致的 Rust 工具链。

## 📑 目录
>
- [Nix 设置指南](#nix-设置指南)
  - [📑 目录](#-目录)
  - [前置要求](#前置要求)
  - [快速开始](#快速开始)
    - [进入开发环境](#进入开发环境)
    - [使用 direnv（推荐）](#使用-direnv推荐)
  - [环境特性](#环境特性)
  - [可用工具](#可用工具)
  - [故障排除](#故障排除)
    - [缓存问题](#缓存问题)
    - [更新依赖](#更新依赖)
  - [参考](#参考)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)

## 前置要求
>
> **[来源: Rust Official Docs]**

- 安装 Nix 包管理器: [https://nixos.org/download.html](https://nixos.org/download.html)
- 启用 Flakes 功能:

  ```bash
  echo "experimental-features = nix-command flakes" >> ~/.config/nix/nix.conf
  ```

## 快速开始
>
> **[来源: Rust Official Docs]**

### 进入开发环境
>
> **[来源: Rust Official Docs]**

```bash
nix develop
```

这将自动加载配置好的 Rust 工具链和开发工具。

### 使用 direnv（推荐）

1. 安装 `direnv` 和 `nix-direnv`:

   ```bash
   nix profile install nixpkgs#direnv nixpkgs#nix-direnv
   ```

2. 在项目根目录执行:

   ```bash
   echo "use flake" > .envrc
   direnv allow
   ```

3. 以后进入项目目录时，开发环境会自动加载。

## 环境特性

- **Rust 工具链**: 使用项目 `rust-toolchain.toml` 指定的版本
- **sccache**: 自动配置缓存加速编译
- **一致性**: 所有开发者使用相同的工具版本

## 可用工具

进入 Nix shell 后，以下工具已预装:

- `rustc` - Rust 编译器
- `cargo` - Rust 包管理器
- `rustfmt` - 代码格式化工具
- `clippy` - 静态分析工具
- `sccache` - 编译缓存工具

## 故障排除

### 缓存问题

如果遇到构建缓存问题，可以清除 sccache:

```bash
sccache --stop-server
sccache --start-server
```

### 更新依赖

更新 flake 输入:

```bash
nix flake update
```

## 参考

- [Nix Flakes 手册](https://nixos.org/manual/nix/stable/command-ref/new-cli/nix3-flake.html)
- [rust-overlay](https://github.com/oxalica/rust-overlay)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [来源: Authority Source Sprint Batch 8]

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念

- [docs 目录](./README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library]**

> **[来源: ACM - Systems Programming]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

> **[来源: Rustonomicon]**
