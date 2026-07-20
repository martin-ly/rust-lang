# `--remap-path-scope` 完全指南

> **分级**: [A]
> **Bloom 层级**: L2 (理解)
> **稳定版本**: Rust 1.95.0
> **适用版本**: 1.95.0+

---

## 目录

- [`--remap-path-scope` 完全指南](#--remap-path-scope-完全指南)
  - [目录](#目录)
  - [一、什么是 `--remap-path-scope`](#一什么是---remap-path-scope)
    - [背景问题](#背景问题)
    - [解决方案演进](#解决方案演进)
  - [二、核心概念：路径重映射的作用域](#二核心概念路径重映射的作用域)
    - [默认行为](#默认行为)
  - [三、使用场景与示例](#三使用场景与示例)
    - [场景 1：可重现构建](#场景-1可重现构建)
    - [场景 2：发布产物脱敏](#场景-2发布产物脱敏)
    - [场景 3：Cargo 项目配置](#场景-3cargo-项目配置)
    - [场景 4：宏路径保护](#场景-4宏路径保护)
  - [四、与 `-Z remap-path-prefix` 的对比](#四与--z-remap-path-prefix-的对比)
    - [迁移示例](#迁移示例)
  - [五、常见配置模式](#五常见配置模式)
    - [模式 1：CI/CD 最小脱敏](#模式-1cicd-最小脱敏)
    - [模式 2：完全可重现构建](#模式-2完全可重现构建)
    - [模式 3：Docker 构建](#模式-3docker-构建)
  - [六、参考](#六参考)
    - [相关文档](#相关文档)

---

## 一、什么是 `--remap-path-scope`

> **[来源: Rust Compiler Documentation]**

`--remap-path-scope` 是 Rust 1.95.0 稳定化的编译器标志，用于**精确控制**哪些编译产物中的路径信息会被 `--remap-path-prefix` 规则重写。

### 背景问题

在 Rust 编译产物（二进制、debuginfo、panic 消息）中，编译器会嵌入源文件路径。这在以下场景中会造成问题：

- **可重现构建 (Reproducible Builds)**: 不同开发者的绝对路径不同，导致二进制哈希不一致
- **隐私保护**: 发布产物中可能包含开发者本地的目录结构
- **CI/CD**: 构建服务器上的临时路径不应泄露到最终产物

### 解决方案演进

| 阶段 | 机制 | 局限 |
|------|------|------|
| 早期 | `-Z remap-path-prefix` | 全局重写，无法精细控制 |
| **1.95+** | `--remap-path-scope` + `--remap-path-prefix` | **按作用域精确控制** |

---

## 二、核心概念：路径重映射的作用域

`--remap-path-scope` 接受一个逗号分隔的作用域列表，每个作用域控制一类编译产物中的路径：

| 作用域 | 影响的产物 | 典型用途 |
|--------|-----------|---------|
| `macro` | 宏展开中的 `file!()` | 消除宏定义的路径依赖 |
| `sym` | debuginfo 中的符号路径 | 保护构建环境隐私 |
| `dbginfo` | DWARF/PDB 调试信息 | 发布调试产物时脱敏 |
| `pathmapping` | 编译器内部路径映射 | 高级场景 |
| `unmapped` | 未被其他规则覆盖的路径 | 兜底处理 |
| `all` | 以上所有 | 一键脱敏 |

### 默认行为

如果不指定 `--remap-path-scope`，编译器使用 `--remap-path-prefix` 的**默认作用域**（通常是 `sym` 和 `dbginfo`）。

---

## 三、使用场景与示例

### 场景 1：可重现构建

```bash
# 将构建目录 /home/ci/build 映射为 /build，仅影响 debuginfo
rustc --remap-path-prefix=/home/ci/build=/build \
      --remap-path-scope=dbginfo \
      src/main.rs -o app
```

### 场景 2：发布产物脱敏

```bash
# 发布前构建：完全移除本地路径信息
rustc --remap-path-prefix=/home/user/projects/myapp=/project \
      --remap-path-scope=all \
      src/main.rs -o app
```

### 场景 3：Cargo 项目配置

在 `.cargo/config.toml` 中：

```toml
[build]
rustflags = [
    "--remap-path-prefix", "/home/user=/project",
    "--remap-path-scope", "all",
]
```

或在 `Cargo.toml` 中：

```toml
[profile.release]
rustflags = ["--remap-path-prefix=/home/user=/project", "--remap-path-scope=all"]
```

### 场景 4：宏路径保护

```bash
# 仅重映射宏展开中的 file!() 路径
rustc --remap-path-prefix=/home/user=/project \
      --remap-path-scope=macro \
      src/lib.rs
```

---

## 四、与 `-Z remap-path-prefix` 的对比

| 维度 | `-Z remap-path-prefix` (旧) | `--remap-path-scope` + `--remap-path-prefix` (1.95+) |
|------|---------------------------|---------------------------------------------------|
| **作用域控制** | 无（全局生效） | ✅ 精确控制 |
| **稳定性** | nightly-only | ✅ **stable** |
| **灵活性** | 低 | 高（可按产物类型选择） |
| **可重现构建** | 部分支持 | 完整支持 |
| **推荐度** | ❌ 已弃用 | ✅ 推荐使用 |

### 迁移示例

```bash
# 旧写法 (nightly)
rustc -Z remap-path-prefix=/home/user=/project src/main.rs

# 新写法 (1.95+ stable)
rustc --remap-path-prefix=/home/user=/project \
      --remap-path-scope=all \
      src/main.rs
```

---

## 五、常见配置模式

### 模式 1：CI/CD 最小脱敏

```bash
# 仅脱敏 debuginfo，保留 panic 消息中的路径
rustc --remap-path-prefix=$(pwd)=/build \
      --remap-path-scope=dbginfo,sym \
      src/main.rs
```

### 模式 2：完全可重现构建

```bash
# 所有路径信息统一映射
rustc --remap-path-prefix=$(pwd)=/build \
      --remap-path-prefix=$HOME=/home \
      --remap-path-scope=all \
      src/main.rs
```

### 模式 3：Docker 构建

```dockerfile
# Dockerfile
ENV RUSTFLAGS="--remap-path-prefix=/app=/project --remap-path-scope=all"
RUN cargo build --release
```

---

## 六、参考

> **[来源: Rust Compiler Documentation]**
> **[来源: Rust Release Notes]**

| 资源 | 链接 |
|------|------|
| Rust 1.95.0 Release Notes | <https://releases.rs/docs/1.95.0/> |
| rustc 路径重映射文档 | <https://doc.rust-lang.org/rustc/command-line-arguments.html> |
| Reproducible Builds 项目 | <https://reproducible-builds.org/> |

### 相关文档

- [Rust 1.95 特性速查表](../../../../docs/02_reference/quick_reference/02_rust_195_features_cheatsheet.md)
- [Rust 版本跟踪](../../../../concept/07_future/00_version_tracking/05_rust_version_tracking.md)
- [Rust 1.96 稳定特性全景](../../../../docs/06_toolchain/06_19_rust_1_96_features.md)
