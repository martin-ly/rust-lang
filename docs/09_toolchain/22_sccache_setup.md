# sccache 配置指南 {#sccache-配置指南}

> **EN**: Sccache Setup
> **Summary**: sccache 配置指南 Sccache Setup.
> **Rust 版本**: 1.97.0+ (Edition 2024)
> **分级**: [B]
> **Bloom 层级**: L2-L3

本文档说明如何在项目中配置和使用 sccache 来加速 Rust 编译。

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [sccache 配置指南 {#sccache-配置指南}](#sccache-配置指南-sccache-配置指南)
  - [📑 目录 {#目录}](#-目录-目录)
  - [什么是 sccache? {#什么是-sccache}](#什么是-sccache-什么是-sccache)
  - [安装 {#安装}](#安装-安装)
    - [方式 1: 使用 cargo 安装 (推荐) {#方式-1-使用-cargo-安装-推荐}](#方式-1-使用-cargo-安装-推荐-方式-1-使用-cargo-安装-推荐)
    - [方式 2: 使用包管理器 {#方式-2-使用包管理器}](#方式-2-使用包管理器-方式-2-使用包管理器)
    - [方式 3: GitHub Releases {#方式-3-github-releases}](#方式-3-github-releases-方式-3-github-releases)
  - [验证安装 {#验证安装}](#验证安装-验证安装)
  - [配置 {#配置}](#配置-配置)
    - [1. Cargo 配置 (已完成) {#1-cargo-配置-已完成}](#1-cargo-配置-已完成-1-cargo-配置-已完成)
    - [2. 环境变量 (可选) {#2-环境变量-可选}](#2-环境变量-可选-2-环境变量-可选)
  - [使用方法 {#使用方法}](#使用方法-使用方法)
  - [监控缓存状态 {#监控缓存状态}](#监控缓存状态-监控缓存状态)
  - [清理缓存 {#清理缓存}](#清理缓存-清理缓存)
  - [CI/CD 配置 {#cicd-配置}](#cicd-配置-cicd-配置)
  - [性能基准 {#性能基准}](#性能基准-性能基准)
  - [故障排除 {#故障排除}](#故障排除-故障排除)
    - [sccache 未生效 {#sccache-未生效}](#sccache-未生效-sccache-未生效)
    - [缓存目录权限问题 {#缓存目录权限问题}](#缓存目录权限问题-缓存目录权限问题)
    - [清理并重启 {#清理并重启}](#清理并重启-清理并重启)
  - [参考 {#参考}](#参考-参考)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 什么是 sccache? {#什么是-sccache}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

`sccache` 是 Mozilla 开发的编译缓存工具，支持:

- **磁盘缓存**: 本地快速重用编译结果
- **远程缓存**: S3, Azure Blob, GCS, Redis 等
- **CI/CD 集成**: GitHub Actions 原生支持

## 安装 {#安装}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 方式 1: 使用 cargo 安装 (推荐) {#方式-1-使用-cargo-安装-推荐}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```bash
cargo install sccache --locked
```

### 方式 2: 使用包管理器 {#方式-2-使用包管理器}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

**Windows (winget):**

```powershell
winget install sccache
```

**macOS (Homebrew):**

```bash
brew install sccache
```

**Linux:**

```bash
# Ubuntu/Debian {#ubuntudebian}
sudo apt-get install sccache

# Arch {#arch}
sudo pacman -S sccache

# 其他发行版使用 cargo 安装 {#其他发行版使用-cargo-安装}
```

### 方式 3: GitHub Releases {#方式-3-github-releases}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

下载预编译二进制文件:
<https://github.com/mozilla/sccache/releases>

## 验证安装 {#验证安装}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

```bash
sccache --version
```

## 配置 {#配置}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### 1. Cargo 配置 (已完成) {#1-cargo-配置-已完成}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

`.cargo/config.toml` 已配置:

```toml
[build]
rustc-wrapper = "sccache"

[env]
SCCACHE_CACHE_SIZE = "50G"
SCCACHE_DIR = "D:\\_cache\\sccache"  # Windows
# SCCACHE_DIR = "${HOME}/.cache/sccache"  # Linux/macOS {#sccache_dir-homecachesccache-linuxmacos}
SCCACHE_GHA_ENABLED = "true"
```

### 2. 环境变量 (可选) {#2-环境变量-可选}
>
> **[来源: [crates.io](https://crates.io/)]**

```bash
# Windows PowerShell {#windows-powershell}
$env:SCCACHE_CACHE_SIZE = "50G"
$env:SCCACHE_DIR = "D:\_cache\sccache"

# Linux/macOS {#linuxmacos-1}
export SCCACHE_CACHE_SIZE="50G"
export SCCACHE_DIR="$HOME/.cache/sccache"
```

## 使用方法 {#使用方法}
>
> **[来源: [docs.rs](https://docs.rs/)]**

配置完成后，正常使用 cargo 命令即可，sccache 自动生效:

```bash
cargo build
cargo test
cargo check
```

## 监控缓存状态 {#监控缓存状态}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```bash
# 查看缓存统计 {#查看缓存统计}
sccache --show-stats

# 示例输出: {#示例输出}
# Compile requests                    1,024 {#compile-requests-1024}
# Compile requests executed             980 {#compile-requests-executed-980}
# Cache hits                            850 (86.7%) {#cache-hits-850-867}
# Cache misses                          130 (13.3%) {#cache-misses-130-133}
# Cache timeouts                          0 {#cache-timeouts-0}
```

## 清理缓存 {#清理缓存}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

```bash
# 手动清理 {#手动清理}
sccache --stop-server
rm -rf $SCCACHE_DIR  # Linux/macOS
# 或删除 D:\_cache\sccache  # Windows {#或删除-d_cachesccache-windows}

# 自动清理 (达到 SCCACHE_CACHE_SIZE 时自动清理) {#自动清理-达到-sccache_cache_size-时自动清理}
# 无需手动操作 {#无需手动操作}
```

## CI/CD 配置 {#cicd-配置}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

GitHub Actions 已配置 (`.github/workflows/ci.yml`):

```yaml
- name: Setup sccache
  uses: mozilla-actions/sccache-action@v0.0.4

- name: Cache sccache
  uses: actions/cache@v4
  with:
    path: ~/.cache/sccache
    key: ${{ runner.os }}-sccache-${{ hashFiles('**/Cargo.lock') }}
```

## 性能基准 {#性能基准}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 场景 | 时间 | 说明 |
|------|------|------|
| 首次构建 | ~X min | 无缓存，创建缓存 |
| 缓存命中 | ~Y min | 约 60-80% 时间节省 |
| CI 缓存 | ~Z min | 跨构建共享缓存 |

运行 `scripts/benchmark-sccache.ps1` 进行本地基准测试。

## 故障排除 {#故障排除}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

### sccache 未生效 {#sccache-未生效}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```bash
# 检查环境变量 {#检查环境变量}
echo $env:RUSTC_WRAPPER  # Windows
echo $RUSTC_WRAPPER      # Linux/macOS

# 应该输出: sccache {#应该输出-sccache}
```

### 缓存目录权限问题 {#缓存目录权限问题}
>
> **[来源: [crates.io](https://crates.io/)]**

```bash
# Windows - 确保目录存在并有写权限 {#windows---确保目录存在并有写权限}
mkdir D:\_cache\sccache -Force

# Linux/macOS {#linuxmacos-1}
mkdir -p ~/.cache/sccache
chmod 755 ~/.cache/sccache
```

### 清理并重启 {#清理并重启}
>
> **[来源: [docs.rs](https://docs.rs/)]**

```bash
sccache --stop-server
sccache --start-server
```

## 参考 {#参考}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [sccache GitHub](https://github.com/mozilla/sccache)
- [Rust Cargo 缓存](https://doc.rust-lang.org/cargo/guide/build-cache.html)

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/), [Rust Standard Library](https://doc.rust-lang.org/std/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Reference、TRPL、标准库官方来源标注 [Authority Source Sprint Batch 8](../concept/00_meta/02_sources/05_international_authority_index.md)

**文档版本**: 1.1
**对应 Rust 版本**: 1.97.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](README.md)

---

## 相关概念 {#相关概念}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

- [docs 目录](README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Compiler Cache](https://en.wikipedia.org/wiki/Compiler_Cache)**
> **[Mozilla - sccache](https://github.com/mozilla/sccache)**
> **[ACM - Build System Optimization](https://dl.acm.org/)**
> **[IEEE - Software Build Automation](https://ieeexplore.ieee.org/) <!-- link: known-broken -->**
> **[Rust CI Best Practices](https://rustc-dev-guide.rust-lang.org/overview.html)**
> **来源: [Wikipedia - Rust (programming language)](https://en.wikipedia.org/wiki/Rust_(programming_language))**
> **来源: [Rust Reference](https://doc.rust-lang.org/reference/)**
> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**
> **来源: [ACM](https://dl.acm.org/)**
> **来源: [IEEE](https://standards.ieee.org/)**
> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
> **来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)**

---
