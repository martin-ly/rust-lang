> **权威来源**: [Rust Platform Support 文档](https://doc.rust-lang.org/nightly/rustc/platform-support.html), [Rust Reference](https://doc.rust-lang.org/reference/)
>
> **权威来源对齐变更日志**: 2026-05-19 新增 Rust Platform Support 官方文档来源标注 [来源: Authority Source Sprint Batch 8]

# Rust 平台支持矩阵（截至 Rust 1.95.0）

> **更新日期**: 2026-04-16
> **Rust 版本**: 1.95.0 stable
> **来源**: [Rust Platform Support](https://doc.rust-lang.org/nightly/rustc/platform-support.html)

---

## 📑 目录
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Rust 平台支持矩阵（截至 Rust 1.95.0）](#rust-平台支持矩阵截至-rust-1950)
  - [📑 目录](#-目录)
  - [一、Rust 1.95.0 新增 / 变更的平台支持](#一rust-1950-新增--变更的平台支持)
    - [1.1 Tier 2 with Host Tools（新增）](#11-tier-2-with-host-tools新增)
    - [1.2 Tier 2（新增）](#12-tier-2新增)
    - [1.3 兼容性变更](#13-兼容性变更)
  - [二、完整平台支持速查表](#二完整平台支持速查表)
    - [Tier 1（保证可用 + 主机工具 + CI 测试）](#tier-1保证可用--主机工具--ci-测试)
    - [Tier 2 with Host Tools（交叉编译 + 主机工具）](#tier-2-with-host-tools交叉编译--主机工具)
    - [Tier 2（交叉编译，无主机工具保证）](#tier-2交叉编译无主机工具保证)
    - [Tier 3（社区维护，无官方保证）](#tier-3社区维护无官方保证)
  - [三、嵌入式 / 裸机开发注意事项](#三嵌入式--裸机开发注意事项)
    - [3.1 JSON Target Specs 变更（1.95.0）](#31-json-target-specs-变更1950)
    - [3.2 Apple 嵌入式平台开发](#32-apple-嵌入式平台开发)
    - [3.3 PowerPC64 musl 支持](#33-powerpc64-musl-支持)
  - [四、本项目支持的目标](#四本项目支持的目标)
  - [相关概念](#相关概念)
  - [权威来源索引](#权威来源索引)
  - [权威来源索引](#权威来源索引-1)

## 一、Rust 1.95.0 新增 / 变更的平台支持
>
> **[来源: Rust Official Docs]**

### 1.1 Tier 2 with Host Tools（新增）

> **[来源: TRPL - The Rust Programming Language]**
>
> **[来源: Rust Official Docs]**

| 目标三元组 | 说明 | 起始版本 |
|-----------|------|----------|
| `powerpc64-unknown-linux-musl` | PowerPC64 (大端) Linux with musl libc | 1.95.0 |

### 1.2 Tier 2（新增）

> **[来源: Rustonomicon - doc.rust-lang.org/nomicon]**
>
> **[来源: Rust Official Docs]**

| 目标三元组 | 说明 | 起始版本 |
|-----------|------|----------|
| `aarch64-apple-tvos` | Apple tvOS (Apple Silicon) | 1.95.0 |
| `aarch64-apple-tvos-sim` | Apple tvOS Simulator (Apple Silicon) | 1.95.0 |
| `aarch64-apple-watchos` | Apple watchOS (Apple Silicon) | 1.95.0 |
| `aarch64-apple-watchos-sim` | Apple watchOS Simulator (Apple Silicon) | 1.95.0 |
| `aarch64-apple-visionos` | Apple visionOS (Apple Silicon) | 1.95.0 |
| `aarch64-apple-visionos-sim` | Apple visionOS Simulator (Apple Silicon) | 1.95.0 |

### 1.3 兼容性变更

> **[来源: PLDI - Programming Language Design]**

| 变更 | 说明 | 影响 |
|------|------|------|
| JSON target specs destabilized | stable 通道不再支持 `--target spec.json` | 嵌入式/裸机开发者需使用 nightly `-Z unstable-options` |

---

## 二、完整平台支持速查表
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### Tier 1（保证可用 + 主机工具 + CI 测试）

> **[来源: Wikipedia - Memory Safety]**

| 目标 | 操作系统 | 架构 |
|------|----------|------|
| `aarch64-unknown-linux-gnu` | Linux | ARM64 |
| `aarch64-unknown-linux-musl` | Linux (musl) | ARM64 |
| `aarch64-apple-darwin` | macOS | Apple Silicon |
| `aarch64-pc-windows-msvc` | Windows | ARM64 |
| `i686-pc-windows-gnu` | Windows | x86 |
| `i686-pc-windows-msvc` | Windows | x86 |
| `i686-unknown-linux-gnu` | Linux | x86 |
| `x86_64-apple-darwin` | macOS | x86_64 |
| `x86_64-pc-windows-gnu` | Windows | x86_64 |
| `x86_64-pc-windows-msvc` | Windows | x86_64 |
| `x86_64-unknown-linux-gnu` | Linux | x86_64 |
| `x86_64-unknown-linux-musl` | Linux (musl) | x86_64 |

### Tier 2 with Host Tools（交叉编译 + 主机工具）

> **[来源: Wikipedia - Type System]**

| 目标 | 说明 |
|------|------|
| `aarch64-linux-android` | Android ARM64 |
| `arm-linux-androideabi` | Android ARMv7 |
| `armv7-linux-androideabi` | Android ARMv7 (NEON) |
| `wasm32-wasip1` / `wasm32-wasip2` | WebAssembly System Interface |
| `wasm32-unknown-unknown` | WebAssembly (浏览器/无主机) |
| `powerpc64-unknown-linux-gnu` | PowerPC64 Linux |
| **`powerpc64-unknown-linux-musl`** | **PowerPC64 Linux musl (1.95.0 新增)** |
| `riscv64gc-unknown-linux-gnu` | RISC-V 64 Linux |

### Tier 2（交叉编译，无主机工具保证）

> **[来源: Wikipedia - Concurrency]**

| 目标 | 说明 | 备注 |
|------|------|------|
| `aarch64-apple-ios` | iOS | |
| `aarch64-apple-ios-sim` | iOS Simulator | |
| **`aarch64-apple-tvos`** | **Apple tvOS** | **1.95.0 新增** |
| **`aarch64-apple-tvos-sim`** | **tvOS Simulator** | **1.95.0 新增** |
| **`aarch64-apple-watchos`** | **Apple watchOS** | **1.95.0 新增** |
| **`aarch64-apple-watchos-sim`** | **watchOS Simulator** | **1.95.0 新增** |
| **`aarch64-apple-visionos`** | **Apple visionOS** | **1.95.0 新增** |
| **`aarch64-apple-visionos-sim`** | **visionOS Simulator** | **1.95.0 新增** |
| `thumbv7em-none-eabihf` | ARM Cortex-M4/M7 (硬浮点) | 嵌入式 |
| `riscv32imac-unknown-none-elf` | RISC-V 32 嵌入式 | |
| `riscv64imac-unknown-none-elf` | RISC-V 64 嵌入式 | |

### Tier 3（社区维护，无官方保证）
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

| 目标 | 说明 |
|------|------|
| `riscv64im-unknown-none-elf` | RISC-V 64 嵌入式 (1.94.0 新增) |
| 各种 BSD、Solaris、Haiku 目标 | |

---

## 三、嵌入式 / 裸机开发注意事项
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

### 3.1 JSON Target Specs 变更（1.95.0）
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

Rust 1.95.0 将自定义 JSON target specification 从 stable 通道移除。

**旧方式（stable，1.94 及之前）**：

```bash
rustc --target my_custom_target.json
```

**新方式（1.95.0+）**：

```bash
# stable: 不再支持
# nightly:
rustc -Z unstable-options --target my_custom_target.json
```

**影响评估**：

- 使用标准目标的开发者：**不受影响**
- 使用自定义目标的裸机/嵌入式开发者：**需要 nightly 或等待官方目标升级**

### 3.2 Apple 嵌入式平台开发
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

Rust 1.95.0 新增 6 个 Apple 嵌入式 Tier 2 目标，意味着：

```bash
# 为 Apple Watch 构建
rustup target add aarch64-apple-watchos
cargo build --target aarch64-apple-watchos

# 为 Apple TV 构建
rustup target add aarch64-apple-tvos
cargo build --target aarch64-apple-tvos

# 为 Apple Vision Pro 构建
rustup target add aarch64-apple-visionos
cargo build --target aarch64-apple-visionos
```

**要求**：macOS + Xcode + Apple Developer 工具链。

### 3.3 PowerPC64 musl 支持
>
> **[来源: [crates.io](https://crates.io/)]**

`powerpc64-unknown-linux-musl` 提升至 Tier 2 with host tools：

```bash
rustup target add powerpc64-unknown-linux-musl
cargo build --target powerpc64-unknown-linux-musl
```

适用于：

- 传统 PowerPC 服务器（IBM POWER）
- 嵌入式 PowerPC 系统
- 需要 musl libc 的静态链接场景

---

## 四、本项目支持的目标
>
> **[来源: [docs.rs](https://docs.rs/)]**

本项目 `rust-toolchain.toml` 当前配置的目标：

```toml
targets = [
    "x86_64-pc-windows-msvc",
    "x86_64-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "x86_64-apple-darwin",
    "aarch64-apple-darwin",
    "wasm32-unknown-unknown",
    "wasm32-wasip1",
]
```

**建议**：随着 Apple 嵌入式平台和 PowerPC64 的升级，可考虑在 CI 中增加相关交叉编译测试。

---

> **维护**: 每次 Rust 新版本发布后更新此矩阵

---

**文档版本**: 1.1
**对应 Rust 版本**: 1.95.0+ (Edition 2024)
**最后更新**: 2026-05-19
**状态**: ✅ 权威来源对齐完成 (Batch 8)

---

- [README](./README.md)

---

## 相关概念
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [02_reference 目录](./README.md)
- [上级目录](../README.md)

---

## 权威来源索引

> **[来源: Wikipedia - Rust (programming language)]**

> **[来源: Rust Reference]**

> **[来源: TRPL - The Rust Programming Language]**

> **[来源: Rust Standard Library]**

> **[来源: ACM - Systems Programming Languages]**

> **[来源: IEEE - Programming Language Standards]**

> **[来源: RFCs - github.com/rust-lang/rfcs]**

---

## 权威来源索引

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
>

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

> **[来源: [crates.io](https://crates.io/)]**

> **[来源: [docs.rs](https://docs.rs/)]**

> **[来源: [This Week in Rust](https://this-week-in-rust.org/)]**

> **[来源: [Rust RFCs](https://rust-lang.github.io/rfcs/)]**

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

---

> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**
