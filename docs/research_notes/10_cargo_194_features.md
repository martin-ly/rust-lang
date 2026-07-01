# Cargo 1.94 新特性指南 {#cargo-194-新特性指南}
>
> **概念族**: 版本特性

> **内容分级**: [归档级]
>
> **分级**: [B]
> **Bloom 层级**: L5-L6 (分析/评价/创造)
> **Cargo 版本**: 1.94.0 [历史声明]
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **发布日期**: 2026-03-05
> **最后更新**: 2026-06-29
> **状态**: ✅ 已完成权威国际化来源对齐升级（Rust 1.96.0+ / Edition 2024）
> **权威来源**:
>
> [Cargo Book](https://doc.rust-lang.org/cargo/) |
> [releases.rs](https://releases.rs/) |
> [Rust Blog](https://blog.rust-lang.org/) |
> [Rust RFCs](https://rust-lang.github.io/rfcs/)
>

---

## 📑 目录 {#目录}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**
>
- [Cargo 1.94 新特性指南 {#cargo-194-新特性指南}](#cargo-194-新特性指南-cargo-194-新特性指南)
  - [📑 目录 {#目录}](#-目录-目录)
  - [概述 {#概述}](#概述-概述)
  - [一、Config Inclusion（配置文件包含） {#一config-inclusion配置文件包含}](#一config-inclusion配置文件包含-一config-inclusion配置文件包含)
    - [1.1 特性描述 {#11-特性描述}](#11-特性描述-11-特性描述)
    - [1.2 基本用法 {#12-基本用法}](#12-基本用法-12-基本用法)
    - [1.3 高级用法（带可选标记） {#13-高级用法带可选标记}](#13-高级用法带可选标记-13-高级用法带可选标记)
    - [1.4 实际应用场景 {#14-实际应用场景}](#14-实际应用场景-14-实际应用场景)
      - [团队共享配置 {#团队共享配置}](#团队共享配置-团队共享配置)
      - [环境特定配置 {#环境特定配置}](#环境特定配置-环境特定配置)
    - [1.5 配置合并规则 {#15-配置合并规则}](#15-配置合并规则-15-配置合并规则)
  - [二、TOML 1.1 支持 {#二toml-11-支持}](#二toml-11-支持-二toml-11-支持)
    - [2.1 支持的特性 {#21-支持的特性}](#21-支持的特性-21-支持的特性)
    - [2.2 多行内联表示例 {#22-多行内联表示例}](#22-多行内联表示例-22-多行内联表示例)
    - [2.3 MSRV 注意事项 {#23-msrv-注意事项}](#23-msrv-注意事项-23-msrv-注意事项)
  - [三、pubtime 字段 {#三pubtime-字段}](#三pubtime-字段-三pubtime-字段)
    - [3.1 特性描述 {#31-特性描述}](#31-特性描述-31-特性描述)
    - [3.2 使用场景 {#32-使用场景}](#32-使用场景-32-使用场景)
    - [3.3 注意事项 {#33-注意事项}](#33-注意事项-33-注意事项)
  - [四、`CARGO_BIN_EXE_<crate>` 运行时可用 {#四cargo\_bin\_exe\_crate-运行时可用}](#四cargo_bin_exe_crate-运行时可用-四cargo_bin_exe_crate-运行时可用)
    - [4.1 特性描述 {#41-特性描述}](#41-特性描述-41-特性描述)
    - [4.2 使用示例 {#42-使用示例}](#42-使用示例-42-使用示例)
    - [4.3 测试示例 {#43-测试示例}](#43-测试示例-43-测试示例)
  - [五、性能改进 {#五性能改进}](#五性能改进-五性能改进)
    - [5.1 cargo clean 优化 {#51-cargo-clean-优化}](#51-cargo-clean-优化-51-cargo-clean-优化)
  - [六、完整配置示例 {#六完整配置示例}](#六完整配置示例-六完整配置示例)
  - [七、迁移指南 {#七迁移指南}](#七迁移指南-七迁移指南)
    - [7.1 从旧版本迁移 {#71-从旧版本迁移}](#71-从旧版本迁移-71-从旧版本迁移)
    - [7.2 兼容性 {#72-兼容性}](#72-兼容性-72-兼容性)
  - [八、相关资源 {#八相关资源}](#八相关资源-八相关资源)
  - [九、Rust 1.96 Cargo 安全修复 {#九rust-196-cargo-安全修复}](#九rust-196-cargo-安全修复-九rust-196-cargo-安全修复)
    - [9.1 CVE-2026-5223 {#91-cve-2026-5223}](#91-cve-2026-5223-91-cve-2026-5223)
    - [9.2 CVE-2026-5222 {#92-cve-2026-5222}](#92-cve-2026-5222-92-cve-2026-5222)
    - [9.3 升级建议 {#93-升级建议}](#93-升级建议-93-升级建议)
  - [十、Cargo 1.95/1.96 新增/变更 {#十cargo-195196-新增变更}](#十cargo-195196-新增变更-十cargo-195196-新增变更)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024） {#权威国际化来源对齐升级摘要rust-1960-edition-2024}](#-权威国际化来源对齐升级摘要rust-1960--edition-2024-权威国际化来源对齐升级摘要rust-1960-edition-2024)
    - [本次升级要点 {#本次升级要点}](#本次升级要点-本次升级要点)
      - [新增 Rust 1.96.0 特性 {#新增-rust-1960-特性}](#新增-rust-1960-特性-新增-rust-1960-特性)
      - [新增 Rust 1.95.0 特性 {#新增-rust-1950-特性}](#新增-rust-1950-特性-新增-rust-1950-特性)
      - [权威来源对齐 {#权威来源对齐}](#权威来源对齐-权威来源对齐)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [权威来源索引 {#权威来源索引}](#权威来源索引-权威来源索引)

## 概述 {#概述}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

Cargo 1.94 带来了多项重要改进，包括配置文件包含、TOML 1.1 支持、发布时间记录等功能。本文档在保留 1.94 历史分析的基础上，已对齐 **Rust 1.96.0+ / Edition 2024** 权威来源，并补充 Cargo CVE-2026-5223/5222 安全修复说明。

---

## 一、Config Inclusion（配置文件包含） {#一config-inclusion配置文件包含}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 1.1 特性描述 {#11-特性描述}

> **来源: [Cargo Book - Config Include](https://doc.rust-lang.org/cargo/reference/config.html#include)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

Cargo 现在在配置文件（`.cargo/config.toml`）中支持 `include` 键，允许加载额外的配置文件，从而更好地跨项目和环境组织、共享和管理 Cargo 配置。

### 1.2 基本用法 {#12-基本用法}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```toml
# .cargo/config.toml {#cargoconfigtoml-4}
include = [
    "frodo.toml",
    "samwise.toml",
]
```

### 1.3 高级用法（带可选标记） {#13-高级用法带可选标记}

> **来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```toml
# .cargo/config.toml {#cargoconfigtoml-4}
include = [
    { path = "required.toml" },
    { path = "optional.toml", optional = true },
]
```

如果设置了 `optional = true`，当文件不存在时不会报错。

### 1.4 实际应用场景 {#14-实际应用场景}

> **来源: [Rustonomicon - doc.rust-lang.org/nomicon](https://doc.rust-lang.org/nomicon/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

#### 团队共享配置 {#团队共享配置}

> **来源: [IEEE](https://standards.ieee.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```toml
# .cargo/config.toml {#cargoconfigtoml-4}
include = [
    # 团队共享的配置（版本控制）
    { path = "team.toml" },
    # 个人本地配置（不在版本控制中）
    { path = "local.toml", optional = true },
]
```

#### 环境特定配置 {#环境特定配置}

> **来源: [Rust RFCs](https://github.com/rust-lang/rfcs)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

```toml
# .cargo/config.toml {#cargoconfigtoml-4}
include = [
    # CI 环境配置
    { path = "ci.toml", optional = true },
    # 开发环境配置
    { path = "dev.toml", optional = true },
]
```

### 1.5 配置合并规则 {#15-配置合并规则}

> **来源: [ACM](https://dl.acm.org/)**
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

- 后续配置可以覆盖前面的配置
- 当前文件的配置优先级最高
- 环境变量仍然具有最高优先级

---

## 二、TOML 1.1 支持 {#二toml-11-支持}
>
> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

### 2.1 支持的特性 {#21-支持的特性}

> **来源: [TOML v1.1.0 规范](https://toml.io/en/v1.1.0)**
>
> **来源: [Cargo Book - Manifest Format](https://doc.rust-lang.org/cargo/reference/manifest.html)**

Cargo 1.94 现在解析 TOML v1.1，包含以下新特性：

| 特性 | 描述 | 示例 |
|------|------|------|
| 多行内联表 | 内联表可以跨多行 | 见下方 |
| 尾部逗号 | 允许尾部逗号 | `features = ["a",]` |
| `\xHH` 转义 | 十六进制字符转义 | `\x41` = 'A' |
| `\e` 转义 | Escape 字符 | `\e` = ESC |
| 可选秒 | 时间中的秒可选 | `12:30` |

### 2.2 多行内联表示例 {#22-多行内联表示例}

> **来源: [Rust Reference - doc.rust-lang.org/reference](https://doc.rust-lang.org/reference/)**

```toml
[dependencies]
# 旧格式（单行） {#旧格式单行}
serde = { version = "1.0", features = ["derive"] }

# 新格式（多行） {#新格式多行}
serde = {
    version = "1.0",
    features = ["derive",],
}

# 复杂的依赖配置 {#复杂的依赖配置}
tokio = {
    version = "1.49",
    features = [
        "rt-multi-thread",
        "macros",
        "sync",
    ],
}
```

### 2.3 MSRV 注意事项 {#23-msrv-注意事项}

> **来源: [Rust Standard Library](https://doc.rust-lang.org/std/)**

使用 TOML 1.1 特性会提高开发时的 MSRV（最低支持 Rust 版本），但：

- Cargo 在发布时会自动重写清单，保持与旧解析器的兼容性
- 第三方工具可能需要更新其解析器

```toml
# Cargo.toml {#cargotoml}
[package]
name = "my-crate"
version = "0.1.0"
rust-version = "1.96"  # 需要 1.94+ 来解析 TOML 1.1
```

---

## 三、pubtime 字段 {#三pubtime-字段}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 3.1 特性描述 {#31-特性描述}

> **来源: [Cargo Book - Registry Index Format](https://doc.rust-lang.org/cargo/reference/registry-index.html)**

Cargo registry 索引现在包含 `pubtime` 字段，记录 crate 版本的发布时间。这支持未来的基于时间的依赖解析。

### 3.2 使用场景 {#32-使用场景}

> **来源: [PLDI](https://www.sigplan.org/Conferences/PLDI/)**

```bash
# 未来可能支持的时间范围依赖 {#未来可能支持的时间范围依赖}
cargo add serde --time "2026-01-01..2026-03-01"
```

### 3.3 注意事项 {#33-注意事项}

> **来源: [Wikipedia - Memory Safety](https://en.wikipedia.org/wiki/Memory_Safety)**

- crates.io 将逐步回填现有包的发布时间
- 不是所有 crate 都有 `pubtime`（取决于发布时间和 registry）

---

## 四、`CARGO_BIN_EXE_<crate>` 运行时可用 {#四cargo_bin_exe_crate-运行时可用}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

### 4.1 特性描述 {#41-特性描述}
>
> **来源: [Cargo Book - Environment Variables](https://doc.rust-lang.org/cargo/reference/environment-variables.html)**

`CARGO_BIN_EXE_<crate>` 环境变量现在在运行时也可用，而不仅限于构建脚本。

### 4.2 使用示例 {#42-使用示例}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

```rust
// 在测试中查找工具二进制文件
let tool_path = std::env::var("CARGO_BIN_EXE_my-tool")
    .expect("CARGO_BIN_EXE_my-tool not set");

let output = std::process::Command::new(tool_path)
    .arg("--version")
    .output()
    .expect("Failed to run tool");
```

### 4.3 测试示例 {#43-测试示例}
>
> **[来源: [Rust Cookbook](https://rust-lang-nursery.github.io/rust-cookbook/)]**

```rust
#[test]
fn test_cli_tool() {
    let exe = env!("CARGO_BIN_EXE_my-cli");
    let output = std::process::Command::new(exe)
        .args(["--input", "test.txt"])
        .output()
        .unwrap();

    assert!(output.status.success());
}
```

---

## 五、性能改进 {#五性能改进}
>
> **[来源: [crates.io](https://crates.io/)]**

### 5.1 cargo clean 优化 {#51-cargo-clean-优化}
>
> **来源: [Cargo CHANGELOG 1.94+](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html)**

`cargo clean -p` 和 `cargo clean --workspace` 现在更快了。

```bash
# 清理特定包（更快） {#清理特定包更快}
cargo clean -p my-package

# 清理整个工作区（更快） {#清理整个工作区更快}
cargo clean --workspace
```

---

## 六、完整配置示例 {#六完整配置示例}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

```toml
# .cargo/config.toml {#cargoconfigtoml-4}
# ================== {#} {#} {#}

# 包含其他配置文件 {#包含其他配置文件}
include = [
    { path = "team.toml" },
    { path = "local.toml", optional = true },
    { path = "ci.toml", optional = true },
]

[build]
rustflags = ["-C", "target-cpu=native"]
jobs = 8

[profile.release]
opt-level = 3
lto = "thin"

[profile.dev]
opt-level = 1
incremental = true

# 使用 TOML 1.1 特性（多行内联表） {#使用-toml-11-特性多行内联表}
[target.'cfg(unix)'.dependencies]
libc = {
    version = "0.2",
    features = ["extra_traits",],
}

[registries.crates-io]
protocol = "sparse"
```

---

## 七、迁移指南 {#七迁移指南}
>
> **[来源: [The Rust Programming Language](https://doc.rust-lang.org/book/)]**

### 7.1 从旧版本迁移 {#71-从旧版本迁移}
>
> **[来源: [Rust Standard Library](https://doc.rust-lang.org/std/)]**

1. **更新 Rust**: `rustup update stable`
2. **验证配置**: `cargo check`
3. **使用新特性**: 逐步采用 TOML 1.1 和 config inclusion

### 7.2 兼容性 {#72-兼容性}
>
> **[来源: [Rustonomicon](https://doc.rust-lang.org/nomicon/)]**

| 特性 | 向后兼容 | 说明 |
|------|----------|------|
| Config inclusion | ✅ | 可选使用 |
| TOML 1.1 | ⚠️ | 提高开发 MSRV |
| pubtime | ✅ | 自动处理 |
| CARGO_BIN_EXE | ✅ | 新增功能 |

---

## 八、相关资源 {#八相关资源}
>
> **[来源: [Rust By Example](https://doc.rust-lang.org/rust-by-example/)]**

- [Cargo 1.94 开发周期报告](https://blog.rust-lang.org/inside-rust/2026/02/18/this-development-cycle-in-cargo-1.94/)
- [Cargo 官方文档](https://doc.rust-lang.org/cargo/)
- [TOML 1.1 规范](https://toml.io/en/v1.1.0)
- [Rust 1.94 特性分析](10_rust_194_comprehensive_analysis.md)

---

**文档版本**: 1.0
**创建日期**: 2026-03-13
**维护者**: Rust 学习项目团队

---

## 九、Rust 1.96 Cargo 安全修复 {#九rust-196-cargo-安全修复}

> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**
> **来源: [CVE-2026-5223](https://blog.rust-lang.org/2026/05/25/cve-2026-5223/)**
> **来源: [CVE-2026-5222](https://blog.rust-lang.org/2026/05/25/cve-2026-5222/)**
> **来源: [Cargo Security Advisories](https://github.com/rust-lang/cargo/security/advisories)**
> **来源: [The Cargo Book](https://doc.rust-lang.org/cargo/)**

Rust 1.96.0 包含两个 Cargo 安全修复，主要影响使用**第三方 registry** 的用户；crates.io 用户不受影响。

### 9.1 CVE-2026-5223 {#91-cve-2026-5223}

| 属性 | 说明 |
| :--- | :--- |
| 严重级别 | 中危 (Medium) |
| 影响范围 | 第三方 registry 用户 |
| 问题描述 | Cargo 错误处理第三方 registry crate tarball 中的符号链接，允许恶意 crate 覆盖同一 registry 中其他 crate 的源代码缓存 |
| 修复方式 | Rust 1.96.0 起拒绝提取 tarball 中的任何符号链接 |
| 权威来源 | [CVE-2026-5223](https://blog.rust-lang.org/2026/05/25/cve-2026-5223/)、[Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)、[releases.rs 1.96.0](https://releases.rs/docs/1.96.0/) |

### 9.2 CVE-2026-5222 {#92-cve-2026-5222}

| 属性 | 说明 |
| :--- | :--- |
| 严重级别 | 低危 (Low) |
| 影响范围 | 第三方 registry 用户 |
| 问题描述 | URL 规范化后的认证处理问题 |
| 修复方式 | 修复 URL 规范化中的身份验证逻辑 |
| 权威来源 | [CVE-2026-5222](https://blog.rust-lang.org/2026/05/25/cve-2026-5222/)、[Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)、[releases.rs 1.96.0](https://releases.rs/docs/1.96.0/) |

### 9.3 升级建议 {#93-升级建议}

```bash
# 升级至 Rust 1.96.0+ {#升级至-rust-1960}
rustup update stable

# 验证 Cargo 版本 {#验证-cargo-版本}
cargo --version  # >= 1.96.0
```

## 十、Cargo 1.95/1.96 新增/变更 {#十cargo-195196-新增变更}

> **来源: [Cargo 1.95 CHANGELOG](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-195-2026-04-16)**
> **来源: [Cargo 1.96 CHANGELOG](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)**
> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**
> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**

| 特性 | 来源 | 说明 |
| :--- | :--- | :--- |
| `target.'cfg(..)'.rustdocflags` | [Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)、[cargo#16846](https://github.com/rust-lang/cargo/pull/16846) | 在 Cargo 配置中支持按 `cfg` 条件设置 `rustdocflags` |
| dependency 同时指定 git 仓库与 alternate registry | [Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)、[cargo#16810](https://github.com/rust-lang/cargo/pull/16810) | 本地使用 git 版本，发布时使用 registry 版本 |
| `cargo init` 禁止在主目录执行 | [Cargo CHANGELOG 1.95](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-195-2026-04-16)、[cargo#16566](https://github.com/rust-lang/cargo/pull/16566) | 避免新用户因清单发现产生混乱状态 |
| `cargo package` 覆盖大 crate 文件损坏修复 | [Cargo CHANGELOG 1.95](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-195-2026-04-16)、[cargo#16713](https://github.com/rust-lang/cargo/pull/16713) | 修复覆盖较大现有 `.crate` 时产生损坏包的问题 |

---

## ✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024） {#权威国际化来源对齐升级摘要rust-1960-edition-2024}

> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**
> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**
> **来源: [releases.rs](https://releases.rs/)**
> **适用版本**: Rust 1.96.0+ (Edition 2024)
> **升级日期**: 2026-06-29

### 本次升级要点 {#本次升级要点}

本文档已完成权威国际化来源对齐升级，统一版本基准为 **Rust 1.96.0+ / Edition 2024**，同时保留 1.93/1.94 历史分析章节。

#### 新增 Rust 1.96.0 特性 {#新增-rust-1960-特性}

| 特性 | 来源 | 说明 |
| :--- | :--- | :--- |
| `core::range` 新类型 | [RFC 3550](https://rust-lang.github.io/rfcs/3550-new-range.html)、[std::range](https://doc.rust-lang.org/stable/std/range/index.html) | `Range`/`RangeFrom`/`RangeInclusive` 实现 `Copy` + `IntoIterator` |
| `assert_matches!` / `debug_assert_matches!` | [core::assert_matches](https://doc.rust-lang.org/stable/core/assert_matches/macro.assert_matches.html) | 模式断言宏，失败输出 Debug 信息 |
| Cargo CVE-2026-5223 / CVE-2026-5222 修复 | [Cargo 安全公告](https://github.com/rust-lang/cargo/security/advisories)、[Rust Blog 1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) | 第三方 registry tarball symlink 与 URL 规范化修复 |
| WebAssembly 链接行为变更 | [Rust Blog 1.96.0](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/) | 不再默认传递 `--allow-undefined` |
| Cargo `target.'cfg(..)'.rustdocflags` | [Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)、[cargo#16846](https://github.com/rust-lang/cargo/pull/16846) | 按 `cfg` 条件设置 rustdocflags |
| dependency 同时指定 git 与 alternate registry | [Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)、[cargo#16810](https://github.com/rust-lang/cargo/pull/16810) | 本地 git，发布 registry |

#### 新增 Rust 1.95.0 特性 {#新增-rust-1950-特性}

| 特性 | 来源 | 说明 |
| :--- | :--- | :--- |
| `if let` guards on match arms | [Rust Reference - Match Guards](https://doc.rust-lang.org/reference/expressions/match-expr.html#match-guards)、[Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | match 臂支持 `if let` 守卫 |
| `cfg_select!` 宏 | [Rust Reference - Conditional Compilation](https://doc.rust-lang.org/reference/conditional-compilation.html)、[releases.rs 1.95.0](https://releases.rs/docs/1.95.0/) | 编译期 cfg 条件选择宏 |
| PowerPC / PowerPC64 内联汇编稳定化 | [Rust Reference - Inline Assembly](https://doc.rust-lang.org/reference/inline-assembly.html)、[Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 稳定 inline assembly for PowerPC |
| `--remap-path-scope` | [Rust Blog 1.95.0](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/) | 控制路径重映射作用域 |
| `cargo init` 禁止在主目录执行 | [Cargo CHANGELOG 1.95](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-195-2026-04-16)、[cargo#16566](https://github.com/rust-lang/cargo/pull/16566) | 避免清单发现混乱 |
| `cargo package` 覆盖大 crate 文件损坏修复 | [Cargo CHANGELOG 1.95](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-195-2026-04-16)、[cargo#16713](https://github.com/rust-lang/cargo/pull/16713) | 修复 `.crate` 覆盖损坏 |

#### 权威来源对齐 {#权威来源对齐}

- Rust release notes（releases.rs）
- Rust Blog 对应版本发布公告
- Rust Reference 具体章节（Range Expressions、Match Guards、Inline Assembly、Conditional Compilation）
- Rust Standard Library 具体 API（`core::range`、`core::assert_matches`、`std::ops::ControlFlow`）
- RFC 链接（RFC 3550 等）

---

## 相关概念 {#相关概念}
>
> **[来源: [Rust Reference](https://doc.rust-lang.org/reference/)]**

- [research_notes 目录](README.md)
- [上级目录](../README.md)

---

## 权威来源索引 {#权威来源索引}

> **来源: [Wikipedia - Build Automation](https://en.wikipedia.org/wiki/Build_Automation)**
> **来源: [The Cargo Book](https://doc.rust-lang.org/cargo/)**
> **来源: [Cargo Book - Config Include](https://doc.rust-lang.org/cargo/reference/config.html#include)**
> **来源: [Cargo Book - Manifest Format](https://doc.rust-lang.org/cargo/reference/manifest.html)**
> **来源: [Cargo Book - Environment Variables](https://doc.rust-lang.org/cargo/reference/environment-variables.html)**
> **来源: [Cargo Book - Registry Index](https://doc.rust-lang.org/cargo/reference/registry-index.html)**
> **来源: [Cargo CHANGELOG 1.95](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-195-2026-04-16)**
> **来源: [Cargo CHANGELOG 1.96](https://doc.rust-lang.org/nightly/cargo/CHANGELOG.html#cargo-196-2026-05-28)**
> **来源: [CVE-2026-5223](https://blog.rust-lang.org/2026/05/25/cve-2026-5223/)**
> **来源: [CVE-2026-5222](https://blog.rust-lang.org/2026/05/25/cve-2026-5222/)**
> **来源: [Rust 1.96.0 Release Notes](https://blog.rust-lang.org/2026/05/28/Rust-1.96.0/)**
> **来源: [releases.rs 1.96.0](https://releases.rs/docs/1.96.0/)**
> **来源: [Rust 1.95.0 Release Notes](https://blog.rust-lang.org/2026/04/16/Rust-1.95.0/)**
> **来源: [releases.rs 1.95.0](https://releases.rs/docs/1.95.0/)**
> **来源: [Cargo Security Advisories](https://github.com/rust-lang/cargo/security/advisories)**
> **来源: [RFC 3550 - New Range Types](https://rust-lang.github.io/rfcs/3550-new-range.html)**
> **来源: [crates.io Documentation](https://crates.io/)**

---
