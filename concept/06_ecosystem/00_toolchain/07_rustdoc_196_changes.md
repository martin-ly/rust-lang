# Rustdoc 1.96–1.97 变更

> **EN**: Rustdoc 1.96–1.97 Changes
> **Summary**: Rustdoc changes stabilized in Rust 1.96 (`target.'cfg(..)'.rustdocflags`, deprecation rendering, sidebar navigation, `missing_doc_code_examples` lint) and Rust 1.97 (`--emit` output control, `--remap-path-prefix` / `--remap-path-scope` path remapping). 1.97 items verified against local rustdoc 1.97.0.
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **受众**: [进阶 / 工程]
> **内容分级**: [专家级]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **A** — Application
> **双维定位**: P×App — 应用 Rustdoc 1.96 变更生成高质量 crate 文档
> **前置概念**: · [Rust vs Python](../../05_comparative/02_managed_languages/02_rust_vs_python.md) [Toolchain](01_toolchain.md) · [Documentation](../09_testing_and_quality/02_documentation.md) · [Macro Patterns](../../02_intermediate/06_macros_and_metaprogramming/03_macro_patterns.md)
> **后置概念**: [Rust Version Tracking](../../07_future/00_version_tracking/01_rust_version_tracking.md) · [Rust 1.96 Stabilized](../../07_future/00_version_tracking/rust_1_96_stabilized.md)
> **深度参考**: [`docs/09_toolchain/09_rustdoc_196_improvements.md`](../../../docs/09_toolchain/09_rustdoc_196_improvements.md) — rustdoc 渲染细节与弃用注释示例
> **版本状态**: 当前稳定 patch 为 **1.97.0**。第二至六节为 Rust 1.96.0 特性集；**第七节为 Rust 1.97.0 新增的 rustdoc 稳定项**（`--emit`、`--remap-path-prefix`），已用本地 `rustdoc 1.97.0 (2d8144b78 2026-07-07)` 实测。

---

> **来源**: Rust 1.96.0 Release Notes · · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Rustdoc Book](https://doc.rust-lang.org/rustdoc/) ·
> [Cargo Book — Configuration](https://doc.rust-lang.org/cargo/reference/config.html) ·
> [RFC 2963 — Rustdoc JSON](https://rust-lang.github.io/rfcs/2963-rustdoc-json.html)

---

## 📑 目录

- [Rustdoc 1.96–1.97 变更](#rustdoc-196197-变更)
  - [📑 目录](#-目录)
  - [一、特性总览](#一特性总览)
  - [二、`target.'cfg(..)'.rustdocflags`](#二targetcfgrustdocflags)
    - [2.1 背景](#21-背景)
    - [2.2 Rust 1.96 新增语法](#22-rust-196-新增语法)
    - [2.3 典型应用场景](#23-典型应用场景)
  - [三、弃用（Deprecation）渲染改进](#三弃用deprecation渲染改进)
    - [3.1 变更内容](#31-变更内容)
    - [3.2 示例](#32-示例)
    - [3.3 建议](#33-建议)
  - [四、侧边栏导航增强](#四侧边栏导航增强)
    - [4.1 变更内容](#41-变更内容)
    - [4.2 对 crate 作者的影响](#42-对-crate-作者的影响)
  - [五、`missing_doc_code_examples` lint 改进](#五missing_doc_code_examples-lint-改进)
    - [5.1 背景](#51-背景)
    - [5.2 Rust 1.96 改进](#52-rust-196-改进)
    - [5.3 启用方式](#53-启用方式)
    - [5.4 与 `cargo test --doc` 的关系](#54-与-cargo-test---doc-的关系)
  - [六、迁移建议](#六迁移建议)
  - [七、Rust 1.97 rustdoc 稳定项：`--emit` 与路径重映射](#七rust-197-rustdoc-稳定项--emit-与路径重映射)
    - [7.1 `--emit` 输出格式控制](#71---emit-输出格式控制)
    - [7.2 `--remap-path-prefix` 与 `--remap-path-scope`](#72---remap-path-prefix-与---remap-path-scope)
    - [7.3 典型应用场景](#73-典型应用场景)

---

## 一、特性总览

Rust 1.96 的 Rustdoc 与文档生成工具链主要带来以下改进：

| 特性 | 说明 | 典型收益 |
|:---|:---|:---|
| **`target.'cfg(..)'.rustdocflags`** | 按目标条件配置 rustdoc 标志 | 跨平台 crate 可针对不同 target 启用不同文档特性 |
| **弃用渲染改进** | `#[deprecated]` 的呈现更清晰，包含 since 与 note | 降低误用已弃用 API 的概率 |
| **侧边栏导航增强** | 长文档页面的章节导航与符号索引改善 | 提升大型 crate 的可读性 |
| **`missing_doc_code_examples` lint** | 对缺少文档示例的项给出更精确的诊断 | 促进文档质量 |

---

## 二、`target.'cfg(..)'.rustdocflags`

本节围绕「`target.'cfg(..)'.rustdocflag…」展开，依次讨论背景、Rust 1.96 新增语法与典型应用场景。

### 2.1 背景

在 Rust 1.96 之前，`rustdocflags` 只能在 `[build]` 下全局配置：

```toml
[build]
rustdocflags = ["--cfg", "docsrs"]
```

这无法针对特定 target 做区分。对于需要在不同平台生成不同文档的 crate（例如底层绑定、嵌入式、OS 开发），全局配置不够灵活。

### 2.2 Rust 1.96 新增语法

Cargo 1.96 支持按 `target.'cfg(..)'` 配置 `rustdocflags`：

```toml
# .cargo/config.toml
[target.'cfg(unix)']
rustdocflags = ["--cfg", "unix_docs"]

[target.'cfg(windows)']
rustdocflags = ["--cfg", "windows_docs"]

[target.'cfg(target_arch = "wasm32")']
rustdocflags = ["--cfg", "wasm_docs"]
```

### 2.3 典型应用场景

| 场景 | 配置示例 |
|:---|:---|
| **docs.rs 多目标文档** | 为 `x86_64-unknown-linux-gnu`、`wasm32-unknown-unknown` 等目标设置不同 `--cfg` |
| **平台特定 API 隐藏/显示** | 仅在文档中展示当前目标支持的模块（Module） |
| **条件化 doc attribute** | 配合 `#[cfg_attr(docsrs, doc(cfg(...)))]` 使用 |

```rust
#[cfg_attr(docsrs, doc(cfg(unix)))]
pub mod unix_only_api {
    //! 仅在 Unix 目标下可用的 API
}
```

---

## 三、弃用（Deprecation）渲染改进

本节围绕「弃用（Deprecation）渲染改进」展开，依次讨论变更内容、示例与建议。

### 3.1 变更内容

Rust 1.96 改进了 rustdoc 对 `#[deprecated]` 属性的渲染：

- **视觉层级更突出**：弃用提示在方法/类型签名附近更明显。
- **信息更完整**：自动显示 `since` 版本与 `note` 内容。
- **关联替代 API 链接**：如果 `note` 中包含路径或 Markdown 链接，渲染更友好。

### 3.2 示例

```rust
/// 旧的配置加载方式。
#[deprecated(
    since = "2.0.0",
    note = "请改用 `Config::load_from_toml`，支持 TOML v1.1 与错误恢复"
)]
pub fn load_config(path: &str) -> Config {
    // ...
}

/// 新的配置加载方式。
pub fn load_from_toml(path: &str) -> Result<Config, ConfigError> {
    // ...
}
```

生成文档后，用户会在 `load_config` 附近看到清晰的弃用横幅，提示 since 版本与替代方案。

### 3.3 建议

- 在弃用 `note` 中始终包含**具体替代 API 名称**或**迁移文档链接**。
- 对于重大变更，使用 `#[deprecated(since = "X.Y.Z", note = "...")]` 并配合 SemVer 主版本升级。

---

## 四、侧边栏导航增强

本节从变更内容 与 对 crate 作者的影响 两个层面剖析「侧边栏导航增强」。

### 4.1 变更内容

Rust 1.96 对 Rustdoc 生成的 HTML 侧边栏进行了多项可用性改进：

- **更稳定的滚动位置**：在页面内跳转后，侧边栏保持当前章节高亮。
- **可折叠层级**：大型模块（Module）的侧边栏支持折叠/展开子模块列表。
- **搜索集成**：侧边栏顶部与搜索框的交互更一致。
- **移动端适配**：窄屏下的侧边栏展开/收起更流畅。

### 4.2 对 crate 作者的影响

- 确保文档章节标题层级（`#`、`##`、`###`）清晰，以便侧边栏正确分组。
- 对特别长的模块（Module），考虑使用 `#[doc = include_str!("...")]` 拆分文档到单独文件。

---

## 五、`missing_doc_code_examples` lint 改进

理解「`missing_doc_code_examples` l…」需要把握背景、Rust 1.96 改进、启用方式与与 `cargo test --doc` 的关系，本节依次展开。

### 5.1 背景

`missing_doc_code_examples` 是一个 rustdoc lint，用于提醒公开 API 的文档中缺少代码示例。

### 5.2 Rust 1.96 改进

- **范围更精确**：不再对明显不需要示例的项（如某些 trait alias、extern block）误报。
- **诊断信息更友好**：指出具体缺少示例的项，并给出添加 `#[doc = ...]` 或 `/// # Examples` 的提示。
- **与 `#[allow(...)]` 的交互更一致**：可以在模块（Module）或项级别精确控制。

### 5.3 启用方式

```rust
#![warn(rustdoc::missing_doc_code_examples)]

/// 返回两个数中的较大值。
///
/// # Examples
///
/// ```
/// let m = my_crate::max(1, 2);
/// assert_eq!(m, 2);
/// ```
pub fn max(a: i32, b: i32) -> i32 {
    if a > b { a } else { b }
}
```

### 5.4 与 `cargo test --doc` 的关系

- rustdoc 代码示例默认会被 `cargo test` 作为文档测试执行。
- 添加示例不仅改善文档，还能通过 doctest 保证示例代码始终可编译。

---

## 六、迁移建议

1. **配置 `target.'cfg(..)'.rustdocflags`**
   - 对于跨平台 crate，在 `.cargo/config.toml` 中为目标特定文档生成添加 `--cfg`。
   - 配合 `#[cfg_attr(docsrs, doc(cfg(...)))]` 控制 API 展示。

2. **审查弃用属性**
   - 搜索项目中所有 `#[deprecated]`，确保 `note` 包含可执行的迁移指引。
   - 在 CI 中启用 `rustdoc::missing_doc_code_examples` 警告。

3. **验证文档生成**
   - 运行 `cargo doc --no-deps` 检查新 lint 和渲染效果。
   - 对多目标 crate，尝试 `cargo doc --target <triple>` 验证 rustdocflags 行为。

4. **关注 docs.rs 行为**
   - docs.rs 默认会读取 `.cargo/config.toml` 中的 `rustdocflags`。
   - 确保新配置在本地和 docs.rs 上一致。

---

## 七、Rust 1.97 rustdoc 稳定项：`--emit` 与路径重映射

Rust 1.97 将两个长期停留在 nightly 的 rustdoc 标志稳定化。以下行为均以本地 `rustdoc 1.97.0 (2d8144b78 2026-07-07)` 实测。

### 7.1 `--emit` 输出格式控制

`--emit` 允许显式选择 rustdoc 的产物类型。1.97 stable 接受三个取值（注意：**没有 `html` 这个值**）：

| 取值 | 产物 | 实测结果 |
|:---|:---|:---|
| `html-static-files` | 仅静态资源（CSS/JS/字体，输出为 `static.files/`） | ✅ `rustdoc --emit=html-static-files src/lib.rs -o out` 生成 `static.files` |
| `html-non-static-files` | 仅 HTML 页面（不含静态资源） | ✅ 生成 `crates.js`、`help.html`、模块目录 |
| `dep-info` | Makefile 风格的依赖文件（`lib.d`） | ✅ 生成 `lib.d`，内容形如 `lib.d: src/lib.rs` |

```bash
# 分离产物：文档页面与静态资源可分别缓存/部署
rustdoc --emit=html-non-static-files src/lib.rs --edition 2024 -o target/doc-pages
rustdoc --emit=html-static-files     src/lib.rs --edition 2024 -o target/doc-assets

# 依赖信息：接入外部构建系统（make/ninja 增量重建文档）
mkdir -p target/doc-dep
rustdoc --emit=dep-info src/lib.rs --edition 2024 -o target/doc-dep
```

实测注意点：

- `--emit=dep-info` 要求 `-o` 指定的目录**已存在**，否则报 `error writing dependencies`（os error 3）。
- 不传 `--emit` 时行为不变（默认生成完整 HTML 文档）。
- `rustdoc --emit=html` 会报 `unrecognized emission type: html`——1.97 没有 `html` 这个 emit 值，组合产物需同时列出所需类型（逗号分隔）。

### 7.2 `--remap-path-prefix` 与 `--remap-path-scope`

与 `rustc` 同名标志对齐：在生成文档中把源码路径前缀替换为占位值，服务于可重现构建与路径隐私。配套稳定的 `--remap-path-scope` 控制重映射作用域。

```bash
rustdoc src/lib.rs --edition 2024 \
    --remap-path-prefix=/home/ci/work=/src \
    --remap-path-scope=all \
    -o target/doc
```

`--remap-path-scope` 取值：`macro`、`diagnostics`、`debuginfo`、`coverage`、`object`、`all`（rustdoc 1.97 `--help` 实测）。

### 7.3 典型应用场景

| 场景 | 组合方式 |
|:---|:---|
| **可重现文档构建** | `--remap-path-prefix` 消除构建机路径差异，产物字节级一致，便于 CI 缓存校验 |
| **文档产物分层部署** | `--emit=html-non-static-files` 页面进 CDN 频繁更新层，`html-static-files` 静态资源长缓存 |
| **外部增量构建** | `--emit=dep-info` 输出 `.d` 文件，make/ninja 据此决定文档是否需要重建 |
| **隐私发布** | 重映射去掉开发者本机路径，避免泄露目录结构 |

---

> **对应练习**: [`exercises/src/rustdoc_196/`](../../exercises/src/rustdoc_196)
