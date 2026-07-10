> **内容分级**: [专家级]

# Rustdoc 1.96 变更

> **EN**: Rustdoc 1.96 Changes
> **Summary**: Rustdoc changes stabilized in Rust 1.96, including `target.'cfg(..)'.rustdocflags` configuration, deprecation rendering improvements, sidebar navigation enhancements, and `missing_doc_code_examples` lint updates.
> **受众**: [进阶 / 工程]
> **Bloom 层级**: L2-L3
> **权威来源**: 本文件为 `concept/` 权威页。
> **A/S/P 标记**: **P** — Process / Platform
> **双维定位**: P×App — 应用 Rustdoc 1.96 变更生成高质量 crate 文档
> **前置概念**: · [Rust vs Python](../../05_comparative/02_managed_languages/07_rust_vs_python.md) [Toolchain](01_toolchain.md) · [Documentation](../09_testing_and_quality/14_documentation.md) · [Macro Patterns](../../02_intermediate/06_macros_and_metaprogramming/17_macro_patterns.md)
> **后置概念**: [Rust Version Tracking](../../07_future/00_version_tracking/05_rust_version_tracking.md) · [Rust 1.96 Stabilized](../../07_future/00_version_tracking/rust_1_96_stabilized.md)
> **深度参考**: [`docs/06_toolchain/06_20_rustdoc_196_improvements.md`](../../../docs/06_toolchain/06_20_rustdoc_196_improvements.md) — rustdoc 渲染细节与弃用注释示例
> **版本状态**: 当前稳定 patch 为 **1.97.0**；特性集与 Rust 1.96.0 一致。

---

> **来源**: Rust 1.96.0 Release Notes · · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/) · [Jung et al. — RustBelt: Securing the Foundations of Rust](https://plv.mpi-sws.org/rustbelt/popl18/) · [Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html)
> [Rustdoc Book](https://doc.rust-lang.org/rustdoc/) ·
> [Cargo Book — Configuration](https://doc.rust-lang.org/cargo/reference/config.html) ·
> [RFC 3271 — Rustdoc links [已失效](https://github.com/rust-lang/rfcs/pull/3271)]<!-- 原链接: https://rust-lang.github.io/rfcs/3271-rustdoc-json.html -->

---

> **过渡**: 从 Rustdoc 1.96 变更 的直观描述转向其形式化定义，需要先把日常经验中的模糊直觉转化为可验证的术语。

> **过渡**: 在建立 Rustdoc 1.96 变更 的核心命题之后，下一步是审视这些命题在边界条件下的稳定性——这正是反命题与反例的价值所在。

> **过渡**: 最后，将 Rustdoc 1.96 变更 与相邻概念连接，形成从 L1 到 L7 的纵向认知路径，避免孤立记忆。

---

> **定理 1** [Tier 2]: Rustdoc 1.96 变更 的核心约束 ⟹ 编译器可以在编译期排除一整类运行时（Runtime）错误。
>
> **定理 2** [Tier 2]: 正确理解 Rustdoc 1.96 变更 的语义 ⟹ 开发者能够写出既安全又零成本抽象（Zero-Cost Abstraction）的代码。
>
> **定理 3** [Tier 3]: 将 Rustdoc 1.96 变更 与 Rust 的所有权（Ownership）/生命周期（Lifetimes）模型结合 ⟹ 可以在更大系统中进行可扩展的推理。

## 📑 目录

- [Rustdoc 1.96 变更](#rustdoc-196-变更)
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

> **对应练习**: [`exercises/src/rustdoc_196/`](../../exercises/src/rustdoc_196)
