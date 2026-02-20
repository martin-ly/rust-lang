# Rust 1.93 Cargo 与 Rustdoc 变更详解

> **创建日期**: 2026-02-12
> **最后更新**: 2026-02-15
> **Rust 版本**: 1.93.0+ (Edition 2024)
> **状态**: ✅ 已完成

---

## 目录

- [Rust 1.93 Cargo 与 Rustdoc 变更详解](#rust-193-cargo-与-rustdoc-变更详解)
  - [目录](#目录)
  - [Cargo 变更](#cargo-变更)
    - [CARGO\_CFG\_DEBUG\_ASSERTIONS](#cargo_cfg_debug_assertions)
    - [cargo tree --format 长格式](#cargo-tree---format-长格式)
    - [cargo clean --workspace](#cargo-clean---workspace)
  - [Rustdoc 变更](#rustdoc-变更)
    - [移除 #!\[doc(document\_private\_items)\]](#移除-docdocument_private_items)
    - [宏搜索过滤](#宏搜索过滤)
    - [import 搜索过滤](#import-搜索过滤)
    - [文档属性校验](#文档属性校验)
  - [相关文档](#相关文档)
  - [完整代码示例](#完整代码示例)
  - [形式化规范链接](#形式化规范链接)

---

## Cargo 变更

### CARGO_CFG_DEBUG_ASSERTIONS

**变更**：Cargo 1.93 在 build scripts 中根据 profile 启用 `CARGO_CFG_DEBUG_ASSERTIONS` 环境变量。

**影响**：依赖 `static-init` 1.0.1–1.0.3 的 crate 可能编译失败，错误为 "failed to resolve: use of unresolved module or unlinked crate `parking_lot`"。

**解决方案**：升级 `static-init` 或检查依赖。

**参考**：[Issue #150646](https://github.com/rust-lang/rust/issues/150646#issuecomment-3718964342)

---

### cargo tree --format 长格式

**变更**：`cargo tree` 支持 `--format` 变量的长格式。

**示例**：

```bash
# 长格式变量示例
cargo tree --format "{p} {l} {r}"
```

**参考**：[PR #16204](https://github.com/rust-lang/cargo/pull/16204)

---

### cargo clean --workspace

**变更**：`cargo clean` 新增 `--workspace` 选项，可清理整个 workspace。

**示例**：

```bash
# 清理整个 workspace 的 target 目录
cargo clean --workspace
```

**参考**：[PR #16263](https://github.com/rust-lang/cargo/pull/16263)

---

## Rustdoc 变更

### 移除 #![doc(document_private_items)]

**变更**：`#![doc(document_private_items)]` 属性已被移除。

**影响**：若 crate 使用了该属性，编译会报错。应改用其他方式展示私有项文档。

**参考**：[PR #146495](https://github.com/rust-lang/rust/pull/146495)

---

### 宏搜索过滤

**变更**：在 rustdoc 的 "macros" 搜索过滤中，现在包含 attribute 宏和 derive 宏。

**影响**：搜索宏时结果更完整。

**参考**：[PR #148176](https://github.com/rust-lang/rust/pull/148176)

---

### import 搜索过滤

**变更**：在 rustdoc 的 `import` 搜索过滤中，现在包含 extern crates。

**影响**：搜索 import 时结果更完整。

**参考**：[PR #148301](https://github.com/rust-lang/rust/pull/148301)

---

### 文档属性校验

**变更**：若 `html_favicon_url`、`html_logo_url`、`html_playground_url`、`issue_tracker_base_url` 或 `html_no_source` 有缺失值、意外值或类型错误，rustdoc 将发出 deny-by-default lint `rustdoc::invalid_doc_attributes`。

**解决方案**：检查并修正 crate 级文档属性配置。

```toml
# Cargo.toml 示例
[package.metadata.docs.rs]
# 确保这些属性有有效值
```

**参考**：[PR #149197](https://github.com/rust-lang/rust/pull/149197)

---

## 相关文档

- [Rust 1.93 完整变更清单](./07_rust_1.93_full_changelog.md)
- [Rust 1.93 兼容性注意事项](./06_rust_1.93_compatibility_notes.md)
- [Cargo 速查卡](../quick_reference/cargo_cheatsheet.md)
- [rustdoc 高级用法](./03_rustdoc_advanced.md)

---

## 完整代码示例

```rust
//! Rust 1.93 Cargo 和 Rustdoc 变更完整示例

/// CARGO_CFG_DEBUG_ASSERTIONS 检测示例
pub mod debug_assertions_example {
    /// 在 build.rs 中检测 debug_assertions
    ///
    /// Cargo 1.93 会根据 profile 设置此变量
    pub fn detect_in_build_script() {
        // build.rs 中：
        // let debug_assertions = std::env::var("CARGO_CFG_DEBUG_ASSERTIONS").is_ok();
        // println!("cargo:rustc-cfg=has_debug_assertions={}", debug_assertions);
    }

    /// 在代码中使用条件编译
    #[cfg(has_debug_assertions = "true")]
    pub fn debug_only_function() {
        println!("仅在 debug 模式下可用");
    }
}

/// cargo clean --workspace 使用示例
pub mod cargo_clean_workspace {
    use std::process::Command;

    /// 清理工作区的完整脚本
    pub fn clean_workspace() -> Result<(), String> {
        // ✅ Rust 1.93+：使用 --workspace 选项
        let output = Command::new("cargo")
            .args(["clean", "--workspace"])
            .output()
            .map_err(|e| e.to_string())?;

        if output.status.success() {
            println!("Workspace cleaned successfully");
            Ok(())
        } else {
            Err(String::from_utf8_lossy(&output.stderr).to_string())
        }
    }

    /// CI 中的清理策略
    pub fn ci_clean_strategy() {
        // 完整清理（包括所有 workspace members）
        // cargo clean --workspace

        // 仅清理当前包
        // cargo clean

        // 清理特定包
        // cargo clean -p package_name
    }
}

/// cargo tree --format 长格式示例
pub mod cargo_tree_format {
    use std::process::Command;

    /// 使用长格式变量
    pub fn tree_with_long_format() {
        // 可用的长格式变量：
        // {p} - 包名和版本
        // {l} - 许可证
        // {r} - 仓库 URL
        // {f} - 特性
        // {s} - 包大小

        let formats = [
            ("包名和许可证", "{p} {l}"),
            ("包名和仓库", "{p} {r}"),
            ("完整信息", "{p} [{f}]"),
        ];

        for (desc, format) in formats {
            println!("{}: cargo tree --format '{}'", desc, format);

            // 实际执行：
            // let _ = Command::new("cargo")
            //     .args(["tree", "--format", format])
            //     .output();
        }
    }

    /// 生成依赖报告
    pub fn generate_dependency_report() -> String {
        r#"
# 依赖报告生成脚本

## 基础依赖树
cargo tree

## 包含许可证信息
cargo tree --format "{p} [{l}]"

## 仅显示生产依赖
cargo tree --edges normal

## 显示重复依赖
cargo tree --duplicates
"#
        .to_string()
    }
}

/// rustdoc 文档属性校验示例
pub mod rustdoc_attr_validation {
    /// ✅ 正确的文档属性配置
    pub mod correct_attrs {
        #![doc(html_logo_url = "https://example.com/logo.png")]
        #![doc(html_favicon_url = "https://example.com/favicon.ico")]
        #![doc(html_root_url = "https://docs.rs/my-crate/0.1.0")]
        #![doc(html_playground_url = "https://play.rust-lang.org/")]
    }

    /// ❌ 错误配置（会被 Rust 1.93 检测到）
    ///
    /// #![doc(html_logo_url = "")]  // 空值错误
    /// #![doc(html_favicon_url = 123)]  // 类型错误（应为字符串）

    /// Cargo.toml 配置示例
    pub const CARGO_TOML_EXAMPLE: &str = r#"
[package.metadata.docs.rs]
# 确保这些属性有有效值
all-features = true
rustdoc-args = ["--cfg", "docsrs"]
"#;
}

/// 文档属性 CI 检查
pub mod doc_ci_checks {
    use std::process::Command;

    /// 检查文档属性有效性
    pub fn check_doc_attributes() -> Result<(), String> {
        // 使用 deny lint 检查无效文档属性
        let output = Command::new("cargo")
            .args(["doc", "--no-deps"])
            .env("RUSTDOCFLAGS", "-D rustdoc::invalid_doc_attributes")
            .output()
            .map_err(|e| e.to_string())?;

        if output.status.success() {
            Ok(())
        } else {
            Err(String::from_utf8_lossy(&output.stderr).to_string())
        }
    }

    /// 完整文档检查流程
    pub fn full_doc_check() -> Result<(), Vec<String>> {
        let mut errors = Vec::new();

        // 检查 1：文档属性有效性
        if let Err(e) = check_doc_attributes() {
            errors.push(format!("Doc attributes invalid: {}", e));
        }

        // 检查 2：文档测试
        let output = Command::new("cargo")
            .args(["test", "--doc"])
            .output()
            .map_err(|e| vec![e.to_string()])?;

        if !output.status.success() {
            errors.push("Doc tests failed".to_string());
        }

        // 检查 3：文档链接有效性
        let output = Command::new("cargo")
            .args(["rustdoc", "--", "-D", "rustdoc::broken-intra-doc-links"])
            .output()
            .map_err(|e| vec![e.to_string()])?;

        if !output.status.success() {
            errors.push("Broken doc links found".to_string());
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

/// 搜索过滤改进示例
pub mod search_filter_examples {
    /// Rust 1.93 搜索过滤改进说明：
    ///
    /// 1. 宏搜索过滤现在包含 attribute 宏和 derive 宏
    /// 2. import 搜索过滤现在包含 extern crates
    ///
    /// 在生成的文档中：
    /// - 搜索 "macros" 会显示声明宏、attribute 宏、derive 宏
    /// - 搜索 "import" 会显示所有可导入的项，包括 extern crates

    /// 示例：attribute 宏
    pub use proc_macro::TokenStream;

    /// 示例 derive 宏
    #[proc_macro_derive(MyDerive)]
    pub fn my_derive(_input: TokenStream) -> TokenStream {
        TokenStream::new()
    }

    /// 示例 attribute 宏
    #[proc_macro_attribute]
    pub fn my_attr(_args: TokenStream, _input: TokenStream) -> TokenStream {
        TokenStream::new()
    }
}

/// 完整 CI/CD 配置示例
pub mod cicd_examples {
    /// GitHub Actions 配置
    pub const GITHUB_ACTIONS_YML: &str = r#"
name: Documentation

on:
  push:
    branches: [main]
  pull_request:
    branches: [main]

jobs:
  doc-check:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-action@stable

      - name: Check Documentation Attributes
        run: |
          RUSTDOCFLAGS="-D rustdoc::invalid_doc_attributes" \
            cargo doc --no-deps --all-features

      - name: Run Doc Tests
        run: cargo test --doc --all-features

      - name: Check Doc Links
        run: |
          cargo rustdoc --all-features -- \
            -D rustdoc::broken-intra-doc-links

  cargo-tree:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Install Rust
        uses: dtolnay/rust-action@stable

      - name: Generate Dependency Report
        run: |
          cargo tree --format "{p} [{l}]" > dependencies.txt
          cargo tree --duplicates > duplicates.txt

      - name: Upload Reports
        uses: actions/upload-artifact@v4
        with:
          name: dependency-reports
          path: |
            dependencies.txt
            duplicates.txt
"#;
}

/// 迁移辅助代码
pub mod migration_helpers {
    /// 从旧版本迁移的检查清单
    pub fn migration_checklist_from_1_92() -> Vec<&'static str> {
        vec![
            "移除所有 #![doc(document_private_items)] 使用",
            "检查 html_favicon_url/html_logo_url 等属性有效性",
            "验证 CARGO_CFG_DEBUG_ASSERTIONS 相关逻辑",
            "测试 cargo clean --workspace 功能",
            "更新 cargo tree 脚本使用新格式变量",
        ]
    }

    /// 检测已移除的文档属性
    pub fn check_removed_attrs(content: &str) -> Vec<String> {
        let mut issues = Vec::new();

        if content.contains("document_private_items") {
            issues.push(
                "发现已移除的 #![doc(document_private_items)]，请改用 cargo doc --document-private-items".to_string()
            );
        }

        issues
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_migration_checklist() {
        let checklist = migration_helpers::migration_checklist_from_1_92();
        assert_eq!(checklist.len(), 5);
    }

    #[test]
    fn test_removed_attr_detection() {
        let content = r#"#![doc(document_private_items)]"#;
        let issues = migration_helpers::check_removed_attrs(content);
        assert_eq!(issues.len(), 1);
    }
}
```

---

## 形式化规范链接

| 工具 | 配置参考 | 形式化规范 |
| :--- | :--- | :--- |
| Cargo | [Cargo Reference](https://doc.rust-lang.org/cargo/reference/) | [Manifest Format](https://doc.rust-lang.org/cargo/reference/manifest.html) |
| rustdoc | [Rustdoc Book](https://doc.rust-lang.org/rustdoc/) | [Doc Attributes](https://doc.rust-lang.org/reference/attributes/documentation.html) |
| Build Scripts | [Build Scripts](https://doc.rust-lang.org/cargo/reference/build-scripts.html) | [Environment Variables](https://doc.rust-lang.org/cargo/reference/environment-variables.html) |

---

**最后对照 releases.rs**: 2026-02-14
