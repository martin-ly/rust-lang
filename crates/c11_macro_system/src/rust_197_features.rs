//! Rust 1.97 特性跟踪模块 —— 宏系统与构建
#![allow(clippy::incompatible_msrv)]

/// # Rust 1.97 宏系统与构建特性演示
///
/// Rust 1.97 稳定化的 Cargo 构建相关改进：
/// - `CARGO_CFG_FEATURE` 环境变量传递给 build scripts
/// - cfg 中关键字 future-incompatibility warning
/// - higher precedence trailing flags
///
/// **注意**: 以下代码展示的是概念性用法，实际 build script 需要在 `build.rs` 中运行。
pub struct Rust197MacroFeatures;

impl Rust197MacroFeatures {
    /// 演示如何在 build script 中使用 `CARGO_CFG_FEATURE`
    ///
    /// 在 `build.rs` 中可以通过 `env::var("CARGO_CFG_FEATURE")` 获取
    /// 当前启用的 feature 列表（逗号分隔）。
    pub fn cargo_cfg_feature_doc() -> &'static str {
        r#"
        // In build.rs:
        use std::env;

        fn main() {
            if let Ok(features) = env::var("CARGO_CFG_FEATURE") {
                for feature in features.split(',') {
                    println!("cargo:rustc-cfg=has_feature_{}", feature);
                }
            }
        }
        "#
    }

    /// 演示 cfg 中关键字的 future-incompatibility warning
    ///
    /// Rust 1.97 开始对 cfg 条件中的关键字（如 `cfg(target_os = "windows")` 中的
    /// `target_os`）引入 future-incompatibility warning。
    pub fn cfg_keyword_warning_doc() -> &'static str {
        r#"
        // 使用 raw-ident 避免关键字冲突（Rust 1.97+ 推荐）:
        #[cfg(target_has_atomics = "64")]
        // 或
        #[cfg(r#type = "mytype")]  // 如果 "type" 是自定义 cfg 键
        "#
    }

    /// 演示 higher precedence trailing flags
    ///
    /// Cargo 1.97 稳定化了尾部标志的更高优先级解析规则。
    pub fn trailing_flags_doc() -> &'static str {
        r#"
        // 在 Cargo.toml 的 [target.'cfg(...)'.linker] 配置中，
        // 尾部标志现在具有更高优先级。
        // 
        // 例如:
        // [target.x86_64-pc-windows-msvc]
        // linker = "lld-link"
        // rustflags = ["/subsystem:console"]
        "#
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_cargo_cfg_feature_doc() {
        let doc = Rust197MacroFeatures::cargo_cfg_feature_doc();
        assert!(doc.contains("CARGO_CFG_FEATURE"));
    }

    #[test]
    fn test_cfg_keyword_warning_doc() {
        let doc = Rust197MacroFeatures::cfg_keyword_warning_doc();
        assert!(doc.contains("raw-ident"));
    }

    #[test]
    fn test_trailing_flags_doc() {
        let doc = Rust197MacroFeatures::trailing_flags_doc();
        assert!(doc.contains("linker"));
    }
}
