//! Rust 1.97 Nightly 前瞻/候选特性 —— 过程宏辅助
//! Rust 1.97.0 stabilized features —— procedural macro helpers
//!
//! 本文件展示与过程宏实现相关的 Rust 1.97.0 Nightly 前瞻/候选特性。
//! 当前工具链为 Rust 1.96.1，所有 1.97 新行为均保留在注释中；
//! 可执行代码使用语义等价的 1.96.1 兼容实现。
//! 权威列表见 `concept/07_future/rust_1_97_stabilized.md`。
//!
//! 注：本文件涉及的 1.97 变更（空 `export_name` 报错、`linker-messages` 默认 warn、
//! struct 模式拒绝元组索引简写）均为编译器/lint 行为变更，没有可直接切换的 runtime API，
//! 因此不采用 `#[cfg(nightly)]` 分支，保留垫片并更新注释。
#![allow(clippy::incompatible_msrv, dead_code)]
#![allow(unexpected_cfgs)]
#![allow(clippy::borrowed_box)]

/// # Rust 1.97 过程宏辅助特性
/// # Rust 1.97 procedural-macro helper features
///
/// 涉及特性：
/// - 空 `export_name` 在 Rust 1.97 中被明确拒绝（编译器行为变更，无 API）
/// - `linker-messages` lint 在 Rust 1.97 恢复默认 warn（lint 变更，无 API）
/// - Rust 1.97 在 struct 模式中拒绝元组索引简写（语法变更，无 API）
pub struct Rust197Features;

impl Rust197Features {
    /// 判断给定的 `export_name` 字符串在 Rust 1.97 下是否合法。
    ///
    /// Rust 1.97: `#[export_name = ""]` 产生编译错误。
    pub fn is_valid_export_name(name: &str) -> bool {
        !name.is_empty()
    }

    /// 返回 `linker-messages` lint 的配置说明。
    ///
    /// Rust 1.97 将链接器输出消息从默认 allow 恢复为 warn-by-default。
    pub fn linker_messages_doc() -> &'static str {
        r#"
Rust 1.97+: linker-messages lint is warn-by-default.
Use RUSTFLAGS="-A linker-messages" to keep silence.
"#
    }

    /// 检查字段名列表是否包含元组索引简写（纯数字字段名）。
    ///
    /// Rust 1.97 在 struct 模式中拒绝 `let S { 0 }` 这类简写。
    pub fn has_numeric_field_name(fields: &[&str]) -> bool {
        fields.iter().any(|f| f.parse::<usize>().is_ok())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_valid_export_name() {
        assert!(Rust197Features::is_valid_export_name("foo"));
        assert!(!Rust197Features::is_valid_export_name(""));
    }

    #[test]
    fn test_linker_messages_doc() {
        assert!(Rust197Features::linker_messages_doc().contains("linker-messages"));
    }

    #[test]
    fn test_has_numeric_field_name() {
        assert!(Rust197Features::has_numeric_field_name(&["name", "0"]));
        assert!(!Rust197Features::has_numeric_field_name(&["name", "age"]));
    }
}
