//! Rust 1.97.0 stable 特性 —— 宏系统
//! Rust 1.97.0 stabilized features —— macro system
//!
//! 本文件展示与宏系统、编译期元编程相关的 Rust 1.97.0 stable 行为变更。
//! 当前工具链为 Rust 1.97.0，直接调用 stable API。
//! 权威列表见 `concept/07_future/rust_1_97_stabilized.md`。
//!
//! 注：本文件涉及的 1.97.0 变更（空 `export_name` 报错、`linker-messages` 默认 warn、
//! struct 模式拒绝元组索引简写）均为编译器/lint 行为变更，没有可直接切换的 runtime API，
//! 因此保留等效实现并更新注释。

/// # Rust 1.97 宏系统特性演示
/// # Rust 1.97 macro-system feature demonstration
///
/// 涉及特性：
/// - 空 `export_name` 在 Rust 1.97.0 中被明确拒绝（编译器行为变更，无 API）
/// - `linker-messages` lint 在 Rust 1.97.0 恢复默认 warn（lint 变更，无 API）
/// - Rust 1.97.0 在 struct 模式中拒绝元组索引简写（语法变更，无 API）
pub struct Rust197MacroFeatures;

impl Rust197MacroFeatures {
    /// 校验 `#[export_name = "..."]` 的值非空。
    ///
    /// Rust 1.97.0 起 `#[export_name = ""]` 会产生编译错误；
    /// 这里保留运行期检查以演示该行为变更。
    pub fn validate_export_name(name: &str) -> Result<(), &'static str> {
        if name.is_empty() {
            Err("export_name must not be empty (Rust 1.97.0 compile error)")
        } else {
            Ok(())
        }
    }

    /// 返回 `linker-messages` lint 的配置说明。
    ///
    /// Rust 1.97.0 将链接器输出消息从默认 allow 恢复为 warn-by-default。
    pub fn linker_messages_note() -> &'static str {
        r#"
Rust 1.97.0: linker-messages lint is warn-by-default.
To silence it, use: RUSTFLAGS="-A linker-messages" cargo build.
"#
    }

    /// 检查字段名列表是否包含元组索引简写（纯数字字段名）。
    ///
    /// Rust 1.97.0 在 struct 模式中拒绝 `let S { 0 }` 这类简写；
    /// 这里保留运行期检查以演示该语法变更。
    pub fn has_tuple_index_shorthand(fields: &[&str]) -> bool {
        fields.iter().any(|f| f.parse::<usize>().is_ok())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_validate_export_name() {
        assert!(Rust197MacroFeatures::validate_export_name("foo").is_ok());
        assert!(Rust197MacroFeatures::validate_export_name("").is_err());
    }

    #[test]
    fn test_linker_messages_note() {
        assert!(Rust197MacroFeatures::linker_messages_note().contains("linker-messages"));
    }

    #[test]
    fn test_tuple_index_shorthand() {
        assert!(Rust197MacroFeatures::has_tuple_index_shorthand(&[
            "name", "0"
        ]));
        assert!(!Rust197MacroFeatures::has_tuple_index_shorthand(&[
            "name", "age"
        ]));
    }
}
