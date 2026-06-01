#![allow(clippy::incompatible_msrv)]

use std::io;

/// # Rust 1.97 控制流/错误处理特性演示
/// # Rust 1.97 stream /error handling feature demonstration
pub struct Rust197ControlFlowFeatures;

impl Rust197ControlFlowFeatures {
    /// 根据错误类型选择不同的恢复策略。
    /// according to error type strategy 。
    pub fn handle_io_error(err: &io::Error) -> &'static str {
        match err.kind() {
            io::ErrorKind::QuotaExceeded => "磁盘配额已耗尽，请清理空间或联系管理员",
            io::ErrorKind::CrossesDevices => "操作跨越设备边界，请使用 copy+delete 替代 rename",
            io::ErrorKind::NotFound => "文件未找到",
            io::ErrorKind::PermissionDenied => "权限不足",
            _ => "其他 I/O 错误",
        }
    }

    /// 适用于需要确定性哈希（如测试）或性能调优的场景。
    /// （）or performance scenario 。
    pub fn create_default_hasher()
    -> std::hash::BuildHasherDefault<std::collections::hash_map::DefaultHasher> {
        std::hash::BuildHasherDefault::new()
    }

    /// 根据错误类型判断是否应该重试
    /// according to error type should
    pub fn should_retry(err: &io::Error) -> bool {
        matches!(
            err.kind(),
            io::ErrorKind::Interrupted | io::ErrorKind::QuotaExceeded
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_handle_quota_error() {
        let err = io::Error::new(io::ErrorKind::QuotaExceeded, "no space");
        assert_eq!(
            Rust197ControlFlowFeatures::handle_io_error(&err),
            "磁盘配额已耗尽，请清理空间或联系管理员"
        );
    }

    #[test]
    fn test_handle_crosses_devices_error() {
        let err = io::Error::new(io::ErrorKind::CrossesDevices, "cross fs");
        assert_eq!(
            Rust197ControlFlowFeatures::handle_io_error(&err),
            "操作跨越设备边界，请使用 copy+delete 替代 rename"
        );
    }

    #[test]
    fn test_create_default_hasher() {
        let _hasher = Rust197ControlFlowFeatures::create_default_hasher();
        // BuildHasherDefault 构造成功即表示 API 可用
    }

    #[test]
    fn test_should_retry_quota() {
        let err = io::Error::new(io::ErrorKind::QuotaExceeded, "retry");
        assert!(Rust197ControlFlowFeatures::should_retry(&err));
    }

    #[test]
    fn test_should_not_retry_not_found() {
        let err = io::Error::new(io::ErrorKind::NotFound, "no retry");
        assert!(!Rust197ControlFlowFeatures::should_retry(&err));
    }
}
