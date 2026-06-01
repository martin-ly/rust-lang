//! Rust 1.97 特性跟踪模块 —— 进程与 FFI
//! Rust 1.97 feature module —— process and FFI
#![allow(clippy::incompatible_msrv)]

use std::fs::{File, FileTimes};
use std::io;
use std::time::SystemTime;

/// # Rust 1.97 进程/文件系统特性演示
/// # Rust 1.97 process /file system feature demonstration
///
/// Rust 1.97 稳定化的核心文件系统与进程 API：
/// Rust 1.97 core file system and process API：
/// - `FileTimes` / `FileTimesExt` / `File::set_modified` / `File::set_times`
/// - `io::ErrorKind::QuotaExceeded` / `CrossesDevices`
/// - `Default` for `ExitCode`
pub struct Rust197ProcessFeatures;

impl Rust197ProcessFeatures {
    /// 使用 `FileTimes` 构建文件时间修改请求
    /// `FileTimes` time
    ///
    /// `FileTimes` 允许原子地设置文件的访问时间和修改时间。
    /// `FileTimes` time and time 。
    pub fn build_file_times(
        accessed: Option<SystemTime>,
        modified: Option<SystemTime>,
    ) -> FileTimes {
        let times = FileTimes::new();
        if let Some(t) = accessed {
            let _ = times.set_accessed(t);
        }
        if let Some(t) = modified {
            let _ = times.set_modified(t);
        }
        times
    }

    /// 使用 `File::set_times` 原子更新文件时间戳
    /// `File::set_times` time
    pub fn update_file_times(path: &str, times: FileTimes) -> io::Result<()> {
        let file = File::options().write(true).open(path)?;
        file.set_times(times)
    }

    /// 使用 `File::set_modified` 快捷设置修改时间
    /// use `File::set_modified` fastset time
    pub fn set_modified_time(path: &str, time: SystemTime) -> io::Result<()> {
        let file = File::options().write(true).open(path)?;
        file.set_modified(time)
    }

    /// 创建 `io::ErrorKind::QuotaExceeded` 错误
    /// create `io::ErrorKind::QuotaExceeded` error
    /// represent 。
    pub fn quota_exceeded_error() -> io::ErrorKind {
        io::ErrorKind::QuotaExceeded
    }

    /// 创建 `io::ErrorKind::CrossesDevices` 错误
    /// create `io::ErrorKind::CrossesDevices` error
    /// represent edge （for example file system rename）。
    pub fn crosses_devices_error() -> io::ErrorKind {
        io::ErrorKind::CrossesDevices
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_build_file_times() {
        let now = SystemTime::now();
        let times = Rust197ProcessFeatures::build_file_times(Some(now), Some(now));
        // FileTimes 内部状态无法直接检查，但确保构造不 panic
        let _ = times;
    }

    #[test]
    fn test_quota_exceeded_error() {
        assert_eq!(
            Rust197ProcessFeatures::quota_exceeded_error(),
            io::ErrorKind::QuotaExceeded
        );
    }

    #[test]
    fn test_crosses_devices_error() {
        assert_eq!(
            Rust197ProcessFeatures::crosses_devices_error(),
            io::ErrorKind::CrossesDevices
        );
    }

    #[test]
    fn test_error_kind_display() {
        let err = io::Error::new(io::ErrorKind::QuotaExceeded, "disk quota exceeded");
        assert_eq!(err.kind(), io::ErrorKind::QuotaExceeded);
    }
}
