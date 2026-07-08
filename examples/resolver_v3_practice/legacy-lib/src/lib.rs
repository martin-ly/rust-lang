//! 模拟一个需要支持 Rust 1.70 的旧库。
//!
//! 设计要点：
//! - `bitflags` 标记为 `public = true`，因为其类型出现在公共 API 中。
//! - `serde` 与 `indexmap` 标记为 `public = false`，仅用于内部实现。

use serde::{Deserialize, Serialize};

bitflags::bitflags! {
    /// 旧组件公开的权限标志位。
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct LegacyFlags: u32 {
        /// 读权限。
        const READ = 1;
        /// 写权限。
        const WRITE = 2;
    }
}

/// 内部配置类型；serde 是私有依赖，因此该类型不公开。
#[derive(Serialize, Deserialize)]
struct InternalConfig {
    name: String,
}

impl InternalConfig {
    fn example() -> Self {
        Self { name: "legacy".to_string() }
    }
}

/// 返回默认的公开标志位。
pub fn default_flags() -> LegacyFlags {
    // 私有依赖 `serde` 仅在本 crate 内部使用，不泄漏到公共 API。
    let _ = InternalConfig::example();
    LegacyFlags::READ
}

/// 返回内部维护的 ordered map 条目数；`indexmap` 是私有依赖。
pub fn ordered_count() -> usize {
    let mut m = indexmap::IndexMap::new();
    m.insert("legacy", 1);
    m.len()
}
