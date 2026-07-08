//! 模拟一个要求 Rust 1.84 的新应用库。
//!
//! 设计要点：
//! - `legacy-lib`、`bitflags`、`serde` 均为公共依赖，因为它们的类型出现在本 crate 公共 API 中。
//! - `indexmap` 仅内部使用，标记为 `public = false`。

use legacy_lib::LegacyFlags;
use serde::{Deserialize, Serialize};

bitflags::bitflags! {
    /// 新组件公开的扩展标志位。
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct ModernFlags: u32 {
        /// 异步能力。
        const ASYNC = 4;
    }
}

/// 在公共 API 中返回 legacy-lib 的 `LegacyFlags` 与本 crate 的 `ModernFlags`。
/// 因为 `legacy-lib` 与 `bitflags` 都是公共依赖，这种暴露是合法的。
pub fn combined_flags() -> (LegacyFlags, ModernFlags) {
    (LegacyFlags::READ, ModernFlags::ASYNC)
}

/// 公共可序列化记录；`serde` 是公共依赖，因此 `Serialize`/`Deserialize` 出现在公共 API 中。
#[derive(Serialize, Deserialize, Debug)]
pub struct Record {
    pub id: u64,
    pub name: String,
}

/// 返回新组件内部维护的 ordered map 条目数。
pub fn ordered_count() -> usize {
    let mut m = indexmap::IndexMap::new();
    m.insert("modern", 2);
    m.len()
}
