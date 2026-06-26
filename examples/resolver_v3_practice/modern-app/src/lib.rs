//! 模拟一个要求 Rust 1.84 的新应用库。
//!
//! 它依赖 `indexmap = "2"`，与 legacy-lib 的 `indexmap = "1"` 共存，
//! 用于演示 `cargo tree --duplicates`。

use indexmap::IndexMap;

/// 返回新组件内部维护的 ordered map 条目数。
pub fn modern_ordered_count() -> usize {
    let mut m = IndexMap::new();
    m.insert("modern", 2);
    m.len()
}
