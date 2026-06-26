//! 模拟一个需要支持 Rust 1.70 的旧库。
//!
//! 它同时依赖：
//! - `clap = "4"`：展示 resolver v3 的 MSRV 感知版本选择
//! - `indexmap = "1"`：与 modern-app 的 `indexmap = "2"` 形成重复依赖

use clap::Parser;
use indexmap::IndexMap;

/// 返回旧库内部维护的 ordered map 条目数。
pub fn legacy_ordered_count() -> usize {
    let mut m = IndexMap::new();
    m.insert("legacy", 1);
    m.len()
}

/// 旧库提供的命令行参数结构。
#[derive(Parser, Debug)]
#[command(name = "legacy")]
pub struct LegacyArgs {
    /// 是否打印详细日志。
    #[arg(short, long)]
    pub verbose: bool,
}
