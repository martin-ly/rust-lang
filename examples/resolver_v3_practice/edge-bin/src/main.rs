//! edge-bin 二进制入口。
//!
//! 它依赖 legacy-lib（MSRV 1.70）与 modern-app（MSRV 1.84），
//! 但自身声明 MSRV 1.96。resolver v3 会以 workspace 中最低的 MSRV（1.70）
//! 作为依赖版本选择约束，从而演示 MSRV-aware 解析。

use legacy_lib::LegacyFlags;
use modern_app::Record;

fn main() {
    let record = Record {
        id: 42,
        name: "edge".to_string(),
    };
    let serialized = serde_json::to_string(&record).expect("serialize");

    println!(
        "edge-bin: flags={:?} -> {}",
        LegacyFlags::READ | LegacyFlags::WRITE,
        serialized,
    );

    println!(
        "edge-bin: counts legacy={}, modern={}",
        legacy_lib::ordered_count(),
        modern_app::ordered_count(),
    );
}
