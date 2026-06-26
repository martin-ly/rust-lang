//! edge-bin 二进制入口。
//!
//! 它依赖 legacy-lib（MSRV 1.70）与 modern-app（MSRV 1.84），
//! 但自身声明 MSRV 1.96。resolver 会以 workspace 中最低的 MSRV（1.70）为准。

fn main() {
    println!(
        "edge-bin: legacy_count={}, modern_count={}",
        legacy_lib::legacy_ordered_count(),
        modern_app::modern_ordered_count(),
    );
}
