//! modern-app 二进制入口。
//!
//! 由于 modern-app 同时依赖 legacy-lib（indexmap 1.x）和自身的 indexmap 2.x，
//! 最终依赖图中会同时存在两个 major 版本的 indexmap。

fn main() {
    println!(
        "modern-app: legacy_count={}, modern_count={}",
        legacy_lib::legacy_ordered_count(),
        modern_app::modern_ordered_count(),
    );

    let args = <legacy_lib::LegacyArgs as clap::Parser>::parse();
    println!("verbose: {}", args.verbose);
}
