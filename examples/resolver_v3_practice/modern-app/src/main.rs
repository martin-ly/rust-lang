//! modern-app 二进制入口。

fn main() {
    let (legacy, modern) = modern_app::combined_flags();
    println!("modern-app: legacy={:?}, modern={:?}", legacy, modern);

    let record = modern_app::Record {
        id: 1,
        name: "modern".to_string(),
    };
    println!("modern-app: record={:?}", record);

    println!(
        "modern-app: ordered legacy={}, modern={}",
        legacy_lib::ordered_count(),
        modern_app::ordered_count(),
    );
}
