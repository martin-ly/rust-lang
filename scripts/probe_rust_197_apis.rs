// Rust 1.97.0 API 可用性探测程序
// 用法（在任意 Rust 环境下）:
//   rustc --edition 2024 scripts/probe_rust_197_apis.rs -o /tmp/probe_197 && /tmp/probe_197
// 本程序通过调用 rustc 编译临时片段来探测 API，主程序始终退出码 0，
// 适合在 CI 中作为信息性步骤运行。

use std::env;
use std::fs;
use std::process::Command;

fn probe(name: &str, code: &str) -> bool {
    let out_dir = env::temp_dir().join("rust_lang_probe_197");
    fs::create_dir_all(&out_dir).unwrap();

    let crate_name = format!("probe_{}", name.replace(|c: char| !c.is_alphanumeric(), "_"));
    let src = out_dir.join(format!("{}.rs", crate_name));
    let exe = out_dir.join(&crate_name);

    fs::write(&src, code).unwrap();

    let status = Command::new("rustc")
        .args([
            "--edition",
            "2024",
            "--crate-name",
            &crate_name,
            src.to_str().unwrap(),
            "-o",
            exe.to_str().unwrap(),
        ])
        .status();

    match status {
        Ok(s) if s.success() => {
            println!("✅ {}", name);
            true
        }
        _ => {
            println!("❌ {} (not stable or signature mismatch)", name);
            false
        }
    }
}

fn main() {
    println!("Probing Rust 1.97.0 APIs...\n");

    let mut results = Vec::new();

    results.push((
        "VecDeque::truncate_front",
        probe(
            "VecDeque::truncate_front",
            r#"
use std::collections::VecDeque;
fn main() {
    let mut deque: VecDeque<i32> = [1, 2, 3, 4, 5].into_iter().collect();
    deque.truncate_front(2);
    assert_eq!(deque.make_contiguous(), &[4, 5]);
}
"#,
        ),
    ));

    results.push((
        "VecDeque::retain_back",
        probe(
            "VecDeque::retain_back",
            r#"
use std::collections::VecDeque;
fn main() {
    let mut deque: VecDeque<i32> = [1, 2, 3, 4, 5].into_iter().collect();
    deque.retain_back(|x| x % 2 == 0);
    assert_eq!(deque.make_contiguous(), &[2, 4]);
}
"#,
        ),
    ));

    results.push((
        "NonZero bit ops",
        probe(
            "NonZero bit ops",
            r#"
use std::num::NonZeroU32;
fn main() {
    let n = NonZeroU32::new(0b10100).unwrap();
    let _ = n.highest_one();
    let _ = n.lowest_one();
    let _ = n.bit_width();
}
"#,
        ),
    ));

    results.push((
        "const char::is_control",
        probe(
            "const char::is_control",
            r#"
const _SPACE_CTRL: bool = ' '.is_control();
const _NUL_CTRL: bool = '\0'.is_control();
fn main() {}
"#,
        ),
    ));

    let available = results.iter().filter(|(_, ok)| *ok).count();
    let total = results.len();

    println!(
        "\nProbe complete: {}/{} expected Rust 1.97.0 APIs available on this toolchain.",
        available, total
    );
}
