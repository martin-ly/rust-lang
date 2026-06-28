// Rust 1.98.0 API 候选可用性探测程序
// 用法（在任意 Rust 环境下）:
//   rustc --edition 2024 scripts/probe_rust_198_apis.rs -o /tmp/probe_198 && /tmp/probe_198
// 本程序通过调用 rustc 编译临时片段来探测 API，主程序始终退出码 0，
// 适合在 CI 中作为信息性步骤运行。

use std::env;
use std::fs;
use std::process::Command;

fn probe(name: &str, code: &str) -> bool {
    let out_dir = env::temp_dir().join("rust_lang_probe_198");
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
    println!("Probing Rust 1.98.0 candidate APIs...\n");

    let mut results = Vec::new();

    results.push((
        "Pin::as_deref_mut",
        probe(
            "Pin::as_deref_mut",
            r#"
use std::pin::Pin;
fn main() {
    let mut s = String::from("hi");
    let mut pin: Pin<&mut String> = Pin::new(&mut s);
    let _r: &mut String = pin.as_deref_mut();
}
"#,
        ),
    ));

    results.push((
        "i32::isqrt",
        probe(
            "i32::isqrt",
            r#"
fn main() {
    assert_eq!(25i32.isqrt(), 5);
}
"#,
        ),
    ));

    results.push((
        "u32::isqrt",
        probe(
            "u32::isqrt",
            r#"
fn main() {
    assert_eq!(25u32.isqrt(), 5);
}
"#,
        ),
    ));

    results.push((
        "NonZeroI32::isqrt",
        probe(
            "NonZeroI32::isqrt",
            r#"
use std::num::NonZeroI32;
fn main() {
    let n = NonZeroI32::new(25).unwrap();
    assert_eq!(n.isqrt().get(), 5);
}
"#,
        ),
    ));

    results.push((
        "ptr::with_exposed_provenance",
        probe(
            "ptr::with_exposed_provenance",
            r#"
fn main() {
    let addr = 0usize;
    let _ptr: *const u8 = unsafe { std::ptr::with_exposed_provenance(addr) };
}
"#,
        ),
    ));

    results.push((
        "ptr::without_provenance",
        probe(
            "ptr::without_provenance",
            r#"
fn main() {
    let _ptr: *const u8 = std::ptr::without_provenance::<u8>(0);
}
"#,
        ),
    ));

    results.push((
        "ptr::dangling",
        probe(
            "ptr::dangling",
            r#"
fn main() {
    let _ptr: *const u8 = std::ptr::dangling::<u8>();
}
"#,
        ),
    ));

    results.push((
        "Ipv6Addr::is_unique_local / is_unicast_link_local",
        probe(
            "Ipv6Addr_is_unique_local",
            r#"
use std::net::Ipv6Addr;
fn main() {
    let addr = Ipv6Addr::new(0xfc00, 0, 0, 0, 0, 0, 0, 1);
    let _ = addr.is_unique_local();
    let _ = addr.is_unicast_link_local();
}
"#,
        ),
    ));

    results.push((
        "CStr::from_bytes_until_nul",
        probe(
            "CStr::from_bytes_until_nul",
            r#"
use std::ffi::CStr;
fn main() {
    let bytes = b"hello\0world";
    let _ = CStr::from_bytes_until_nul(bytes);
}
"#,
        ),
    ));

    results.push((
        "FromBytesUntilNulError type",
        probe(
            "FromBytesUntilNulError type",
            r#"
use std::ffi::FromBytesUntilNulError;
fn foo(_e: FromBytesUntilNulError) {}
fn main() {}
"#,
        ),
    ));

    results.push((
        "std::pin::pin! macro",
        probe(
            "std::pin::pin! macro",
            r#"
use std::pin::pin;
fn main() {
    let _pinned = pin!(42);
}
"#,
        ),
    ));

    results.push((
        "impl From<bool> for f32 / f64",
        probe(
            "From bool for float",
            r#"
fn main() {
    let _x: f32 = true.into();
    let _y: f64 = false.into();
}
"#,
        ),
    ));

    results.push((
        "Waker::noop",
        probe(
            "Waker::noop",
            r#"
use std::task::Waker;
fn main() {
    let _waker: &Waker = Waker::noop();
}
"#,
        ),
    ));

    // 1.97 推迟到 1.98 的跟踪项
    results.push((
        "Vec::into_non_null",
        probe(
            "Vec::into_non_null",
            r#"
fn main() {
    let v = vec![1, 2, 3];
    let _non_null = Vec::into_non_null(v);
}
"#,
        ),
    ));

    results.push((
        "Box::into_non_null",
        probe(
            "Box::into_non_null",
            r#"
fn main() {
    let b = Box::new(42);
    let _non_null = Box::into_non_null(b);
}
"#,
        ),
    ));

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

    let available = results.iter().filter(|(_, ok)| *ok).count();
    let total = results.len();

    println!(
        "\nProbe complete: {}/{} candidate Rust 1.98.0 APIs available on this toolchain.",
        available, total
    );
}
