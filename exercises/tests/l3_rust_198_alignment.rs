#![cfg(feature = "nightly")]

//! L3 Rust 1.98.0 稳定特性对齐测验
//!
//! 覆盖 Rust 1.98.0（预计 2026-09-04 stable）引入的关键标准库 API：
//! - 整数平方根：`i32::isqrt` / `u32::isqrt` / `NonZeroU32::isqrt`
//! - Strict provenance 指针 API：`ptr::with_exposed_provenance` / `without_provenance` / `dangling`
//! - IPv6 地址分类：`Ipv6Addr::is_unique_local` / `is_unicast_link_local`
//! - CStr 构造：`CStr::from_bytes_until_nul`
//! - 栈上 pin：`std::pin::pin!`
//! - 布尔到浮点：`impl From<bool> for f32 / f64`
//! - 无操作 Waker：`Waker::noop`
//!
//! 对于仍在等待稳定化的 API（如 `Pin::as_deref_mut`、`VecDeque::truncate_front`、
//! `Box::into_non_null` 等），本测验暂不提供测试，待 1.98 beta cutoff 后根据
//! Release Notes 补充。
//!
//! 运行: cargo test --test l3_rust_198_alignment

use std::ffi::CStr;
use std::net::Ipv6Addr;
use std::num::NonZeroU32;
use std::pin::pin;
use std::ptr;
use std::task::Waker;

// ============================================================================
// 已可用 API 测验
// ============================================================================

/// 测验1: `i32::isqrt` — 有符号整数平方根
#[test]
fn test_i32_isqrt() {
    assert_eq!(25i32.isqrt(), 5);
    assert_eq!(0i32.isqrt(), 0);
    assert_eq!(26i32.isqrt(), 5);
}

/// 测验2: `u32::isqrt` — 无符号整数平方根
#[test]
fn test_u32_isqrt() {
    assert_eq!(25u32.isqrt(), 5);
    assert_eq!(0u32.isqrt(), 0);
    assert_eq!(u32::MAX.isqrt(), 65535);
}

/// 测验3: `NonZeroU32::isqrt` — 非零整数平方根
#[test]
fn test_nonzero_u32_isqrt() {
    let n = NonZeroU32::new(25).unwrap();
    assert_eq!(n.isqrt().get(), 5);
}

/// 测验4: `ptr::with_exposed_provenance` — 从地址重建带 provenance 的指针
#[test]
fn test_ptr_with_exposed_provenance() {
    let raw = 0usize;
    let _ptr: *const u8 = ptr::with_exposed_provenance(raw);
}

/// 测验5: `ptr::without_provenance` — 构造无 provenance 的指针
#[test]
fn test_ptr_without_provenance() {
    let _ptr: *const u8 = ptr::without_provenance::<u8>(0);
}

/// 测验6: `ptr::dangling` — 构造对齐的悬空指针
#[test]
fn test_ptr_dangling() {
    let _ptr: *const u8 = ptr::dangling::<u8>();
    let _ptr: *const u64 = ptr::dangling::<u64>();
}

/// 测验7: `Ipv6Addr::is_unique_local` — 唯一本地地址判断
#[test]
fn test_ipv6_is_unique_local() {
    let unique_local = Ipv6Addr::new(0xfc00, 0, 0, 0, 0, 0, 0, 1);
    assert!(unique_local.is_unique_local());

    let global = Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1);
    assert!(!global.is_unique_local());
}

/// 测验8: `Ipv6Addr::is_unicast_link_local` — 链路本地单播判断
#[test]
fn test_ipv6_is_unicast_link_local() {
    let link_local = Ipv6Addr::new(0xfe80, 0, 0, 0, 0, 0, 0, 1);
    assert!(link_local.is_unicast_link_local());

    let unique_local = Ipv6Addr::new(0xfc00, 0, 0, 0, 0, 0, 0, 1);
    assert!(!unique_local.is_unicast_link_local());
}

/// 测验9: `CStr::from_bytes_until_nul` — 遇第一个 NUL 停止构造 CStr
#[test]
fn test_cstr_from_bytes_until_nul() {
    let bytes = b"hello\0world";
    let cstr = CStr::from_bytes_until_nul(bytes).expect("valid C string");
    assert_eq!(cstr.to_str().unwrap(), "hello");
}

/// 测验10: `std::pin::pin!` — 栈上 pin 宏
#[test]
fn test_pin_macro() {
    let pinned = pin!(42);
    assert_eq!(*pinned, 42);
}

/// 测验11: `impl From<bool> for f32 / f64`
#[test]
fn test_bool_to_float() {
    let x: f32 = true.into();
    let y: f64 = false.into();
    assert_eq!(x, 1.0);
    assert_eq!(y, 0.0);
}

/// 测验12: `Waker::noop` — 无操作 Waker
#[test]
fn test_waker_noop() {
    let waker: &Waker = Waker::noop();
    // 多次调用不 panic、不产生副作用
    waker.wake_by_ref();
    waker.wake_by_ref();
}
