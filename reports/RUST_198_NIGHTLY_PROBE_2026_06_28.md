# Rust 1.98 Nightly API 探测报告（2026-06-28）

> **EN**: Rust 1.98 Nightly API Probe Report (2026-06-28)
> **Summary**: 使用 `rustc 1.98.0-nightly (2026-06-26)` 对 17 项候选 API 进行无 feature gate 编译探测的结果汇总。
> **来源**: [concept/07_future/rust_1_98_preview.md](../concept/07_future/rust_1_98_preview.md) · [Rust Project Goals 2026](https://rust-lang.github.io/rust-project-goals/2026/)

---

## 探测环境

- **rustc**: `1.98.0-nightly (2026-06-26)`
- **探测脚本**: [`scripts/probe_rust_198_apis.rs`](../scripts/probe_rust_198_apis.rs)
- **探测方式**: 在无 `feature gate` 条件下尝试编译调用候选 API

## 结果摘要

| 状态 | 数量 | 代表 API |
|---|---|---|
| ✅ 已可用 | 11 | `i32::isqrt`、`u32::isqrt`、`ptr::with_exposed_provenance`、`ptr::without_provenance`、`ptr::dangling`、`Ipv6Addr::is_unique_local`、`CStr::from_bytes_until_nul`、`std::pin::pin!`、`From<bool> for f32/f64`、`Waker::noop` |
| ❌ 仍不可用 | 6 | `Pin::as_deref_mut`、`NonZeroI32::isqrt`、`Vec::into_non_null`、`Box::into_non_null`、`VecDeque::truncate_front`、`VecDeque::retain_back` |

## 关键发现

- `i32::isqrt` 等整数平方根 API 已在 nightly 可用，预计进入 1.98.0 stable。
- Provenance 相关 API（`with_exposed_provenance`、`without_provenance`、`dangling`）已在 nightly 可用，是 strict provenance 迁移的重要信号。
- `Pin::as_deref_mut` 在当前 nightly 仍不存在，说明 Pin ergonomics 仍在演进，教学中应保持保守。
- 从 1.97.0 推迟的 `Box::into_non_null`、`Vec::into_non_null`、`VecDeque::truncate_front`、`VecDeque::retain_back` 仍未稳定，代码中需继续保留等效实现。

---

*本报告作为 `concept/07_future/rust_1_98_preview.md` 的配套探测记录，随 nightly 版本迭代持续更新。*
