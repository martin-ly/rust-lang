# Rust 1.98.0 API 候选 Nightly 探测报告

> **探测日期**: 2026-06-28
> **工具链**: `rustc 1.98.0-nightly (ce9954c0c 2026-06-26)`
> **探测脚本**: `scripts/probe_rust_198_apis.rs`
> **探测方式**: 直接调用 `rustc --edition 2024` 编译临时片段，不使用任何 feature gate

---

## 探测结果总览

| 指标 | 数值 |
|---|---|
| 候选 API 总数 | 17 |
| 当前 nightly 已可用 | 11 |
| 仍不可用 / 需要 feature gate | 6 |

---

## 已可用 API（11 项）

| # | API | 说明 |
|---|---|---|
| 1 | `i32::isqrt` | 有符号整数平方根 |
| 2 | `u32::isqrt` | 无符号整数平方根 |
| 3 | `ptr::with_exposed_provenance` | 暴露 provenance 的指针构造 |
| 4 | `ptr::without_provenance` | 无 provenance 的指针构造 |
| 5 | `ptr::dangling` | 悬空对齐指针 |
| 6 | `Ipv6Addr::is_unique_local` / `is_unicast_link_local` | IPv6 地址分类辅助方法 |
| 7 | `CStr::from_bytes_until_nul` | 从字节构造 CStr（遇第一个 NUL 停止）|
| 8 | `std::ffi::FromBytesUntilNulError` | `from_bytes_until_nul` 错误类型 |
| 9 | `std::pin::pin!` | 栈上 pin 宏 |
| 10 | `impl From<bool> for f32 / f64` | 布尔到浮点转换 |
| 11 | `Waker::noop` | 无操作 Waker（返回 `&Waker`）|

---

## 不可用 API（6 项）

| # | API | 当前状态 |
|---|---|---|
| 1 | `Pin::as_deref_mut` | 方法不存在（可能仍在设计或未合并） |
| 2 | `NonZeroI32::isqrt` | 仅 `NonZero<u*>` 提供 `isqrt`，有符号版本未实现 |
| 3 | `Vec::into_non_null` | 方法不存在（`box_vec_non_null` feature 下仍不稳定） |
| 4 | `Box::into_non_null` | 仍不稳定，需 `#![feature(box_vec_non_null)]` |
| 5 | `VecDeque::truncate_front` | 仍不稳定，需 `#![feature(vec_deque_truncate_front)]` |
| 6 | `VecDeque::retain_back` | 方法不存在 |

---

## 与 Rust 1.97.0 的关联

以下 4 项原本是 Rust 1.97.0 的候选 API，但在当前 nightly 仍未稳定，预计推迟到 **1.98.0 或更晚**：

- `Vec::into_non_null`
- `Box::into_non_null`
- `VecDeque::truncate_front`
- `VecDeque::retain_back`

代码中已保留等效实现，发布日需根据官方 Release Notes 决定是否切换。

---

## 结论与建议

1. **1.98.0 候选 API 中约 65%（11/17）在当前 nightly 已可用**，这些 API 有较大概率进入 1.98.0 stable。
2. **Pin ergonomics 相关 API（`Pin::as_deref_mut`）** 仍在快速演进，建议继续跟踪官方 Pin ergonomics project goal，不要提前在教学内容中承诺具体签名。
3. **`NonZeroI32::isqrt` 缺失** 属于对称性缺口，可关注 `rust-lang/rust` issue 是否会在后续补齐。
4. **推迟自 1.97.0 的 4 项 API** 仍需保留 fallback 实现，并在 1.97.0 发布后继续跟踪其 1.98.0 状态。

---

## 复现命令

```bash
rustc --edition 2024 scripts/probe_rust_198_apis.rs -o /tmp/probe_198
/tmp/probe_198
```

---

*本报告由 `scripts/probe_rust_198_apis.rs` 自动生成，仅供参考。最终稳定 API 集合以 Rust 官方 Release Notes 为准。*
