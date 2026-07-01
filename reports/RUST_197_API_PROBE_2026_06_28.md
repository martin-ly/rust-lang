# Rust 1.97.0 API 可用性探测报告

> **探测日期**: 2026-06-28
> **工具链**: nightly-x86_64-pc-windows-msvc（rustc 1.98.0-nightly，built 2026-06-26）
> **探测脚本**: `scripts/probe_rust_197_apis.rs`
> **探测方式**: 使用 `rustc --edition 2024` 编译独立代码片段，不启用任何 nightly feature gate

---

## 汇总

- **可用**: 9 / 12
- **不可用**: 3 / 12

| API | 状态 | 备注 |
|:---|:---:|:---|
| `NonZero` bit ops (`highest_one` / `lowest_one` / `bit_width`) | ✅ | 无需 feature gate |
| `const char::is_control` | ✅ | 无需 feature gate |
| `NonZeroU32::midpoint` | ✅ | 无需 feature gate |
| `NonZeroU32::isqrt` | ✅ | 无需 feature gate |
| `ptr::fn_addr_eq` | ✅ | 无需 feature gate |
| `const size_of_val / align_of_val` | ✅ | 无需 feature gate |
| `BuildHasherDefault::new` const | ✅ | 无需 feature gate |
| `Box::as_ptr` | ✅ | 无需 feature gate；原 feature `box_as_ptr` |
| `int::format_into` | ✅ | 无需 feature gate；使用 `core::fmt::NumBuffer` |
| `VecDeque::truncate_front` | ❌ | 仍需 `#![feature(vec_deque_truncate_front)]` |
| `VecDeque::retain_back` | ❌ | 方法在当前 nightly 不存在（仅存在 `retain`） |
| `Vec::into_non_null` | ❌ | 方法在当前 nightly 不存在；相关 feature 为 `box_vec_non_null` |

---

## 影响与后续行动

### 已确认可用的 API

这些 API 在当前 nightly 上已无需 feature gate，有较大概率进入 Rust 1.97.0 stable（最终需以 2026-07-09 官方 Release Notes 为准）：

- `NonZero` 位操作、`const char::is_control`
- `NonZeroU32::midpoint` / `isqrt`
- `ptr::fn_addr_eq`
- `const size_of_val` / `align_of_val`
- `BuildHasherDefault::new` const
- `Box::as_ptr` / `Box::as_mut_ptr`
- `int::format_into`

### 仍不可用的 API

以下 API 在 2026-06-26 nightly 上仍不可用，**不应**在 1.97 发布日直接取消注释真实调用：

- `VecDeque::truncate_front` — 仍不稳定，保留 `while deque.len() > n { deque.pop_front(); }` 等效实现。
- `VecDeque::retain_back` — 方法在当前 nightly 不存在，可能已被移除或推迟；保留反向遍历等效实现。
- `Vec::into_non_null` — 方法不存在；保留 `Vec::as_ptr()` + `NonNull::new` 等效实现。

### 发布日复核项

1. 重新运行 `scripts/probe_rust_197_apis.rs`。
2. 对照官方 Release Notes 确认上述 API 是否稳定。
3. 仅对 Release Notes 明确标注为 1.97.0 stable 的 API 取消注释 `crates/c08_algorithms/src/rust_197_features.rs` 中的真实调用。
4. 未进入 1.97.0 的 API 更新注释为 "推迟至 1.98"，并同步更新 `CHANGELOG.md`。

---

## 命令

```bash
# 编译并运行探测脚本
rustc --edition 2024 scripts/probe_rust_197_apis.rs -o target/probe_197 && ./target/probe_197
```
## 参考

- Rust 1.97 Release Notes（发布后替换 URL）: <https://blog.rust-lang.org/2026/07/09/Rust-1.97.0.html>
- 发布日执行清单: `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`
- 倒计时排期: `.kimi/RUST_197_RELEASE_COUNTDOWN_2026_06_28.md`
