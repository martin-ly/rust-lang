# Rust 1.98.0 跟踪状态（2026-06-28）

> **创建日期**: 2026-06-28
> **当前工具链**: `rustc 1.98.0-nightly (ce9954c0c 2026-06-26)`
> **预计稳定发布**: 2026-09-04（以官方公告为准）
> **上游 beta cutoff**: 预计 2026-07-25 前后

---

## 当前状态

| 轨道 | 状态 |
|---|---|
| 探测脚本 | ✅ `scripts/probe_rust_198_apis.rs` 已创建 |
| Nightly 探测报告 | ✅ `reports/RUST_198_NIGHTLY_PROBE_2026_06_28.md` 已生成 |
| 概念预览更新 | ✅ `concept/07_future/rust_1_98_preview.md` 已增加探测结果小节 |
| 代码示例 | ⏳ 待 1.98.0 接近时在 `crates/c08_algorithms/src/rust_198_features.rs` 补充 |
| 练习与测验 | ✅ `exercises/tests/l3_rust_198_alignment.rs` 已创建，覆盖 12 个已可用 API |

---

## 探测结果摘要

- **17 项候选 API** 中 **11 项** 在当前 nightly 已无需 feature gate 编译。
- **6 项** 仍不可用或需 feature gate：
  - `Pin::as_deref_mut`
  - `NonZeroI32::isqrt`
  - `Vec::into_non_null`
  - `Box::into_non_null`
  - `VecDeque::truncate_front`
  - `VecDeque::retain_back`

---

## 从 1.97.0 推迟项的跟踪

以下 API 原计划 1.97.0，当前 nightly 仍未稳定，已纳入 1.98.0 跟踪：

| API | 当前状态 | 代码中的 fallback |
|---|---|---|
| `VecDeque::truncate_front` | 不稳定，需 feature gate | `pop_front` 循环等效实现 |
| `VecDeque::retain_back` | 方法不存在 | 反向 `remove` 等效实现 |
| `Box::into_non_null` | 不稳定，需 feature gate | `Box::into_raw` + `NonNull::new_unchecked` |
| `Vec::into_non_null` | 方法不存在 | `Vec::into_raw_parts` + `NonNull::new_unchecked` |

---

## 近期行动项

1. **2026-07-09 之后**: 在 Rust 1.97.0 发布稳定后，确认上述 4 项是否进入 1.98.0 beta。
2. **2026-07-25 前后**: 关注 beta cutoff，冻结 1.98.0 可稳定 API 集合预期。
3. **2026-08 月**: 根据 beta 状态，开始为 `crates/c08_algorithms/src/rust_198_features.rs` 编写代码示例与 fallback。
4. **2026-09-04 前后**: 发布日执行 1.98.0 激活检查（复用 `scripts/rust_197_release_day.sh` 模式）。

---

## 风险

- `Pin::as_deref_mut` 等 Pin ergonomics API 仍在设计阶段，签名可能变化，教学中不应提前承诺。
- `NonZeroI32::isqrt` 等对称 API 可能永远不会实现，等效实现应以 `i32::isqrt` + `NonZero::new` 包装为准。

---

*本文件随 nightly 探测与上游动态持续更新。*
