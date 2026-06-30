# Rust 1.97.0 稳定特性 {#rust-1970-稳定特性}

> **内容重叠提示**: 本文与 [`knowledge/06_ecosystem/emerging/05_rust_1_96.md`](../../knowledge/06_ecosystem/emerging/05_rust_1_96.md) 内容高度重叠。`concept/` 版本为项目权威主轨；本文保留作为工具链参考。
> **内容重叠提示**: 本文与 [`concept/07_future/rust_1_96_stabilized.md`](../../concept/07_future/rust_1_96_stabilized.md) 内容高度重叠。`concept/` 版本为项目权威主轨；本文保留作为工具链参考。
> **状态**: 预迁移草稿 — 正式发布日（2026-07-09）根据官方 Release Notes 最终确认勾选。
> **Rust 版本**: 1.97.0 stable（预计 2026-07-09）
> **对应预览文档**: `../../concept/07_future/rust_1_97_preview.md`
> **发布日执行清单**: `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`
> **API 激活指南**: `.kimi/RUST_197_API_ACTIVATION_GUIDE.md`
> **探测报告**: `../../reports/RUST_197_API_PROBE_2026_06_28.md`
> **代码示例**: `../../crates/c08_algorithms/src/rust_197_features.rs`

---

## 已确认进入 1.97.0 的标准库 API {#已确认进入-1970-的标准库-api}

以下 API 已合并至 Rust 1.97.0 milestone，且在当前 nightly 上无需 feature gate 即可编译。
发布日主要工作：移除代码示例中的等效实现注释、核对 Release Notes、将 `rust,ignore` 改为 `rust`。

### NonZero 位操作：`highest_one` / `lowest_one` / `bit_width` {#nonzero-位操作highest_one-lowest_one-bit_width}

```rust
use std::num::NonZeroU32;

let n = NonZeroU32::new(0b10100).unwrap();

// 最高 set bit 的索引
assert_eq!(n.highest_one(), 4);

// 最低 set bit 的索引
assert_eq!(n.lowest_one(), 2);

// 表示 self 所需的最少位数（返回同类型 NonZero）
assert_eq!(n.bit_width(), NonZeroU32::new(5).unwrap());
```

### `char::is_control()` const 稳定化 {#charis_control-const-稳定化}

```rust
const SPACE_CTRL: bool = ' '.is_control(); // false
const NUL_CTRL: bool = '\0'.is_control();  // true

assert!(!SPACE_CTRL);
assert!(NUL_CTRL);
```

### `NonZeroU32::midpoint` / `isqrt` {#nonzerou32midpoint-isqrt}

```rust
use std::num::NonZeroU32;

let a = NonZeroU32::new(10).unwrap();
let b = NonZeroU32::new(20).unwrap();
assert_eq!(a.midpoint(b).get(), 15);

let n = NonZeroU32::new(25).unwrap();
assert_eq!(n.isqrt().get(), 5);
```

### `ptr::fn_addr_eq` {#ptrfn_addr_eq}

```rust
fn sample() {}
let f: fn() = sample;

assert!(std::ptr::fn_addr_eq(f, f));
```

### `const mem::size_of_val` / `const mem::align_of_val` {#const-memsize_of_val-const-memalign_of_val}

```rust
const fn size_and_align<T>(val: &T) -> (usize, usize) {
    (std::mem::size_of_val(val), std::mem::align_of_val(val))
}

let x = 42u64;
assert_eq!(size_and_align(&x), (8, 8));
```

### `BuildHasherDefault::new` const {#buildhasherdefaultnew-const}

```rust
use std::collections::hash_map::DefaultHasher;
use std::hash::BuildHasherDefault;

const _BH: BuildHasherDefault<DefaultHasher> = BuildHasherDefault::new();

let bh = BuildHasherDefault::<DefaultHasher>::new();
let mut hasher = bh.build_hasher();
hasher.write_u32(123);
let _ = hasher.finish();
```

---

## Beta Cutoff 风险 / 可能推迟至 1.98 的 API {#beta-cutoff-风险-可能推迟至-198-的-api}

以下 API 在当前 nightly（1.98.0）已可用，但 Rust 1.97 beta 于 **2026-05-22** 从 master 分支，因此存在未进入 1.97.0 stable 的风险。发布日需按 Release Notes 核对：

- [ ] `Box::as_ptr` / `Box::as_mut_ptr`
- [ ] `int::format_into`（`core::fmt::NumBuffer`）

若 Release Notes 未包含，保留等效实现并标注为 **1.98 稳定**。

---

## 仍未进入 1.97.0 的 API {#仍未进入-1970-的-api}

以下 API 在当前 nightly 上仍不稳定或方法不存在，预计推迟至 1.98.0 或更晚：

- `VecDeque::truncate_front` — 仍不稳定，需 `#![feature(vec_deque_truncate_front)]`
- `VecDeque::retain_back` — 方法不存在
- `Box::into_non_null` / `Vec::into_non_null` — 仍不稳定或方法不存在

代码中的等效实现应继续保留，并在发布日后纳入 1.98 跟踪。

---

## 语言与编译器 {#语言与编译器}

Rust 1.97.0 的语言特性以稳定化和细节修正为主，当前预览文档中列出的主要语言特性（如 Async Drop、RTN、Pin Ergonomics、Open Enums 等）均处于 nightly / MCP / RFC 阶段，**未进入 1.97.0 stable**。发布日根据 Release Notes 补充此处。

---

## Cargo / rustdoc / 工具链 {#cargo-rustdoc-工具链}

发布日根据 Release Notes 补充此处。当前可预填的候选项包括：

- Cargo 对 keywords in cfgs 的未来不兼容警告
- rustdoc 渲染改进

---

## 发布日迁移步骤 {#发布日迁移步骤}

1. 访问 <https://blog.rust-lang.org/2026/07/09/Rust-1.97.0.html> 核对实际稳定特性。
2. 根据 Release Notes 勾选上方复选框，将稳定的 API 代码块改为可编译 `rust`。
3. 将未稳定的 API 从本文件移至 `concept/07_future/rust_1_98_preview.md`。
4. 在 `concept/07_future/rust_1_97_preview.md` 顶部添加重定向说明。
5. 更新 `CHANGELOG.md [3.1.0]` 和 `concept/00_meta/terminology_glossary.md`。
6. 运行 `cargo check --workspace`、`cargo test --workspace`、`cargo clippy --workspace --all-features -- -D warnings`。

---

*本草稿生成于 2026-06-28，随发布日执行清单同步更新。*