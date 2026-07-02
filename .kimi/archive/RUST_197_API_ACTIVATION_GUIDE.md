# Rust 1.97.0 API 激活指南

> **目标文件**: `crates/c08_algorithms/src/rust_197_features.rs`
> **探测脚本**: `scripts/probe_rust_197_apis.rs`
> **执行脚本**: `scripts/rust_197_release_day.sh`
> **对应清单**: `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`

---

## 激活原则

1. **必须以 Rust 1.97.0 官方 Release Notes 为唯一权威来源**。
2. 仅当 Release Notes 明确列出某 API 已稳定，才取消注释真实调用并删除等效实现。
3. 若 API 未进入 1.97.0，保留等效实现，并将注释更新为 `推迟至 1.98`。
4. 激活后在 **nightly** 工具链上运行 `cargo check -p c08_algorithms` 和 `cargo test -p c08_algorithms`。

> **工具链说明**: workspace 因多处使用 nightly feature gates 无法整体切换到 1.97.0 stable。`c08_algorithms` 本身也声明了 `#![feature(gen_blocks, yield_expr)]`，因此只能在 nightly 上编译。1.97.0 已稳定的 API 在 nightly 上同样可用，文档中标注其为 1.97.0 stable 即可。

---

## API 激活对照表

### 1. NonZero 位操作 API

| 项目 | 内容 |
|---|---|
| 函数 | `demo_nonzero_bit_ops` |
| 等效实现行 | 24 ~ 28 |
| 真实 API 行 | 18 ~ 22（已注释） |
| 激活操作 | 取消注释 17~21 行；删除 23~27 行及分隔注释 |
| 验证 | `cargo test -p c08_algorithms test_nonzero_bit_ops` |
| Fallback | 若未稳定，保留 23~27 行等效实现 |

### 2. `char::is_control()` const

| 项目 | 内容 |
|---|---|
| 函数 | `demo_char_is_control_const` |
| 等效实现行 | 44 ~ 48 |
| 真实 API 行 | 39 ~ 41（已注释） |
| 激活操作 | 取消注释 38~40 行；删除 42~46 行 |
| 验证 | `cargo test -p c08_algorithms test_char_is_control_const` |

### 3. `VecDeque::truncate_front`

| 项目 | 内容 |
|---|---|
| 函数 | `demo_vecdeque_truncate_front` |
| 等效实现行 | 72 ~ 76 |
| 真实 API 行 | 67 ~ 69（已注释） |
| 激活操作 | 取消注释 65~67 行；删除 69~73 行 |
| 验证 | `cargo test -p c08_algorithms test_vecdeque_truncate_front` |
| 边界 | 空 deque、`n >= len`、`n = 0` |

### 4. `VecDeque::retain_back`

| 项目 | 内容 |
|---|---|
| 函数 | `demo_vecdeque_retain_back` |
| 等效实现行 | 95 ~ 102 |
| 真实 API 行 | 90 ~ 92（已注释） |
| 激活操作 | 若 Release Notes 确认稳定，取消注释 87~89 行；删除 91~98 行 |
| 验证 | `cargo test -p c08_algorithms test_vecdeque_retain_back` |
| Fallback | 若未稳定，更新顶部注释为 `推迟至 1.98`，保留等效实现 |

### 5. `Box::as_ptr`

| 项目 | 内容 |
|---|---|
| 函数 | `demo_box_as_ptr` |
| 等效实现行 | 228 ~ 232 |
| 真实 API 行 | 220 ~ 223（已注释） |
| 激活操作 | 若 Release Notes 确认稳定，取消注释 220~223 行；删除 225~232 行 |
| 验证 | `cargo test -p c08_algorithms test_box_as_ptr` |
| Fallback | 若未稳定，更新注释为 `推迟至 1.98`，保留等效实现 |

### 6. `int::format_into`

| 项目 | 内容 |
|---|---|
| 函数 | `demo_int_format_into` |
| 等效实现行 | 252 ~ 260 |
| 真实 API 行 | 246 ~ 249（已注释） |
| 激活操作 | 若 Release Notes 确认稳定，取消注释 246~249 行；删除 251~260 行 |
| 验证 | `cargo test -p c08_algorithms test_int_format_into` |
| Fallback | 若未稳定，更新注释为 `推迟至 1.98`，保留等效实现 |

---

## 快速 sed 命令（仅供参考，发布日核对后使用）

```bash
# 仅当确认所有四个 API 都稳定后才可一次性运行
cd crates/c08_algorithms/src

# NonZero bit ops
sed -i '/当前等效实现 (Rust 1.96):/,/assert_eq!(u32::BITS - n.leading_zeros(), 5);/d' rust_197_features.rs
sed -i 's|// let n = NonZeroU32::new(0b10100).unwrap();|let n = NonZeroU32::new(0b10100).unwrap();|' rust_197_features.rs
sed -i 's|// assert_eq!(n.highest_one(), 4);|assert_eq!(n.highest_one(), 4);|' rust_197_features.rs
sed -i 's|// assert_eq!(n.lowest_one(), 2);|assert_eq!(n.lowest_one(), 2);|' rust_197_features.rs
sed -i 's|// assert_eq!(n.bit_width(), NonZeroU32::new(5).unwrap());|assert_eq!(n.bit_width(), NonZeroU32::new(5).unwrap());|' rust_197_features.rs

# char::is_control const
sed -i '/当前等效实现 (Rust 1.96):/,/assert!(nul_ctrl);/d' rust_197_features.rs
sed -i "s|// const _SPACE_CTRL: bool = ' '.is_control();|const _SPACE_CTRL: bool = ' '.is_control();|" rust_197_features.rs
sed -i "s|// const _NUL_CTRL: bool = '\\0'.is_control();|const _NUL_CTRL: bool = '\\0'.is_control();|" rust_197_features.rs

# VecDeque::truncate_front
sed -i '/当前等效实现:/,/assert_eq!(deque.make_contiguous(), \&\[4, 5\]);/d' rust_197_features.rs
sed -i 's|// deque.truncate_front(2);|deque.truncate_front(2);|' rust_197_features.rs

# VecDeque::retain_back
sed -i '/当前等效实现（从尾部遍历）:/,/assert_eq!(deque.make_contiguous(), \&\[2, 4\]);/d' rust_197_features.rs
sed -i 's|// deque.retain_back(|x| x % 2 == 0);|deque.retain_back(|x| x % 2 == 0);|' rust_197_features.rs
```
---

## 发布日执行顺序

1. 运行 `scripts/rust_197_release_day.sh`。
2. 根据探测脚本输出确认哪些 API 可用。
3. 核对 Release Notes。
4. 按本指南逐条激活。
5. 运行 `cargo check -p c08_algorithms`。
6. 运行 `cargo test -p c08_algorithms`。
7. 继续执行 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` 阶段 4~8。

---

*本指南与 `crates/c08_algorithms/src/rust_197_features.rs` 当前版本（2026-06-28）对齐。*
