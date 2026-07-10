# Rust 1.90–1.93 特性速查表 {#rust-190193-特性速查表}

<!-- canonical-normalized 2026-07-11 -->
> **权威来源（Canonical）**: 本文件为Rust 1.90–1.93 特性速查表（版本速查）；通用 Rust 概念解释请以 concept 权威页为准：[`concept 版本跟踪`](../../../concept/07_future/00_version_tracking/05_rust_version_tracking.md)
>
> 根据 AGENTS.md §2 Canonical 规则：本文仅保留本文独特内容（1.90–1.93 特性快速参考与迁移检查清单（速查，非概念正文）），不重复 concept/ 中的概念定义、规则与定理推导。

> **EN**: Rust 190 To 193 Features Cheatsheet
> **Summary**: Rust 1.90–1.93 特性速查表 Rust 190 To 193 Features Cheatsheet.
> **分级**: [A]
> **Bloom 层级**: L2
> **版本**: Rust 1.90.0 – 1.93.1
> **更新日期**: 2026-05-29
> **适用版本**: stable
> **版本勘误说明**:
>
> - 本表覆盖 Rust 1.90 至 1.93.1 的累积特性，按版本分组。
> - 部分 API 在更早版本已稳定，本表仅作为文档归类便利。
>
> **受众**: [初学者] / [进阶]
> **内容分级**: [综述级]

---

## 目录 {#目录}

- [Rust 1.90–1.93 特性速查表 {#rust-190193-特性速查表}](#rust-190193-特性速查表-rust-190193-特性速查表)
  - [目录 {#目录}](#目录-目录)
  - [快速参考 {#快速参考}](#快速参考-快速参考)
  - [Rust 1.90 (2025-09) {#rust-190-2025-09}](#rust-190-2025-09-rust-190-2025-09)
    - [LLD 默认链接器 {#lld-默认链接器}](#lld-默认链接器-lld-默认链接器)
    - [`cargo publish --workspace` {#cargo-publish---workspace}](#cargo-publish---workspace-cargo-publish---workspace)
  - [Rust 1.91 (2025-10) {#rust-191-2025-10}](#rust-191-2025-10-rust-191-2025-10)
    - [平台支持升级 {#平台支持升级}](#平台支持升级-平台支持升级)
    - [新 Lint：`dangling_pointers_from_locals` {#新-lintdangling\_pointers\_from\_locals}](#新-lintdangling_pointers_from_locals-新-lintdangling_pointers_from_locals)
  - [Rust 1.92 (2025-12) {#rust-192-2025-12}](#rust-192-2025-12-rust-192-2025-12)
    - [Never 类型 Lint 严格化 {#never-类型-lint-严格化}](#never-类型-lint-严格化-never-类型-lint-严格化)
    - [标准库新 API {#标准库新-api}](#标准库新-api-标准库新-api)
  - [Rust 1.93 (2026-01) {#rust-193-2026-01}](#rust-193-2026-01-rust-193-2026-01)
    - [musl 1.2.5 {#musl-125}](#musl-125-musl-125)
    - [`asm_cfg`：汇编行级 cfg {#asm\_cfg汇编行级-cfg}](#asm_cfg汇编行级-cfg-asm_cfg汇编行级-cfg)
    - [标准库 API 稳定化 {#标准库-api-稳定化}](#标准库-api-稳定化-标准库-api-稳定化)
    - [兼容性变更 {#兼容性变更}](#兼容性变更-兼容性变更)
  - [迁移检查清单 {#迁移检查清单}](#迁移检查清单-迁移检查清单)
  - [相关链接 {#相关链接}](#相关链接-相关链接)

---

## 快速参考 {#快速参考}

> **来源: [Rust Official Docs](https://doc.rust-lang.org/)**

| 版本 | 日期 | 核心特性 |
|------|------|----------|
| **1.90** | 2025-09 | LLD 默认链接器、`cargo publish --workspace` |
| **1.91** | 2025-10 | aarch64-windows Tier 1、`dangling_pointers_from_locals` lint |
| **1.92** | 2025-12 | Never 类型 lint 严格化、`Box::new_zeroed` |
| **1.93** | 2026-01 | musl 1.2.5、`asm_cfg`、大量标准库 API |

---

## Rust 1.90 (2025-09) {#rust-190-2025-09}

> **[来源: [Rust Blog](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)]**

### LLD 默认链接器 {#lld-默认链接器}

`x86_64-unknown-linux-gnu` 目标默认使用 LLD 链接器，提升链接速度。

```toml
# Cargo.toml（无需配置，默认生效） {#cargotoml无需配置默认生效}
# 如需显式指定： {#如需显式指定}
[target.x86_64-unknown-linux-gnu]
linker = "lld"
```

### `cargo publish --workspace` {#cargo-publish---workspace}

一键发布 workspace 中所有可发布的 crate。

```bash
# 发布 workspace 中所有符合条件的 crate {#发布-workspace-中所有符合条件的-crate}
cargo publish --workspace

# dry-run 预览 {#dry-run-预览}
cargo publish --workspace --dry-run
```

---

## Rust 1.91 (2025-10) {#rust-191-2025-10}

> **[来源: [Rust Blog](https://blog.rust-lang.org/2025/10/30/Rust-1.91.0/)]**

### 平台支持升级 {#平台支持升级}

| 目标 | 变更 |
|------|------|
| `aarch64-pc-windows-msvc` | 升级为 **Tier 1** |

### 新 Lint：`dangling_pointers_from_locals` {#新-lintdangling_pointers_from_locals}

```rust,ignore
// ⚠️ warn-by-default
fn example() {
    let ptr = {
        let local = 42;
        &local as *const i32 // 警告：指针在 local 离开作用域后悬空
    };
}
```

---

## Rust 1.92 (2025-12) {#rust-192-2025-12}

> **[来源: [Rust Blog](https://blog.rust-lang.org/2025/12/11/Rust-1.92.0/)]**

### Never 类型 Lint 严格化 {#never-类型-lint-严格化}

| Lint | 旧级别 | 新级别 |
|------|--------|--------|
| `never_type_fallback_flowing_into_unsafe` | warn | **deny** |
| `dependency_on_unit_never_type_fallback` | warn | **deny** |

### 标准库新 API {#标准库新-api}

| API | 说明 |
|-----|------|
| `Box::new_zeroed` | 创建零初始化的 Box |
| `Rc::new_zeroed` | 创建零初始化的 Rc |
| `Arc::new_zeroed` | 创建零初始化的 Arc |

```rust
use std::boxed::Box;

let zeroed: Box<u64> = Box::new_zeroed();
```

---

## Rust 1.93 (2026-01) {#rust-193-2026-01}

> **[[Rust Blog [已失效]]<!-- 原链接: https://blog.rust-lang.org/2026/01/xx/Rust-1.93.0/ -->](https://blog.rust-lang.org/)**

### musl 1.2.5 {#musl-125}

musl 目标升级至 1.2.5，DNS 解析改进。

### `asm_cfg`：汇编行级 cfg {#asm_cfg汇编行级-cfg}

```rust
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
pub unsafe fn cpuid() {
    unsafe {
        std::arch::asm!(
            "cpuid",
            // 行级 cfg 在 1.93+ 可用
            lateout("eax") _,
            lateout("ebx") _,
            lateout("ecx") _,
            lateout("edx") _,
            options(nomem, nostack),
        );
    }
}
```

### 标准库 API 稳定化 {#标准库-api-稳定化}

| API | 说明 |
|-----|------|
| `MaybeUninit::as_mut_ptr` | 获取 MaybeUninit 的裸指针 |
| `String::into_raw_parts` / `from_raw_parts` | 原始部件转换 |
| `Vec::into_raw_parts` / `from_raw_parts` | 原始部件转换 |
| `VecDeque::truncate` / `resize` | 截断/调整大小 |
| `Duration::as_millis_f64` 等 | 浮点持续时间转换 |
| `char::to_ascii_uppercase` / `to_ascii_lowercase` const | ASCII 大小写转换 const 化 |

### 兼容性变更 {#兼容性变更}

| 变更 | 影响 |
|------|------|
| `deref_nullptr` | 升级为 **deny** |
| `#[test]` 无效位置 | 硬错误 |
| `offset_of!` 改进 | 支持更多场景 |

---

## 迁移检查清单 {#迁移检查清单}

- [ ] 确认 Rust 版本 ≥ 1.96.1（本速查表为历史归档，特性已在 1.96.1 中稳定可用）
- [ ] 检查 `dangling_pointers_from_locals` lint 警告
- [ ] 检查 never type 相关 lint（`never_type_fallback_flowing_into_unsafe`）
- [ ] 评估 `Box::new_zeroed` 等 API 替换机会
- [ ] 更新 CI 中的 Rust 版本

---

## 相关链接 {#相关链接}

- [Rust 1.90.0 Release](https://blog.rust-lang.org/2025/09/18/Rust-1.90.0/)
- [Rust 1.91.0 Release](https://blog.rust-lang.org/2025/10/30/Rust-1.91.0/)
- [Rust 1.92.0 Release](https://blog.rust-lang.org/2025/12/11/Rust-1.92.0/)
- [Rust 1.93.0 Release [已失效]]<!-- 原链接: https://blog.rust-lang.org/2026/01/xx/Rust-1.93.0/ -->
- [Rust 1.94 特性速查表](02_rust_194_features_cheatsheet.md)
- [Rust 1.95 特性速查表](02_rust_195_features_cheatsheet.md)
- [Rust 版本跟踪](../../../concept/07_future/00_version_tracking/05_rust_version_tracking.md)

---

> **权威来源**: [Rust Standard Library](https://doc.rust-lang.org/std/), [Rust Reference](https://doc.rust-lang.org/reference/), [The Rust Programming Language](https://doc.rust-lang.org/book/)
>
> **文档版本**: 1.0
> **对应 Rust 版本**: 1.90.0–1.93.1 stable
> **最后更新**: 2026-05-29
> **状态**: ✅ 已完成
