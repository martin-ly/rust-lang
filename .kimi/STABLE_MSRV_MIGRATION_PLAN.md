# Stable MSRV 迁移计划

> **目标**: 让 `rust-toolchain.toml` 与 CI 使用 stable 工具链（MSRV 1.96.0），同时保留 nightly 预览内容的可选构建路径。
> **创建日期**: 2026-06-28
> **状态**: 计划中 / 待执行

---

## 1. 当前矛盾

- `rust-toolchain.toml` 锁定 `nightly`
- `Cargo.toml` 声明 MSRV `1.96.0`
- CI 使用 `dtolnay/rust-toolchain@nightly`
- 仓库中存在 13 处活跃 `#![feature(...)]` gate，分布在 8 个 crate

## 2. 活跃 feature gate 清单

| Crate | 文件 | Feature | 状态/用途 |
|-------|------|---------|-----------|
| `exercises` | `src/lib.rs` | `gen_blocks`, `yield_expr` | 生成器/协程预览 |
| `c04_generic` | `src/lib.rs` | `gen_blocks`, `yield_expr` | 生成器/协程预览 |
| `c08_algorithms` | `src/lib.rs` | `gen_blocks`, `yield_expr` | 生成器/协程预览 |
| `c08_algorithms` | `src/lib.rs` | `portable_simd` (cfg_attr) | SIMD 预览 |
| `c02_type_system` | `src/lib.rs` | `never_type` | `!` 类型 |
| `c02_type_system` | `src/lib.rs` | `derive_coerce_pointee` | `#[derive(CoercePointee)]` |
| `c02_type_system` | `src/type_system_frontier.rs` | `type_alias_impl_trait` | TAIT |
| `c02_type_system` | `src/type_system_frontier.rs` | `negative_impls` | 负实现 |
| `c06_async` | `src/lib.rs` | `async_iterator`, `async_for_loop` | 异步迭代 |
| `c13_embedded` | `src/lib.rs` | `core_intrinsics`, `fn_align` | 内联函数对齐 |
| `c04_generic` | `src/field_projections_preview.rs` | `field_projections` | Pin 字段投影 |

## 3. 迁移策略（建议方案 C：混合）

### 3.1 移除/改写可在 stable 实现的用法

- `never_type`：将 `Result<T, !>` 等用法改为 `Result<T, Infallible>` 或移除相关演示
- `type_alias_impl_trait`：TAIT 已在 1.75 稳定，但当前 nightly 仍要求 gate；可评估是否可改写为具体类型或保留 gate
- `gen_blocks` / `yield_expr`：改写为稳定迭代器/状态机实现

### 3.2 对无法稳定的预览特性启用 `nightly` Cargo feature

- 每个受影响的 crate 增加可选 `nightly` feature
- lib 顶部使用 `#![cfg_attr(feature = "nightly", feature(...))]`
- nightly-only 模块使用 `#[cfg(feature = "nightly")]` 包裹
- 默认构建（无 `nightly` feature）在 stable 上通过

### 3.3 工具链与 CI

- `rust-toolchain.toml`: `channel = "1.96.0"`
- `.github/workflows/ci.yml`: `RUST_VERSION: 1.96.0`，setup 使用 `dtolnay/rust-toolchain@stable` 或指定版本
- 保留一个可选的 `nightly` CI job，启用 `nightly` feature 验证预览内容

## 4. 风险

- 改写生成器/协程示例可能损失教学表达
- `portable_simd` 在 stable 上无直接替代，必须保留为 nightly-only
- 需要同步更新文档中“需要 nightly”的说明

## 5. 验收标准

- `cargo +stable build --workspace` 通过
- `cargo +stable test --workspace` 通过
- `cargo +stable clippy --workspace --tests --all-features -- -D warnings` 通过
- `cargo +nightly build --workspace --features nightly` 仍能通过（保留预览路径）

---

*本计划需在执行前与用户确认策略（尤其是 nightly-only 内容的保留方式）。*
