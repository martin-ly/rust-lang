# AFIDT / dynosaur / WASI 目标状态再确认报告（2026-07-09）

> **EN**: AFIDT / dynosaur / WASI Target Reconfirmation Report (2026-07-09)
> **Summary**: 重新确认 AFIDT、dynosaur 与 WASI 相关 Rust 目标在 2026-07-09 的 stable/nightly 状态，并同步更新 `concept/` 中的对应页面。
> **关联任务**: P2-Q3 2026 / P2-8
> **来源**: [rust-lang/rust#133119](https://github.com/rust-lang/rust/issues/133119) · [crates.io/dynosaur](https://crates.io/crates/dynosaur) · [Rust Platform Support](https://doc.rust-lang.org/rustc/platform-support.html) · [Rust 1.82 WASI blog](https://blog.rust-lang.org/2024/11/26/wasip2-tier-2/)

---

## 1. 评估环境

- **评估日期**: 2026-07-09
- **rustc 版本**: `1.96.1 (31fca3adb 2026-06-26)`
- **已安装目标**（`rustup target list --installed`）:
  - `wasm32-unknown-unknown`
  - `wasm32-wasip1`
  - `wasm32-wasip2`
  - `x86_64-pc-windows-msvc` / `x86_64-unknown-linux-gnu` / `aarch64-apple-darwin` 等主机目标

---

## 2. AFIDT（async fn in dyn trait）状态

| 问题 | 结论 |
|---|---|
| 是否在 stable Rust 中可用？ | **否**。Rust 1.96.1 stable 下，含 `async fn` 的 trait 仍不是 dyn-compatible。 |
| 是否需要 feature gate？ | 是。nightly 需 `#![feature(async_fn_in_dyn_trait)]`，且编译器提示其为 **incomplete feature**。 |
| 跟踪 issue | [rust-lang/rust#133119](https://github.com/rust-lang/rust/issues/133119) |
| 预计稳定时间 | 未确定。Rust Project Goals 2026 仍将 AFIDT / `.box` notation 列为关键目标，依赖 new trait solver 进展。 |

**验证命令**:

```bash
# stable (1.96.1) -> 报错 E0038：trait 不是 dyn-compatible
rustc --edition 2021 - <<'EOF'
trait Greeter { async fn greet(&self); }
fn use_dyn(g: &dyn Greeter) { let _ = g.greet(); }
EOF

# nightly -> 仍报错，需配合设计模式或 dynosaur
rustc +nightly --edition 2021 - <<'EOF'
#![feature(async_fn_in_dyn_trait)]
trait Greeter { async fn greet(&self); }
fn use_dyn(g: &dyn Greeter) { let _ = g.greet(); }
EOF
```

**结论**: AFIDT 仍是 **nightly 实验性功能**，不适合生产代码。

---

## 3. dynosaur 状态

| 指标 | 状态 |
|---|---|
| 最新版本 | `0.3.1`（stable） |
| crates.io max stable | `0.3.1` |
| MSRV | `1.75.0` |
| 兼容性 | 可在 stable Rust 使用 |
| 作用 | 为含 `async fn` 或 `-> impl Trait` 的 trait 生成 `DynTrait`，实现动态分发（动态路径仍会 box 返回值） |

**结论**: `dynosaur` 是 **stable 可用的 AFIDT polyfill**，适合在需要 `dyn Trait` 又不想使用 `async-trait` 全场景 boxing 时代码使用。本项目当前未使用 dynosaur，但可将其作为未来 AFIDT 稳定前的过渡方案记录。

---

## 4. WASI 目标状态

| 目标名 | 对应 WASI 版本 | Rust 状态 | 说明 |
|---|---|---|---|
| `wasm32-wasi` | WASI 0.1 / Preview 1 | **已在 Rust 1.84 移除** | 旧目标名，现已不可用 |
| `wasm32-wasip1` | WASI 0.1 / Preview 1 | Tier 2，可用 | 旧 `wasm32-wasi` 的正式继任名称 |
| `wasm32-wasip2` | WASI 0.2 / Preview 2 | **Tier 2 自 Rust 1.82**（2024-10-17） | 组件模型（Component Model）目标，可直接生成 WASI 0.2 组件 |
| `wasm32-wasip1-threads` | WASI 0.1 + threads | Tier 2 | 带线程支持的 WASI 0.1 变体 |
| `wasm64-*` / WASI 0.3 | WASI 0.3 / Preview 3 | **开发中，未稳定** | 原生异步 I/O 与进一步组件能力，尚在标准化阶段 |

**关键事实**:

- `wasm32-wasip2` 自 **Rust 1.82** 起从 Tier 3 提升为 **Tier 2**，可通过 `rustup target add wasm32-wasip2` 安装。
- 旧目标 `wasm32-wasi` 已在 **Rust 1.84** 彻底移除；未迁移的项目升级到 1.84+ 会收到目标不存在错误。
- WASI 0.2（Preview 2）接口已由 Bytecode Alliance 于 2024-01-25 正式发布，目前处于 **稳定可用** 状态。
- WASI 0.3（Preview 3）仍在开发，主要特性为原生异步 I/O，尚未进入 Rust stable toolchain 的默认支持。

---

## 5. `concept/` 页面更新

根据再确认结果，对以下页面做了最小化事实更新：

1. **`concept/03_advanced/01_async/02_async.md`**
   - 在“AFIT 限制与注意事项”中补充：截至 2026-07-09，Rust 1.96.1 stable 仍不支持 AFIDT；nightly 仍需 `#![feature(async_fn_in_dyn_trait)]` 且为 incomplete feature。
   - 明确 `dynosaur 0.3.1` 为 stable 兼容方案。

2. **`concept/06_ecosystem/05_systems_and_embedded/08_wasi.md`**
   - 变更日志新增 `v1.1 (2026-07-09)`：确认 `wasm32-wasip2` 为 Rust Tier 2、`wasm32-wasi` 已在 Rust 1.84 移除、当前 stable 1.96.1 提供 `wasm32-wasip1`/`wasm32-wasip2`。

3. **`concept/07_future/03_preview_features/47_wasm_target_evolution.md`**
   - 在顶部生态状态提示中补充 2026-07-09 再确认结论：`wasm32-wasip2` 为 Tier 2、`wasm32-wasi` 已移除。

---

## 6. 建议

| 主题 | 建议 |
|---|---|
| AFIDT | **继续观望**。不在项目代码中使用；教学中标注为 nightly experimental。 |
| dynosaur | 可作为 `dyn Trait + async fn` 需求的 **stable 过渡方案**；若后续需要动态分发异步 trait，优先评估 dynosaur 0.3.1。 |
| WASI 目标 | 新示例/部署统一使用 **`wasm32-wasip2`**；任何残留 `wasm32-wasi` 引用应立即改为 `wasm32-wasip1` 或 `wasm32-wasip2`。 |
| WASI 0.3 | 保持跟踪，但不纳入当前项目依赖；待 Rust 提供稳定目标与标准库支持后再评估。 |

---

*本报告作为 P2-8 的验收产出，随上游状态变化持续更新。*
