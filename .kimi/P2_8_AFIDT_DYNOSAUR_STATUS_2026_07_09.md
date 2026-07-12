# P2-8: AFIDT / dynosaur 状态更新

> **评估日期**: 2026-07-09
> **评估范围**: `crates/` 中 `async_trait`、`dynosaur`、AFIDT 相关代码与文档
> **AFIDT 跟踪 Issue**: [rust-lang/rust#133119](https://github.com/rust-lang/rust/issues/133119)
> **dynosaur 最新版本**: `0.3.1`（2026-07-03 发布）
> **状态**: AFIDT 仍为 nightly 实验性；`dynosaur` 已提供 stable 兼容方案；代码侧继续保留 `async_trait`

---

## 1. AFIDT 当前状态

### 1.1 跟踪 Issue

- **正确跟踪 Issue**: [#133119](https://github.com/rust-lang/rust/issues/133119) `Tracking Issue for async_fn_in_dyn_trait`
- **标签**: `T-lang`、`T-types`、`C-tracking-issue`、`B-experimental`、`F-async_fn_in_dyn_trait`
- **状态**: 🟡 **Open**，实验性阶段
- **已完成**:
  - ✅ Lang experiment 批准
  - ✅ Nightly 实现（[#133122](https://github.com/rust-lang/rust/pull/133122)）
- **尚未完成**:
  - ⬜ RFC 接受
  - ⬜ Dev guide / Reference / Style guide 文档
  - ⬜ 稳定化（Stabilize）

> **注意**: 项目早期文档中曾引用 `#133882`，该 issue 实际与 AFIDT 无关；本次更新统一为 `#133119`。

### 1.2 功能概要

AFIDT（async fn in dyn trait）允许在 trait object `dyn Trait` 中直接使用 `async fn`，解决 Rust 1.75 稳定的 AFIT（async fn in trait）不支持动态分发的问题。需要 nightly feature gate：

```rust
#![feature(async_fn_in_dyn_trait)]
```

### 1.3 稳定性判断

- 截至 2026-07-09，AFIDT **未进入任何 stable 版本**。
- 早期预估的 "1.97–1.98" 稳定窗口仍未达成；RFC 与文档步骤尚未完成。
- 建议继续按 **实验性特性** 处理，不承诺生产可用时间。

---

## 2. dynosaur 当前状态

### 2.1 版本信息

| 版本 | 发布日期 | 说明 |
|:---|:---|:---|
| `0.3.1` | 2026-07-03 | 最新稳定版 |
| `0.3.0` | 2026-05 月 | 增加 `no_std` 支持 |

- **MSRV**: `1.75.0`
- **License**: MIT OR Apache-2.0
- **仓库**: [spastorino/dynosaur](https://github.com/spastorino/dynosaur)
- **crates.io**: [dynosaur](https://crates.io/crates/dynosaur)

### 2.2 功能定位

`dynosaur` 是一个过程宏，为返回 `impl Trait`（包括 `async fn`）的 trait 生成 dyn-compatible 的包装类型，允许在 **stable Rust** 上实现类似 AFIDT 的动态分发。

示例（概念）:

```rust
use dynosaur::dynosaur;

#[dynosaur(DynMyTrait)]
trait MyTrait {
    async fn method(&self) -> i32;
}

fn use_dyn(obj: &DynMyTrait<'_>) -> impl std::future::Future<Output = i32> + '_ {
    obj.method()
}
```

### 2.3 与 `async_trait` 的对比

| 维度 | `async_trait` | `dynosaur` |
|:---|:---|:---|
| 稳定性 | ✅ Stable | ✅ Stable |
| 额外依赖 | `async-trait` | `dynosaur` |
| 性能 | 每次调用 Box<dyn Future> 分配 | 同样基于类型擦除，开销类似 |
| Send bound | 自动添加，可能过度约束 | 可更精确控制 |
| 生态成熟度 | 广泛使用（Axum 旧版、tonic 等） | 较新，用户基础较小 |
| 代码侵入性 | 低（属性宏） | 中（需为 trait 生成 Dyn 包装） |

---

## 3. 本项目当前使用

### 3.1 `async_trait` 使用情况

`async_trait` 在本项目中使用广泛，主要用于需要在 `dyn Trait` 场景下做动态分发的教学与示例代码：

| 位置 | 说明 |
|:---|:---|
| `examples/microservice_template.rs` | `RequestHandler` 等策略 trait |
| `crates/c06_async/src/` | 多个高级工具、actor/reactor 模式、集成框架示例 |
| `crates/c06_async/examples/` | 综合异步模式示例 |
| `crates/c06_async/tests/` | 测试用 trait |
| `crates/c10_networks/src/protocol/async_traits.rs` | 网络协议 trait（注释说明 1.75+ 原生 AFIT） |
| `crates/c09_design_pattern/examples/async_trait_demo.rs` | 原生 async trait 演示（非 `async_trait` crate） |
| `crates/common/src/traits/mod.rs` | `async_traits` 子模块 |

### 3.2 AFIDT / dynosaur 使用

- **AFIDT**: `crates/c06_async/src/afit_dyn_tracking.rs` 是一个 `#[cfg(nightly)]` 预览模块，仅在 nightly 工具链下编译。
- **dynosaur**: 未使用。

---

## 4. 推荐行动

### 4.1 保持 `async_trait`（推荐）

- **原因**:
  - `async_trait` 稳定、成熟、生态广泛。
  - `dynosaur` 与 `async_trait` 同样引入类型擦除开销，迁移收益有限。
  - AFIDT 仍未稳定，无法作为生产方案。
- **做法**: 代码侧继续使用 `#[async_trait::async_trait]`；文档侧明确说明“动态分发场景仍需 `async_trait`，AFIDT 仍处 nightly 实验”。

### 4.2 继续关注 AFIDT

- 跟踪 [rust-lang/rust#133119](https://github.com/rust-lang/rust/issues/133119)。
- 当 AFIDT 进入 FCP / stabilisation report 阶段时，再评估是否准备迁移示例。

### 4.3 可选：小范围 `dynosaur` 试点

- 若未来需要展示“无 `async_trait` 的 dyn async trait”方案，可在 `crates/c06_async` 中新增一个可选示例，使用 `dynosaur 0.3.1`。
- **当前不建议**：会增加依赖面，且无迫切需求。

---

## 5. 已更新的项目文件

- `CHANGELOG.md`: 追加 AFIDT / dynosaur 状态摘要。
- `concept/03_advanced/01_async/01_async.md`:
  - 在 AFIT 限制小节补充 AFIDT 仍处 nightly 实验（#133119）与 `dynosaur` 稳定替代方案说明。
  - 在边界测试 10.4 修正/补充段落中更新动态分发现状。
- `knowledge/INDEX.md`: 修正 AFIDT 跟踪 issue 为 `#133119`。
- `crates/c06_async/src/afit_dyn_tracking.rs`: 顶部注释与迁移路径说明更新为“截至 2026-07-09 仍为 nightly 实验”。
- `crates/c06_async/src/lib.rs`: `async_trait` 使用说明中补充 AFIDT/dynosaur 当前状态。

---

## 6. 参考

- [rust-lang/rust#133119 — Tracking Issue for `async_fn_in_dyn_trait`](https://github.com/rust-lang/rust/issues/133119)
- [dynosaur on crates.io](https://crates.io/crates/dynosaur)
- [dynosaur GitHub Releases](https://github.com/spastorino/dynosaur/releases)
- [async-trait on crates.io](https://crates.io/crates/async-trait)
- [Rust 1.75 Release Notes — async fn in traits](https://blog.rust-lang.org/2023/12/28/Rust-1.75.0.html)
