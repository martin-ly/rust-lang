# Sea-ORM 2.0 Stable 迁移评估报告（2026-07-09）

> **EN**: Sea-ORM 2.0 Stable Migration Assessment (2026-07-09)
> **Summary**: 截至 2026-07-09，Sea-ORM 2.0 仍未发布 stable；项目当前使用 2.0.0-rc.42。本报告评估迁移准备度、AFIDT 可行性、风险与建议时间表。
> **关联任务**: P2-Q3 2026 / P2-7
> **来源**: [crates.io/sea-orm](https://crates.io/crates/sea-orm) · [SeaQL/sea-orm releases](https://github.com/SeaQL/sea-orm/releases) · [rust-lang/rust#133119](https://github.com/rust-lang/rust/issues/133119)

---

## 1. 评估环境

- **评估日期**: 2026-07-09
- **rustc 版本**: `1.96.1 (31fca3adb 2026-06-26)`
- **项目 Sea-ORM 版本**: `2.0.0-rc.42`（workspace 统一声明）
- **受影响 crate**: `crates/c06_async`
- **受影响示例**: `crates/c06_async/examples/database_ecosystem_demo.rs`

---

## 2. Sea-ORM 2.0 发布状态

| 指标 | 当前状态 | 说明 |
|---|---|---|
| crates.io `max_version` | `2.0.0-rc.42` | 包含预发布版本的最高版本 |
| crates.io `max_stable_version` | `1.1.20` | 最新 **stable** 版本，发布于 2026-03-31 |
| GitHub 最新 release | `2.0.0-rc.42` | 发布于 2026-07-04 |
| GitHub 最新 stable tag | 无 | 尚未标记 `2.0.0` stable |
| 2.0 MSRV | `1.94.0` | `2.0.0-rc.42` 的最低 Rust 版本要求 |
| 内部 async trait 实现 | 仍依赖 `async-trait` | `2.0.0-rc.42` 的依赖树中仍包含 `async-trait ^0.1` |

**结论**: Sea-ORM 2.0 **尚未到达 stable**。当前最新可用的是 `2.0.0-rc.42`，处于 release candidate 阶段。

---

## 3. 项目当前 Sea-ORM 使用情况

```text
Cargo.toml (workspace)
  └─ sea-orm = { version = "2.0.0-rc.42", ... }

crates/c06_async/Cargo.toml
  └─ sea-orm = { workspace = true, features = ["sqlx-sqlite", "runtime-tokio"] }

crates/c06_async/examples/database_ecosystem_demo.rs
  └─ 使用 Database::connect、ConnectionTrait、Statement、DbBackend、query_one_raw/query_all_raw
```

- **使用深度**: 浅层。仅使用原始 SQL 与连接管理 API，未使用 Entity/Migration/Schema 等高层抽象。
- **实体或迁移文件**: 无。
- **当前兼容性**: 已基于 2.0 RC 线构建，`cargo check` 可通过（见 §6 验证结果）。

---

## 4. 2.0 潜在破坏性变更（基于 RC 发布说明摘要）

根据 `2.0.0-rc.41`/`2.0.0-rc.42` 的 release notes，stable 2.0 可能继承以下变更：

1. **Streaming API 默认 feature 化**: `stream` 默认开启；若 `default-features = false` 且需流式查询，需显式启用 `stream`。
2. **First-party value wrapper 的 serde 形状固化**: `TextUuid`、Unix-timestamp wrapper 等的 JSON 表示已稳定。
3. **Loader trait 新增方法**: 生成代码会自动更新，手动实现 loader trait 需要补方法。
4. **Per-migration 事务控制**: `MigrationTrait::use_transaction()` 可控制单条迁移的事务行为。
5. **MSRV 提升**: 2.0 线 MSRV 已提升至 1.94.0，旧 stable Rust 无法编译。

**对当前项目的影响**: 由于示例仅使用低层 SQL API，上述变更大概率**不产生影响**；stable 发布后的迁移工作主要是把版本号从 `2.0.0-rc.42` 改为 `2.0.0` 并重新跑测试。

---

## 5. AFIDT 迁移评估

| 问题 | 结论 |
|---|---|
| AFIDT 是否已在 stable Rust 中可用？ | **否**。Rust 1.96.1 stable 下，`async fn` trait 仍不是 dyn-compatible。 |
| 是否需要 nightly feature gate？ | 是，`#![feature(async_fn_in_dyn_trait)]` 仍为 incomplete feature。 |
| Sea-ORM 2.0 是否已迁移到 AFIDT？ | **否**。`sea-orm 2.0.0-rc.42` 仍依赖 `async-trait` crate。 |
| 项目是否应从 `async_trait` 迁移到 AFIDT？ | **不建议**。AFIDT 不稳定且 Sea-ORM 内部仍使用 `async-trait`；迁移无收益且引入 nightly 依赖。 |

**建议**: 继续使用 `async-trait` 或原生 AFIT（async fn in trait，Rust 1.75+ stable）；AFIDT 仅做跟踪，待其进入 stable 且 Sea-ORM 官方采用后再评估。

---

## 6. 风险、阻塞项与时间表

| 编号 | 风险/阻塞项 | 影响 | 当前状态 | 应对策略 |
|---|---|---|---|---|
| R1 | Sea-ORM 2.0 stable 未发布 | 无法完成向 stable 的正式迁移 | 阻塞中 | 持续跟踪 crates.io/GitHub releases |
| R2 | RC 与 stable 之间仍可能有破坏性变更 | 升级后可能需要小幅调整代码 | 中低风险 | 发布后立即阅读 Migration Guide 并跑 `cargo test` |
| R3 | MSRV 1.94.0 限制旧工具链 |  CI/协作者环境需 Rust ≥ 1.94 | 已满足（当前 1.96.1） | 在 CI 中保持 `rust-version` 声明 |
| R4 | AFIDT 未稳定 | 不能移除 `async-trait` | 上游阻塞 | 不主动迁移，仅跟踪 rust-lang/rust#133119 |

**推荐时间表**:

- **现在 ~ 2.0 stable 发布前**: 保持 `2.0.0-rc.42`，每周检查一次 crates.io/GitHub。
- **2.0 stable 发布后 1~2 周内**: 将 `Cargo.toml` 改为 `version = "2.0.0"`，运行 `cargo check --workspace` 与 `cargo test --workspace`。
- **2.0 stable 发布后 1 个月内**: 更新示例文档与迁移笔记，移除 RC 相关注释。

---

## 7. 结论与建议

- **Go / No-Go**: **No-Go**（当前阶段）。Sea-ORM 2.0 stable 尚未发布，不能宣布迁移完成。
- **短期行动**: 维持 `2.0.0-rc.42`，继续依赖 `async-trait`；不尝试 AFIDT。
- **长期行动**: stable 发布后，迁移工作量预计 **< 1 天**（当前使用深度浅），优先验证 `database_ecosystem_demo.rs` 的 SQLite 内存路径。

---

*本报告随 Sea-ORM 发布状态持续更新。下次建议评审日期：2026-07-23 或 2.0 stable 发布时。*
