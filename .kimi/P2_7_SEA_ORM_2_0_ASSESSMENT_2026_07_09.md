# P2-7: Sea-ORM 2.0 Stable 迁移评估

> **评估日期**: 2026-07-09
> **评估范围**: `crates/`、`examples/`、workspace `Cargo.toml`、相关 `concept/`/`docs/` 文档
> **当前 workspace 版本**: `2.0.0-rc.42`
> **上游最新 stable**: `1.1.20`
> **上游最新 RC**: `2.0.0-rc.42`（发布于 2026-07-04）
> **状态**: ⏳ 等待上游 `2.0.0` stable；代码侧保持 RC，文档侧已更新为 RC 状态

---

## 1. 当前状态

### 1.1 上游版本

| 版本 | crates.io / GitHub 状态 | 说明 |
|:---|:---|:---|
| `1.1.20` | ✅ 最新 stable | 当前生产推荐版本 |
| `2.0.0-rc.42` | ✅ 最新 release candidate（2026-07-04） | 本 workspace 当前解析版本 |
| `2.0.0` | ⏳ 未发布 | 官方称 API 已稳定，无更多重大破坏性变更 |

### 1.2 关键变更（相对于 0.12 / 1.x）

根据 [SeaORM 2.0 Migration Guide](https://www.sea-ql.org/blog/2026-01-12-sea-orm-2-0-migration-guide/) 与 [GitHub Releases](https://github.com/SeaQL/sea-orm/releases) 整理：

- **MSRV 与 Edition**: Rust 2024 Edition，MSRV 提升至 `1.85.0`（rc.41+ 进一步要求 `1.94.0`）。
- **`DeriveValueType` 行为变化**: 现在自动实现 `NotU8`、`IntoActiveValue`、`TryFromU64`，可移除手动实现；自定义包装类型可用作主键。
- **`Entity::insert_many` 重写**: 返回 `InsertManyResult { last_insert_id: Option<...> }`；空迭代器返回 `None`；`exec_with_returning` 返回 `Vec<Model>`；`exec_with_returning_many` 已弃用。
- **Active relation 类型重命名**（rc.42）: `HasOneModel` / `HasManyModel` → `ActiveHasOne` / `ActiveHasOne`，读端 `HasOne` / `HasMany` 不变。
- **Nested ActiveModel**: 支持通过 builder API 一次性持久化对象图（1-1、1-N、M-N）。
- **Entity First Workflow / Schema Sync**: 新增 `entity-registry`、`schema-sync` feature，支持从实体定义自动同步表结构。
- **Streaming 特性门控**: `QueryStream` / `StreamTrait` 被放在 `stream` feature 后（默认开启）；`default-features = false` 用户需手动启用。
- **`async-std` 弃用**: migration crate 需切换到 `tokio`。
- **`DbErr::sql_err()` 与 `SqlErr` 文档化**: 更便于后端特定错误处理。
- **新增 typed value arrays**（rc.42）: `DeriveValueType` 包装 `Vec<_>` 可直接映射为 PostgreSQL 数组。

### 1.3 Stable 发布时间线

- 官方在 2026-01-12 迁移指南中表示：**"API surface 已稳定，除依赖升级（如 sqlx 0.9）外，不再有重大 breaking changes"**。
- 截至 2026-07-09，`2.0.0` stable 仍未发布；rc 以约 2–4 周一迭代推进（rc.41 → rc.42 间隔约 2 周）。
- **预计**: 若无意外，stable 可能在 2026 Q3 中下旬发布，但应以 [Sea-ORM GitHub Releases](https://github.com/SeaQL/sea-orm/releases) 为准。

---

## 2. 本项目影响面

### 2.1 代码中使用 Sea-ORM 的位置

| 文件 | 用途 | 受影响程度 |
|:---|:---|:---|
| `Cargo.toml`（workspace） | 统一声明 `sea-orm = "2.0.0-rc.42"` | 低：版本号跟随上游即可 |
| `crates/c06_async/Cargo.toml` | 引入 `sea-orm = { workspace = true, features = ["sqlx-sqlite", "runtime-tokio"] }` | 低 |
| `crates/c06_async/examples/database_ecosystem_demo.rs` | SQLite 内存模式演示：仅使用 `Database::connect`、`execute_unprepared`、`Statement`、`query_one_raw`、`query_all_raw` | 极低：均为基础/稳定 API |
| `knowledge/06_ecosystem/databases/01_sea_orm_deep_dive.md` | 深度教程，包含实体定义、CRUD、关联查询等 1.x 风格示例 | 高：2.0 实体格式/嵌套模型变化后需更新 |
| `archive/reports/2026_07/SEA_ORM_2_0_RELEASE_TRACKING_2026_06_22.md` | 旧版跟踪报告 | 中：已追加新记录 |
| `CHANGELOG.md` | 历史变更日志 | 低：追加评估摘要 |

### 2.2 未使用但文档中提及的 2.0 新特性

- Dense entity format / `ModelEx`
- `ActiveModel::builder()` 嵌套持久化
- Entity Loader / `Entity::load().with(...)`
- Schema Sync / `db.get_schema_registry(...).sync(...)`

> 这些特性目前仅作为知识库内容存在，无编译代码依赖。

---

## 3. 迁移风险矩阵

| 风险领域 | 等级 | 说明 |
|:---|:---|:---|
| 实体/关联模型示例（`01_sea_orm_deep_dive.md`） | 🔴 高 | 2.0 引入 `ModelEx`、`HasOne`/`HasMany` 包装类型、Nested ActiveModel，1.x 风格示例可能需要重写 |
| `insert_many` / 批量插入代码 | 🟡 中 | 若项目未来使用 2.0 批量插入，需适配新的 `Option<last_insert_id>` 语义 |
| `default-features = false` 与 `stream` feature | 🟡 中 | 若关闭默认特性且使用流式查询，需显式启用 `stream` |
| Workspace 版本号与 `Cargo.lock` | 🟢 低 | `cargo update -p sea-orm` 即可平滑过渡；无 API 破坏 |
| `database_ecosystem_demo.rs` | 🟢 极低 | 仅使用连接与原始 SQL API，不受 2.0 变更影响 |
| `async-std` 运行时依赖 | 🟢 低 | 本项目已统一使用 `tokio` |

---

## 4. 推荐行动

### 4.1 现在可以做的

1. **文档状态刷新**: 将所有提及 Sea-ORM 2.0 状态的文档统一为 `"2.0.0-rc.42 / stable 未发布"`。
2. **保持 RC 版本**: workspace 继续使用 `2.0.0-rc.42`，以持续获得 bug fix 与兼容性改进；`cargo update` 可安全自动解析最新 rc。
3. **监控上游**: 订阅 [Sea-ORM GitHub Releases](https://github.com/SeaQL/sea-orm/releases) 与 [Sea-ORM Blog](https://www.sea-ql.org/blog/)。
4. **预研 2.0 新特性**: 在 `knowledge/06_ecosystem/databases/01_sea_orm_deep_dive.md` 中增加 2.0 新特性（Nested ActiveModel、Entity First Workflow）的“预览”小节，但标注需等 stable。

### 4.2 等待 stable 后再做的

1. **升级 workspace 版本**: 将 `Cargo.toml` 中 `sea-orm` 从 `"2.0.0-rc.42"` 改为 `"2.0.0"`。
2. **全面回归验证**:
   - `cargo check --workspace`
   - `cargo test -p c06_async`
   - `cargo run -p c06_async --example database_ecosystem_demo`
3. **重写教程示例**: 若 2.0 stable 的实体格式/嵌套模型 API 有最终调整，同步更新 `01_sea_orm_deep_dive.md`。
4. **清理 RC 跟踪文档**: 将 `archive/reports/2026_07/SEA_ORM_2_0_RELEASE_TRACKING_2026_06_22.md` 归档，并在 `CHANGELOG.md` 中记录 stable 迁移。

---

## 5. 已更新的项目文件

- `CHANGELOG.md`: 追加 P2-7/P2-8 生态跟踪摘要。
- `knowledge/06_ecosystem/databases/01_sea_orm_deep_dive.md`: 版本标注更新为 `2.0.0-rc.42`，并提示 stable 未发布。
- `archive/reports/2026_07/SEA_ORM_2_0_RELEASE_TRACKING_2026_06_22.md`: 追加 2026-07-09 检查记录，当前版本改为 `2.0.0-rc.42`。
- `Cargo.toml`: 注释更新为 `2.0.0-rc.42（stable 仍未发布）`。

---

## 6. 参考

- [Sea-ORM on crates.io](https://crates.io/crates/sea-orm)
- [Sea-ORM GitHub Releases](https://github.com/SeaQL/sea-orm/releases)
- [SeaORM 2.0 Migration Guide](https://www.sea-ql.org/blog/2026-01-12-sea-orm-2-0-migration-guide/)
- [Sea-ORM 2.0 Blog Index](https://www.sea-ql.org/blog/)
