# Sea-ORM 2.0 Stable 发布跟踪

> **跟踪日期**: 2026-06-22
> **当前 workspace 版本**: `2.0.0-rc.41`
> **目标版本**: `2.0.0` stable
> **状态**: ⏳ 等待上游发布

---

## 检查记录

| 日期 | crates.io 最新版本 | 状态 |
|:---|:---|:---|
| 2026-06-19 | `2.0.0-rc.40` | 等待 stable |
| 2026-06-22 | `2.0.0-rc.41` | 已升级至 rc.41，继续等待 stable |

---

## 当前配置

```toml
# workspace Cargo.toml
sea-orm = { version = "2.0.0-rc.41", features = [
    "sqlx-postgres",
    "runtime-tokio-rustls",
], default-features = false }
```

使用 crate:

- `crates/c06_async`（示例/开发依赖）

---

## 阻塞原因

Sea-ORM 2.0 仍处于 release candidate 阶段，上游尚未发布 `2.0.0` stable。继续跟踪 crates.io 和 [Sea-ORM GitHub Releases](https://github.com/SeaQL/sea-orm/releases)。

> **注意**: 网络上部分第三方文章声称 Sea-ORM 2.0 已于 2026-01 发布，但 crates.io 索引与 `cargo search sea-orm` 截至 2026-06-22 仍返回 `2.0.0-rc.41`。本项目以 crates.io 官方索引为最终依据，暂不升级。

---

## 升级计划

一旦 `2.0.0` stable 发布：

1. 更新 `Cargo.toml` 中 `sea-orm` 版本为 `"2.0.0"`。
2. 运行 `cargo update -p sea-orm` 刷新 `Cargo.lock`。
3. 运行 `cargo check --workspace` 验证 API 兼容性。
4. 运行 `cargo test -p c06_async` 验证示例。
5. 更新 `CHANGELOG.md` 和本跟踪报告。

---

## 参考

- [Sea-ORM on crates.io](https://crates.io/crates/sea-orm)
- [Sea-ORM GitHub Releases](https://github.com/SeaQL/sea-orm/releases)
