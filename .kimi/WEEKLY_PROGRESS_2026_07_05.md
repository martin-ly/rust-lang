# 项目周进度报告 — 2026-07-05

> **报告周期**: 2026-07-05 ~ 2026-07-11（Rust 1.97.0 发布周）
> **主控来源**: `.kimi/EXECUTION_CHECKLIST_2026_06_26_CONFIRMED.md`
> **硬截止**: **2026-07-09** Rust 1.97.0 stable 发布日

---

## 上周（2026-06-28 ~ 2026-07-04）关键完成

| 任务 | 状态 | 说明 |
|---|---|---|
| C 轨道：1.97 发布日准备 | ✅ | 探测脚本、探测报告、API 激活指南、发布日决策清单全部就绪 |
| C 轨道：1.97 API 可用性验证 | ✅ | 12 项 API 探测，9 项已可用；`VecDeque::truncate_front` / `retain_back` 仍不可用；修正 `box_vec_non_null` API 名称为 `Box::into_non_null` / `Vec::into_non_null` |
| C 轨道：1.97 特性测验扩展 | ✅ | `exercises/tests/l3_rust_197_alignment.rs` 从 8 个扩展到 13 个 |
| C 轨道：文档与术语表更新 | ✅ | `concept/07_future/rust_1_97_preview.md` 探测快讯、术语表 17 项候选术语分组、`CHANGELOG.md` 条目草稿 |
| D 轨道：倒计时排期推进 | ✅ | 任务已推进至 2026-07-02（距发布日 7 天） |
| B 轨道：P3 结构债务清理收尾 | ✅ | 17 个 crates boilerplate docs 模板化与批量生成（56 个新文件）完成；`CHANGELOG.md` 新增 B3 小节 |
| D 轨道：BCD 状态总览 | ✅ | 生成 `.kimi/BCD_TRACK_STATUS_2026_06_28.md` |
| 全 workspace 回归测试 | ✅ | `cargo test --workspace` 通过 |

---

## 本周（2026-07-05 ~ 2026-07-11）计划

### C. Rust 1.97.0 发布日执行

| 编号 | 任务 | 负责人 | 状态 | 预计完成 |
|---|---|---|---|---|
| C6 | 2026-07-08 发布日前最终预检 | Kimi | ⏳ 2026-07-08 执行 | 2026-07-08 |
| C7 | 执行 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` | Kimi | ⏳ 2026-07-09 执行 | 2026-07-09 |
| C8 | 根据 Release Notes 激活真实 API 调用 | Kimi | ⏳ 2026-07-09 执行 | 2026-07-09 |
| C9 | 迁移/刷新 1.97 稳定特性文档 | Kimi | ⏳ 2026-07-09 执行 | 2026-07-09 |
| C10 | 发布后稳定化收尾 | Kimi | ⏳ 2026-07-10 ~ 11 | 2026-07-11 |

### D. 计划与跟踪

| 编号 | 任务 | 负责人 | 状态 | 预计完成 |
|---|---|---|---|---|
| D3 | 生成本周进度报告（本文件） | Kimi | ✅ 已完成 | 2026-07-05 |
| D4 | 每日检查 releases.rs / 官方博客（07-05 ~ 07-08） | Kimi | ⏳ 待执行 | 2026-07-08 |
| D5 | 发布日后归档倒计时排期与执行清单 | Kimi | ⏳ 2026-07-10 ~ 11 | 2026-07-11 |

### B. P3 结构债务清理

| 编号 | 任务 | 负责人 | 状态 | 预计完成 |
|---|---|---|---|---|
| B8 | 模板化 per-crate boilerplate docs | Kimi | ✅ 已完成 | 2026-06-28 |
| B9 | 批量生成缺失 boilerplate 文档（实际生成 56 个文件） | Kimi | ✅ 已完成 | 2026-06-28 |

---

## 当前阻塞与风险

| 风险 | 影响 | 缓解措施 |
|---|---|---|
| Rust 1.97.0 延迟发布 | 发布日计划顺延 | 密切关注 releases.rs 与 Rust 官方博客 |
| `VecDeque::truncate_front` / `retain_back` 未进入 1.97.0 | 需要保留等效实现 | 已写 fallback，决策清单已明确处理动作 |
| `Box::as_ptr` / `int::format_into` 因 beta cutoff 未进 1.97.0 | 需要保留等效实现 | 发布日按 Release Notes 核对，决策清单已覆盖 |

---

## 关键数字

- 距离 Rust 1.97.0 发布日：**4 天**
- 1.97 API 探测覆盖：**12 项（9 项已可用）**
- `l3_rust_197_alignment.rs` 1.97 特性测验：**13 个**
- 术语表 1.97 候选术语：**17 项**
- crate docs boilerplate 覆盖率：**17/17 crate（7 类文件）**
- 全 workspace 编译/测试状态：**✅ 通过**

---

## 本周交付物（已提前准备）

- `reports/RUST_197_API_PROBE_2026_06_28.md` — API 可用性探测报告
- `.kimi/RUST_197_API_ACTIVATION_GUIDE.md` — 发布日 API 激活指南
- `.kimi/RUST_197_RELEASE_DAY_DECISIONS.md` — 发布日人工决策清单
- `.kimi/RUST_197_RELEASE_PREFLIGHT_2026_07_08.md` — 发布日前一天预检清单
- `.kimi/RUST_197_POST_RELEASE_STABILIZATION_2026_07_10.md` — 发布后稳定化清单
- `docs/06_toolchain/06_21_rust_1_97_features.md` — 稳定特性文档迁移模板

---

## 下周（2026-07-12 ~ 2026-07-18）概要

1. 完成发布后稳定化收尾（归档、CHANGELOG 最终完善、全 workspace 最终回归）。
2. 启动 P4 i18n 链接治理（506 个外部失效链接）或 B8 boilerplate docs 模板化（视优先级）。
3. 准备 Rust 1.98 跟踪计划。

---

*本报告生成于 2026-07-05，基于当前发布日准备状态。*
