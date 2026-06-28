# 项目周进度报告 — 2026-06-28

> **报告周期**: 2026-06-28 ~ 2026-07-04（发布日前一周）
> **主控来源**: `.kimi/EXECUTION_CHECKLIST_2026_06_26_CONFIRMED.md`
> **硬截止**: **2026-07-09** Rust 1.97.0 stable 发布日

---

## 上周（2026-06-21 ~ 2026-06-27）关键完成

| 任务 | 状态 | 说明 |
|---|---|---|
| P2 深度内容冲刺：rustc query system / Cargo resolver v3 / Kani / TRPL-Brown 对齐 | ✅ | 详见 `CHANGELOG.md [3.1.0]` P2 章节 |
| docs/ C-class 治理收尾 | ✅ | C-class 问题数降至目标以下 |
| Rust 1.96 覆盖缺口回填 | ✅ | 文档 + 概念页 + 10 个测验 |

---

## 本周（2026-06-28 ~ 2026-07-04）计划

### B. P3 结构债务清理

| 编号 | 任务 | 负责人 | 状态 | 预计完成 |
|---|---|---|---|---|
| B1 | 清理空 `.gitkeep` 与空/占位 `.rs` 文件 | Kimi | ✅ 已完成 | 2026-06-28 |
| B2 | 更新 `crates/README.md` 补全全部 workspace crate | Kimi | ✅ 已完成 | 2026-06-28 |
| B3 | 实现 `unsafe_rust/` 练习主题 | Kimi | ✅ 已完成 | 2026-06-28 |
| B4 | 复查重复/编号冲突文件 | Kimi | ✅ 已完成 | 2026-06-28 |
| B5 | 补全 `crates/common` examples/tests | Kimi | ✅ 已完成 | 2026-06-28 |
| B6 | 处理 `BorrowSanitizer` 文件重叠 | Kimi | ✅ 已完成 | 2026-06-28 |
| B7 | 模板化 per-crate boilerplate docs | Kimi | ⏸️ 推迟 | 2026-07 中下旬 |

### C. Rust 1.97.0 发布日准备

| 编号 | 任务 | 负责人 | 状态 | 预计完成 |
|---|---|---|---|---|
| C1 | 复核 `rust-toolchain.toml`、1.97 特性代码、preview 文档 | Kimi | ✅ 已完成 | 2026-06-28 |
| C2 | 创建发布日自动检查脚本 | Kimi | ✅ 已完成 | 2026-06-28 |
| C3 | 准备 `VecDeque::truncate_front` / `retain_back` fallback 切换策略 | Kimi | ✅ 已就绪 | 2026-06-28 |
| C4 | 预演 `rust-toolchain.toml` → `1.97.0` 切换 | Kimi | ⏳ 2026-07-08 执行 | 2026-07-08 |
| C5 | 发布日执行 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md` | Kimi | ⏳ 2026-07-09 执行 | 2026-07-09 |

### D. 计划与跟踪

| 编号 | 任务 | 负责人 | 状态 | 预计完成 |
|---|---|---|---|---|
| D1 | 生成本周进度报告（本文件） | Kimi | ✅ 已完成 | 2026-06-28 |
| D2 | 生成下周计划文件 | Kimi | ⏳ 2026-07-05 生成 | 2026-07-05 |

---

## 当前阻塞与风险

| 风险 | 影响 | 缓解措施 |
|---|---|---|
| `VecDeque::retain_back` 可能未进入 1.97.0 | 需要保留等效实现 | 已写 fallback，发布日按 Release Notes 决定 |
| Sea-ORM 2.0 stable 继续延迟 | 生态文档状态需更新 | 已标注 rc.41 跟踪中 |
| 506 个外部失效链接 | 国际化质量 | 排入 2026-07 中下旬分批处理（不在 BCD 范围） |

---

## 关键数字

- 已清理空/占位文件：**56 个**
- 已补全 README：**10 个**
- `concept/SUMMARY.md` 新增链接：**13 个**
- `unsafe_rust/` 练习主题：**7 个练习 + 17 个集成测试**
- `crates/common` 新增示例/测试：**3 个文件**
- 删除冗余 BorrowSanitizer 预览文件：**1 个**
- 全 workspace 编译/测试/Clippy 状态：**✅ 通过**
- 距离 Rust 1.97.0 发布日：**11 天**

---

## 本周已交付提交

- `D(schedule): resolve BorrowSanitizer cluster by removing redundant 32_borrow_sanitizer_preview.md`
  - 删除 `concept/07_future/32_borrow_sanitizer_preview.md`
  - 更新 `concept/SUMMARY.md`
- `C+D: robust 1.97 release-day probe & schedule update`
  - 重写 `scripts/probe_rust_197_apis.rs` 为子进程探测，主程序始终退出 0
  - 更新 `scripts/rust_197_release_day.sh` 调用探测脚本
- `D(schedule): add Rust 1.97 release countdown plan`
  - 新增 `.kimi/RUST_197_RELEASE_COUNTDOWN_2026_06_28.md`
- `C+D: update 1.97 release plan and add preflight checklist`
  - 更新 `.kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`
  - 新增 `.kimi/RUST_197_RELEASE_PREFLIGHT_2026_07_08.md`
- `C: add Rust 1.97 API activation guide for release day`
  - 新增 `.kimi/RUST_197_API_ACTIVATION_GUIDE.md`
- `D: add Rust 1.97 post-release stabilization checklist`
  - 新增 `.kimi/RUST_197_POST_RELEASE_STABILIZATION_2026_07_10.md`
- `B: add crate docs boilerplate audit script and remove duplicate README`
  - 新增 `scripts/audit_crate_docs_boilerplate.py`
  - 删除 `crates/c03_control_fn/docs/README (2).md`
- `B: add missing boilerplate docs for c13_embedded`
  - 新增 `crates/c13_embedded/docs/README.md`
  - 新增 `crates/c13_embedded/docs/ONE_PAGE_SUMMARY.md`
  - 新增 `crates/c13_embedded/docs/00_MASTER_INDEX.md`

---

## 下周（2026-07-05 ~ 2026-07-11）概要

1. 2026-07-08 预演工具链切换。
2. 2026-07-09 执行 1.97 发布日清单。
3. 发布日后 3 天内完成 P2 稳定化（CHANGELOG、归档、回归测试）。
4. 启动 P4 i18n 链接治理（如时间允许）。
