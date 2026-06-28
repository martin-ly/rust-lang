# 第一阶段执行清单：治理与低风险修复

> **阶段**: 第一阶段（1–2 周）
> **目标**: 建立单一主控、清理历史计划、修复最明显不一致、稳定 archive 边界
> **来源**: `.kimi/SUSTAINABLE_IMPROVEMENT_PLAN_2026_06_28_CONFIRMED.md`
> **开始日期**: 2026-06-28

---

## G1 整理 `.kimi/` 目录

- [x] 创建 `.kimi/archive/`（如不存在）
- [x] 将以下历史计划/检查清单文件移入 `.kimi/archive/`，并保留原文件名：
  - `EXECUTION_CHECKLIST_2026_06_22.md`
  - `EXECUTION_CHECKLIST_2026_06_26_CONFIRMED.md`
  - `EXECUTION_PLAN_2026_06_02.md`
  - `EXECUTION_PLAN_CONFIRMED_2026_05_29.md`
  - `EXECUTION_PLAN_CONFIRMED_2026_06_03.md`
  - `PENDING_PLANS_ALIGNMENT_DRAFT_2026_06_25.md`
  - `PROJECT_COMPREHENSIVE_PENDING_PLAN_2026_06_28.md`
  - `PROJECT_PENDING_PLANS_ALIGNMENT_CONFIRM_2026_06_26.md`
  - `RUST_197_RELEASE_DAY_DECISIONS.md`（发布日后归档）
  - `WEEKLY_PROGRESS_2026_06_28.md`（周报过期后归档）
  - 其他以 `_2026_05_` / `_2026_06_22_` / `_2026_06_25_` 结尾的历史状态文件
- [x] 保留以下活跃文件在 `.kimi/` 根目录：
  - `SUSTAINABLE_IMPROVEMENT_PLAN_2026_06_28_CONFIRMED.md`（本改进计划）
  - `PHASE1_GOVERNANCE_2026_06_28.md`（本执行清单）
  - `EXECUTION_RUST_1_97_RELEASE_2026_07_09.md`（发布日清单）
  - `RUST_197_RELEASE_COUNTDOWN_2026_06_28.md`（倒计时排期）
  - `RUST_198_TRACKING_2026_06_28.md`（1.98 跟踪）
  - `BCD_TRACK_STATUS_2026_06_28.md`（BCD 状态总览）
  - `I18N_Q4_2026_PLAN.md`（Q4 i18n 计划）
  - `WEEKLY_PROGRESS_2026_07_05.md`（下周周报）
- [x] 更新 `BCD_TRACK_STATUS_2026_06_28.md` 中的提交记录与链接（若引用被归档文件）
- [x] 提交变更（commit `45dfd14f3`）

---

## G2 制定 Archive 政策并迁移历史内容

- [x] 创建 `ARCHIVE_POLICY.md`（项目根目录），明确：
  - archive 目录的用途：只读历史参考
  - 归档标准：6 个月以上未更新、内容被替代、历史审计/备份
  - 禁止向 archive 写入新内容（除明确的归档动作）
  - 迁移路径：`docs/archive/` → `archive/docs/`；`docs/rust-ownership-decidability/` → `archive/rust-ownership-decidability/`
- [x] 将 `docs/archive/` 下所有内容迁移到 `archive/docs/`
- [x] 将 `docs/rust-ownership-decidability/` 迁移到 `archive/rust-ownership-decidability/`
  - 合并了之前已存在的部分归档副本（`17-unsafe-rust/01-intro.md`、`extensions/rust-for-linux.md`、`extensions/unsafe-rust-patterns.md`）
- [x] 检查并确认相对链接在迁移后仍然有效（绝对路径链接不存在，无需额外修复）
- [x] 在迁移后的 archive 目录顶层添加 `README.md` 说明归档政策
- [x] 提交变更（commit `9d65d11fc`）

---

## G3 修复最明显的代码/文档不一致

- [ ] 为 `crates/c14_semantic_web/` 创建顶层 `README.md`
  - 内容基于 `crates/c14_semantic_web/docs/README.md` 或模板
  - 版本号与 workspace 一致（3.1.0）
- [ ] 重写 `crates/c11_macro_system_proc/src/lib.rs` 顶部文档注释
  - 去除中英混杂、机器翻译痕迹
  - 统一为中文说明，必要时提供英文标题
- [ ] 检查并修复其他 crate 顶层 README 的版本号一致性
- [ ] 提交变更

---

## G4 修复 Clippy/编译警告基线

- [ ] 确认 `cargo clippy --workspace --tests --all-features -- -D warnings` 通过
- [ ] 确认 `cargo test --workspace` 通过
- [ ] 在 CI 工作流中加入 `--tests` 的 clippy 检查
- [ ] 提交变更

---

## G5 制定命名规范

- [x] 创建 `NAMING_CONVENTION.md`（项目根目录），规定：
  - Markdown 文件名：`number_prefix_snake_case.md` 或 `snake_case.md`
  - 脚本文件名：`snake_case.py` / `snake_case.sh` / `snake_case.rs`
  - 禁止中文、空格、混合大小写（过渡期例外清单需明确列出）
  - 目录名：`snake_case` 或 `number_prefix_snake_case`
- [x] 创建 `scripts/lint_filenames.py`，检查新增文件是否符合规范
- [ ] 将命名检查加入 pre-commit / CI（先作为 warning，待历史文件清理后再改为失败）
- [x] 提交变更（commit `9dd4836`）

---

## 验收标准

第一阶段完成时，仓库应满足：

1. `.kimi/` 根目录下仅有当前周期活跃清单，历史文件已归档
2. `docs/archive/` 和 `docs/rust-ownership-decidability/` 已迁移到 `archive/`
3. `crates/c14_semantic_web/` 有顶层 README，`c11_macro_system_proc` 文档注释已清理
4. `cargo clippy --workspace --tests --all-features -- -D warnings` 通过
5. `NAMING_CONVENTION.md` 和 `ARCHIVE_POLICY.md` 已创建

---

*本清单随执行进度更新，完成后进入第二阶段。*
