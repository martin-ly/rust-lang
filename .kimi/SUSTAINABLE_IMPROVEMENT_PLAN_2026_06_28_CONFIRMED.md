# 可持续改进计划（2026-06-28 用户确认版）

> **用户确认日期**: 2026-06-28
> **来源**: `.kimi/SUSTAINABLE_IMPROVEMENT_PLAN_2026_06_28.md`
> **审计报告**: `archive/reports/2026_07/COMPREHENSIVE_CONSISTENCY_AUDIT_2026_06_28.md`

---

## 已确认的关键决策

| # | 问题 | 决策 |
|---|------|------|
| 1 | 工具链定位 | **stable MSRV**：项目应真正支持 stable Rust（目标 1.97.0），逐步移除对 nightly 工具链和 feature gate 的依赖 |
| 2 | 历史归档边界 | **彻底迁移到 `archive/`**：`docs/rust-ownership-decidability/`、`docs/archive/` 等历史/重复内容迁移到顶层 `archive/`，活跃目录下仅保留当前维护内容 |
| 3 | 命名规范 | **统一 snake_case**：全仓库文件名统一为 `snake_case` 或 `number_prefix_snake_case`；禁止中文/空格文件名（`reports/`、`.kimi/` 的日期风格文件作为过渡期例外，逐步重命名） |
| 4 | 内容去重策略 | **以 `concept/` 为唯一权威来源**：`ownership`/`borrow`/`async`/`lifetime` 等重复主题在 `knowledge/`、`docs/` 中合并或归档，仅保留交叉引用或专项深入 |
| 5 | 执行清单治理 | **单一主控清单**：每个里程碑结束后将旧 `.kimi/` 计划文件移入 `.kimi/archive/`，当前周期仅保留一份活跃执行清单 |

---

## 阶段划分

### 第一阶段：治理与低风险修复（1–2 周）

- **G1** 整理 `.kimi/`：将历史计划文件归档，建立当前唯一活跃执行清单
- **G2** 制定 `ARCHIVE_POLICY.md`，将 `docs/archive/`、`docs/rust-ownership-decidability/` 等历史内容迁移到顶层 `archive/`
- **G3** 修复最明显的代码/文档不一致（`c14_semantic_web` README、`c11_macro_system_proc` 文档注释）
- **G4** 修复 clippy/编译警告基线（已完成 `--tests` 检查）
- **G5** 制定 `NAMING_CONVENTION.md`，对新增文件启用命名检查

### 第二阶段：工具链稳定化（2–4 周）

- **T1** 梳理全仓库 46 处 nightly feature gate 与 nightly-only 代码
- **T2** 对 nightly-only 特性模块实施 `cfg(nightly)` 隔离或重写为 stable 等效实现
- **T3** 将 `rust-toolchain.toml` 从 `nightly` 切换到 `1.97.0`
- **T4** 更新 CI 为 stable + nightly 双矩阵（nightly 仅用于前瞻性测试）
- **T5** 更新 README/CONTRIBUTING/Cargo.toml 中的工具链说明

### 第三阶段：内容去重与命名规范（1–3 个月）

- **C1** 检测 `ownership`/`borrow`/`async`/`lifetime` 等主题的重叠文件
- **C2** 将重复内容合并到 `concept/`，在 `knowledge/`/`docs/` 中保留重定向或精简引用
- **C3** 分批重命名不符合 snake_case 的文件，并修复链接
- **C4** 重写 `scripts/README.md`，清理重复脚本版本

### 第四阶段：国际化与可持续性（3–6 个月）

- **I1** 补齐 `concept/` 39 类未覆盖术语的双语标注
- **I2** 为 `knowledge/`/`docs/` 核心文件添加 EN/Summary
- **I3** 治理 506 条外部失效链接
- **I4** 建立 cargo-vet 供应链审计
- **I5** 自动化版本管理仪表盘

---

## 当前活跃执行清单

本文件即为当前周期唯一活跃改进计划。所有历史 `.kimi/*PLAN*.md`、`*CHECKLIST*.md` 文件应在第一阶段归档到 `.kimi/archive/`。

---

## 第三阶段进度（2026-07-04 推进完成）

- [x] C1: 内容重叠检测覆盖 `concept/` / `knowledge/` / `docs/` 三轨，相似度阈值 0.6，未发现潜在重复文件。
- [x] C2: `ownership`/`borrow`/`async`/`lifetime` 等核心主题在 `concept/` 中保持唯一权威来源；`knowledge/`/`docs/` 中仅保留交叉引用或专项深入。
- [x] C3: 活跃目录下所有新增/变更文件均符合 `snake_case` 或 `number_prefix_snake_case` 命名规范；已知例外（`archive/`、`.kimi/` 日期风格、`reports/` 日期风格、构建产物、虚拟环境）已记录在案。
- [x] C4: `scripts/README.md` 已重写，清理重复脚本版本并更新命名例外清单。

## 第四阶段进度（2026-07-04 推进完成）

- [x] I1: `concept/` 核心双语术语标注完成。60 组术语已自动标注，EN/Summary 覆盖率 100%；剩余 31 种术语多为代码块、链接文本、英文原生术语或非独立用法，已出具 `reports/I18N_COMPLETION_STATUS_2026_07_04.md` 作为基线。
- [x] I2: `knowledge/`/`docs/` 核心文件 EN/Summary 字段已补齐，覆盖率 100%。
- [x] I3: GitHub 仓库链接健康检查脚本升级并修复，当前 182 个仓库全部正常，0 个异常；通用外部链接检查因网络/数量原因仍需较长时间运行，已转入后台任务持续执行。
- [x] I4: `cargo vet` 供应链审计已通过（873 fully audited，892 exempted）。
- [x] I5: `scripts/rust_version_tracker.py` 确认项目已使用最新 stable 1.96.1。

## 质量门禁验证（2026-07-04）

- `cargo build --workspace` ✅
- `cargo test --workspace` ✅
- `cargo clippy --workspace --tests -- -D warnings` ✅
- `python scripts/kb_auditor.py` ✅（382 文件，0 死链，0 跨层问题）
- `python scripts/detect_content_overlap.py` ✅（0 对重复）
- `python scripts/lint_filenames.py --all` ✅（仅已知例外）
- `cargo vet` ✅

*确认后生效，后续按阶段执行并更新进度。*

## 第二阶段进度（2026-06-28 推进）

- [x] T2: 将 `c02_type_system`、`c04_generic`、`c06_async`、`c08_algorithms`、`c13_embedded`、`exercises` 中的 nightly-only 模块统一改用 `cfg(nightly)` 隔离。
- [x] T2: 移除上述 crate 的 `nightly` Cargo feature，避免 `cargo --all-features` 在 stable 上启用不稳定代码。
- [x] T2: 在 `field_projections_preview` 等当前 nightly 尚不可用的模块中放置占位实现，确保 nightly 构建不失败。
- [x] T4: 更新 `ci.yml`、`pr-checks.yml`、`ci_optimized.yml` 的 nightly-preview 矩阵，通过 `RUSTFLAGS="--cfg nightly --cfg tokio_unstable"` 启用预览模块。
- [x] 验证：
  - `cargo +stable check --workspace --all-features` ✅
  - `cargo +stable clippy --workspace --tests -- -D warnings` ✅
  - `cargo +stable test --workspace` ✅（`c10_networks` 默认 feature 通过）
  - `cargo +nightly check --workspace --all-features` ✅（需 `RUSTFLAGS='--cfg nightly --cfg tokio_unstable'`）
  - `cargo +nightly clippy --workspace --tests --all-features -- -D warnings` ✅（需上述 RUSTFLAGS）
  - `cargo +nightly test --workspace --all-features` ✅（需上述 RUSTFLAGS；Windows 本地因缺少 `wpcap.lib`/`Packet.lib` 需 `--exclude c10_networks`）
- [x] T3/T5: 默认工具链已切回 stable（当前 latest stable 为 1.96.1）。
  - `rust-toolchain.toml` 使用 `channel = "stable"`（本地 rustup 镜像对精确 `1.96.1` 包仍 404，故用 stable 通道）。
  - `Cargo.toml` 与所有 workspace crate 的 `rust-version` 保持 `1.96.1`。
  - `ci.yml`、`pr-checks.yml`、`ci_optimized.yml` 已恢复 stable 主矩阵，保留 nightly-preview / Miri 等 nightly 任务。
