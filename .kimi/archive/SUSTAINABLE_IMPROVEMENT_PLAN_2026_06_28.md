# 可持续改进计划（2026-06-28）

> **来源**: `reports/COMPREHENSIVE_CONSISTENCY_AUDIT_2026_06_28.md`
> **目标**: 解决项目一致性、可维护性、可发现性、可持续性、国际化、版本管理六大维度的结构性问题
> **性质**: 中长期规划，需与用户确认后分阶段执行

---

## 一、需要用户确认的关键问题

在启动以下任务前，请确认以下 5 个关键决策：

1. **工具链定位**：本项目应明确为“nightly-only 教学/预览仓库”，还是应真正支持 stable MSRV（1.96.0/1.97.0）？
   - *影响*: `rust-toolchain.toml`、`.cargo/config.toml`、CI、feature gate、README/CONTRIBUTING 需要同步修改。

2. **历史归档边界**：`docs/rust-ownership-decidability/`、`docs/archive/` 等历史/重复内容应彻底迁移到 `archive/`，还是保留在 `docs/` 下仅作“历史参考”？
   - *影响*: 大量内部链接、学习路径引用、目录结构将随之调整。

3. **命名规范**：是否统一全仓库文件名为 `snake_case` 或 `number_prefix_snake_case`，并禁止中文/空格文件名（`reports/`、`.kimi/` 的大写下划线日期风格是否保留为例外）？
   - *影响*: 批量重命名会破坏现有链接，需要一次性链接修复。

4. **内容去重策略**：对于 `ownership`/`borrow`/`async`/`lifetime` 等跨目录重复主题，是否以 `concept/` 为唯一权威来源，将 `knowledge/`、`docs/` 中的重复文件合并或归档？
   - *影响*: 可能删除或迁移用户已熟悉的路径，需要确认保留清单。

5. **执行清单治理**：是否同意在每个里程碑结束后将旧 `.kimi/` 计划文件移入 `.kimi/archive/`，仅保留当前周期唯一活跃清单？
   - *影响*: 需要重新整理目前 30+ 个 `.kimi/` 文件，并明确“主控清单”命名规则。

---

## 二、短期任务（1–2 周）

| # | 目标 | 交付物 | 负责人 | 验收标准 | 依赖 |
|---|------|--------|--------|----------|------|
| S1 | 统一治理“单一主控” | 在 `.kimi/` 内指定唯一活跃执行清单，其余计划移入 `.kimi/archive/`；更新 `README.md`/`CONTRIBUTING.md` 指向该清单 | 维护者 | 仓库中仅存在 1 份“当前周期执行清单”；所有历史计划明确标注“历史参考” | 问题 5 |
| S2 | 修正版本/工具链声明 | 要么切换到 stable 并移除 nightly feature gate，要么明确声明为 nightly-only 教学仓库 | 维护者 | README/Cargo.toml/`rust-toolchain.toml`/CI/`.cargo/config.toml` 口径一致 | 问题 1 |
| S3 | 冻结 archive 边界 | 制定 `ARCHIVE_POLICY.md`；将最近仍在编辑的 archive 内容迁回活跃区或明确标记；禁止 CI/脚本向 archive 写入新文件 | 维护者 | 未来 30 天内 archive 无新增/修改文件（除非明确归档动作） | 问题 2 |
| S4 | 修复最明显的代码/文档不一致 | 为 `crates/c14_semantic_web/` 添加顶层 `README.md`；重写 `crates/c11_macro_system_proc/src/lib.rs` 文档注释；更新 boilerplate 模板中的版本号来源 | 维护者 | `c14` 顶层 README 存在且版本号与 workspace 一致；`c11_macro_system_proc` 文档无机器翻译残留 | 无 |
| S5 | 修复 clippy/编译警告基线 | 在全仓库启用 `--tests` 的 clippy 检查；修复剩余警告 | 自动化脚本 + 维护者 | `cargo clippy --workspace --tests --all-features -- -D warnings` 通过 | 无 |

---

## 三、中期任务（1–3 个月）

| # | 目标 | 交付物 | 负责人 | 验收标准 | 依赖 |
|---|------|--------|--------|----------|------|
| M1 | 内容去重与主题归属 | 基于重叠检测脚本输出，合并/归档 `ownership`/`borrow`/`async`/`lifetime` 等重复主题；建立 `concept/` 为唯一权威入口 | 内容维护者 | 同名文件减少 ≥50%；每个核心主题在活跃目录中仅保留 1 个主文档 + N 个交叉引用 | 问题 4 |
| M2 | 统一命名规范并自动化检查 | 制定 `NAMING_CONVENTION.md`；编写 `scripts/lint_filenames.py`；分批重命名旧文件 | 自动化脚本 + 维护者 | 新增文件 100% 通过命名检查；旧文件违规数下降 ≥60% | 问题 3 |
| M3 | 脚本仓库清理 | 合并/归档重复修复脚本；重写 `scripts/README.md` 覆盖全部活跃脚本；将一次性脚本归入 `scripts/archive/2026/one_off/` | 维护者 | `scripts/README.md` 中每个活跃脚本都有条目；根目录 `fix_*` 脚本数量减少 ≥50% | 无 |
| M4 | 补齐 i18n 缺口 | 针对 39 类未覆盖术语强制标注；为 `knowledge/01_fundamentals/`–`03_advanced/` 添加 EN/Summary | 自动化脚本 + 审校者 | `add_bilingual_annotations.py --mode check-only` 未覆盖术语 ≤10 种；`knowledge/` 核心文件 EN/Summary 覆盖率 ≥50% | 无 |
| M5 | 建立真实的集成测试 | 扩展 `crates/integration_tests/`，覆盖关键 crate 的跨模块调用场景 | Rust 开发者 | `crates/integration_tests/` 测试数 ≥20 个，每个测试真正调用 ≥2 个 workspace crate 的 API | 无 |
| M6 | 外部链接治理 | 修复/更新 506 条失效/异常外部链接；建立外部链接月度检查机制 | 自动化脚本 + 维护者 | 外部链接失效数降至 ≤50 条；每月生成外部链接健康报告 | 无 |
| M7 | 供应链审计落地 | 为 `supply-chain/audits.toml` 建立 cargo-vet 审计记录；review `.cargo/audit.toml` 的 ignore 项 | 安全/维护者 | `supply-chain/audits.toml` 非空；每条 ignore 均有理由和过期时间 | 无 |

---

## 四、长期任务（3–6 个月）

| # | 目标 | 交付物 | 负责人 | 验收标准 | 依赖 |
|---|------|--------|--------|----------|------|
| L1 | 版本管理自动化 | 用 CI matrix（stable/beta/nightly）替代手动 `probe_rust_*_apis.rs`；通过 `cfg`/`build.rs` 自动启用/禁用预览 API | 自动化/CI 维护者 | 每 6 周发布日只需修改 1–2 个配置文件；手动探测脚本退役 | S2, M5 |
| L2 | 依赖与安全治理 | 降低 Cargo.lock 依赖数量；为关键依赖建立审计记录；每季度 review ignore 项 | 安全/维护者 | 依赖数减少 ≥20%；无长期被忽略且未跟踪的 RUSTSEC | M7 |
| L3 | 国际化流水线 | 评估 `mdbook-i18n-helpers` 或 gettext/PO 工作流；产出 `README_EN.md` 和 L0/L1 概念文件英文翻译 | i18n 负责人 | 产出技术选型决策文档；英文 README 上线；≥30% 的 `concept/01_foundation/` 有英文对照 | M4 |
| L4 | 学习路径与质量仪表盘自动化 | 让 `kb_quality_dashboard.md` 与 `LEARNING_MVP_PATH.md` 在 CI 中每周重新生成；自动比对文件数量、链接、术语覆盖率 | 自动化脚本 | 仪表盘日期与仓库状态差距 ≤7 天；README 统计数字由脚本自动注入 | M1, M4, M6 |
| L5 | 内容质量评分体系 | 建立文件成熟度模型（stub/boilerplate/draft/reviewed/authoritative）；为每个 `concept/` 文件标注成熟度 | 内容维护者 | 每个活跃概念文件均有成熟度标签；boilerplate 文件比例 ≤10% | S4, M1 |

---

## 五、建议的优先级排序

### P0（阻塞级，必须立即决策）
- **S1 单一主控清单**：否则后续任何计划都无法确定来源。
- **S2 工具链定位**：影响 CI、依赖、学习者预期，是根本性问题。

### P1（高优先级，1 个月内）
- S3 archive 边界冻结
- S4 修复最明显代码/文档不一致
- M1 内容去重与主题归属
- M3 脚本仓库清理

### P2（中优先级，1–3 个月）
- M2 命名规范
- M4 i18n 补齐
- M5 真实集成测试
- M6 外部链接治理
- M7 供应链审计

### P3（长期优化，3–6 个月）
- L1 版本管理自动化
- L2 依赖安全治理
- L3 国际化流水线
- L4 仪表盘自动化
- L5 内容质量评分

---

## 六、验收与跟踪

- 每个任务完成后，更新本计划中的状态列（待补充 `status` 字段）。
- 建议每月生成一份 `reports/IMPROVEMENT_PROGRESS_YYYY_MM_DD.md`，汇总已完成、进行中、阻塞中的任务。
- 与用户确认本计划后，将确认结果写入 `.kimi/SUSTAINABLE_IMPROVEMENT_PLAN_2026_06_28_CONFIRMED.md`，作为后续执行主控。

---

*本计划基于 `reports/COMPREHENSIVE_CONSISTENCY_AUDIT_2026_06_28.md`，待用户确认关键问题后执行。*
