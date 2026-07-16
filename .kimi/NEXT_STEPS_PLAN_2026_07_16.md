# 后续计划与任务编排（2026-07-16）

> **EN**: Next Steps Plan
> **Summary**: 基于当前质量门基线、活跃计划文件与全局 TODO，梳理项目后续未完成计划与任务，供用户确认优先级与范围。
> **状态**: 待用户确认

---

## 1. 执行摘要

当前知识库处于**形式治理高度成熟**的状态：

- **23 个阻断质量门**全部通过（`run_quality_gates.sh` exit 0）。
- **5 个语义观察门**当前基线全部达标：
  - O1 stub 纯度：伪 stub=0 / 空壳页=0 / 高重复=0
  - O2 交叉语义覆盖：16/16 = 100%
  - O3 KG 谓词精度：核心 50 实体 generic_ratio=0%
  - O4 决策树：Top 30 常见错误码覆盖率 30/30 = 100%
  - O5 版本语义注入：74 特性 / 74 映射 = 100%
- **语义健康分**: 99.5 / 100，grade=OK。
- **代码块腐烂**: `--strict` 默认抽样下 rot=0。
- **元数据一致性**: D1–D6 仅 D6=3（Summary 套话），其余为 0。

因此，后续工作已从"补课式修复"转向**可持续维护、深度补全与长期治理**。

---

## 2. 已处置或已不再是问题的项

以下问题在 2026-07-15/16 的报告中曾被提及，但**当前已解决或基线已达标**，不纳入后续主线：

| 原问题 | 当前状态 | 证据 |
|---|---|---|
| `docs/15_rust_formal_engineering_system/` 伪 stub / 8,245 行重复 | ✅ 已清理为真正 stub | 28 个 `.md` 文件共 359 行，均 ≤25 行，含权威来源链接 |
| `content/safety_critical/01_completion_report_100_percent.md` 过度声明 | ✅ 文件已不存在 | 目录 listing 已无此文件 |
| 8 个跨领域权威页缺失 | ✅ 已覆盖 | `check_cross_domain_coverage.py --strict` 16/16=100% |
| 决策树 Top 30 覆盖率不足 | ✅ 已达标 | `check_decision_trees.py --strict` 30/30=100% |
| 版本语义注入缺口 | ✅ 已全覆盖 | `check_version_semantic_injection.py --strict` 74/74=100% |
| KG 核心 50 实体谓词精度 | ✅ 已达标 | `check_kg_relation_precision.py --strict` generic_ratio=0% |
| `knowledge/` L1–L3 核心概念非 stub 文件 | ✅ 已标准化为 AGENTS.md §4.3 重定向 stub | `check_stub_purity.py --strict` 伪 stub=0 |
| `knowledge/INDEX.md` 未直接指向 `concept/` | ✅ 已更新学习路径与字母索引 | `kb_auditor.py` 死链 0 |
| Brown Inventory 练习 i18n | ✅ 文件头与 TODO 已双语化 | `cargo test -p exercises --lib ownership_borrowing::brown_inventories` 通过 |
| naming convention WARN 收尾 | ✅ 已合规化（为无 README 的专题系列目录补索引） | `check_naming_convention.py --strict` ERROR=0 |

> 注：上述问题在 `reports/COMPREHENSIVE_SEMANTIC_AUDIT_CRITIQUE_2026_07_15.md` 中仍有记录，但数据已过时。建议将该报告归档或标注为"已部分过时"。

---

## 3. 后续任务（按优先级编排）

### 3.1 高优先级：立即推进

#### T1. 审阅并提交当前工作区未提交变更

- **内容**: 12 个未提交文件，包括 `AGENTS.md`、`Cargo.toml`/`Cargo.lock`、`concept/00_meta/02_sources/` 下 4 个文件、`concept/00_meta/03_audit/` 下 2 个文件、`concept/00_meta/knowledge_topology/decision_trees.yaml`、`.github/PULL_REQUEST_TEMPLATE.md`、`.kimi/templates/`。
- **风险**: 这些变更携带了最新的 AGENTS.md 规则（23 门阻断 + 5 观察门、转正纪律、PR 模板等），若不提交会导致后续协作口径不一致。
- **动作**:
  1. 人工 review `AGENTS.md` 与 `Cargo.toml` 的变更合理性。
  2. 处理 CRLF→LF 的 warning（7 个 concept/00_meta 文件）。
  3. 运行 `bash scripts/run_quality_gates.sh` 验证提交前全绿。
  4. 提交并 push（需用户确认是否由 agent 执行 `git commit`）。
- **验收**: `git status --short` 为空，CI 全绿。

#### T2. Q4 外部链接批量修复 ✅

- **来源**: `Q4_EXTERNAL_LINK_FIX_PLAN_2026_07_09.md`
- **状态**: 已完成。复跑 `check_non_github_links_health.py`：3270 个去重链接中异常链接=0；
  唯一超时链接 `www.eprosima.com/index.php/products-all/eprosima-fast-dds` 已替换为
  `https://github.com/eProsima/Fast-DDS`。剩余 SSL/403 警告均为环境证书或受保护站点，
  已登记于 `reports/non_github_links_health_report.md`。
- **验收**: `check_non_github_links_health.py` 异常链接=0；`kb_auditor.py` 死链 0。

#### T3. `docs/` 非 stub 文件 canonical 链接补全 ✅

- **来源**: `concept/00_meta/00_framework/todos.md` Wave 3
- **状态**: 已完成。定位并修复 5 个缺 `concept/` 权威来源链接的 docs 文件：
  - `docs/12_research_notes/11_cheatsheets/01_concurrency_cheatsheet.md` → `concept/03_advanced/00_concurrency/01_concurrency.md`
  - `docs/12_research_notes/11_cheatsheets/02_error_handling_cheatsheet.md` → `concept/02_intermediate/03_error_handling/01_error_handling.md`
  - `docs/12_research_notes/11_cheatsheets/03_lifetime_cheatsheet.md` → `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md`
  - `docs/12_research_notes/11_cheatsheets/04_macros_cheatsheet.md` → `concept/03_advanced/03_proc_macros/01_macros.md`
  - `docs/12_research_notes/10_tutorials_and_guides/06_faq_comprehensive.md` → `concept/` 根索引
- **验收**: `kb_auditor.py` 死链 0；`check_concept_authority_coverage.py --strict --include-crates` 保持通过。

---

### 3.2 中优先级：本周至 7 月下旬

#### T4. i18n 未覆盖术语清零 ✅

- **来源**: `concept/00_meta/00_framework/todos.md`
- **状态**: 已完成。`concept/` 443 个文件已自动标注，4 个误标已手工修正，
  未覆盖术语降至 3 种（出现在 `knowledge/` README 索引中，不阻断）。
- **验收**: `python scripts/add_bilingual_annotations.py --mode check-only` exit 0。

#### T5. `knowledge/` 高优先级大型非 stub 文件迁移 ✅

- **来源**: `concept/00_meta/00_framework/todos.md` Wave 3
- **状态**: L1–L3 核心概念文件已完成标准化。`knowledge/01_fundamentals/` 与
  `knowledge/02_intermediate/` 中 10 个核心概念页已改写为 AGENTS.md §4.3 重定向 stub。
  其余 82 个大型文件按用户指示暂不处理。
- **验收**: `check_stub_purity.py --strict` 伪 stub=0；`detect_content_overlap.py` 无新增可处理项。

#### T6. Brown Inventory 练习 i18n 补全 ✅

- **来源**: `Q4_BROWN_INVENTORY_I18N_STATUS_2026_07_09.md`
- **状态**: 已完成。8 个练习文件、`README.md`、`mod.rs` 已补齐标准头，TODO 已双语化，
  Related Concepts 链接已指向 `concept/` 权威页。
- **验收**: 文件头符合 `knowledge/` stub 模板；`cargo test -p exercises --lib ownership_borrowing::brown_inventories` 通过。

#### T7. `knowledge/INDEX.md` 导航效率优化 ✅

- **来源**: `COMPREHENSIVE_SEMANTIC_AUDIT_CRITIQUE_2026_07_15.md` T7
- **状态**: 已完成。索引顶部已增加导航入口声明；字母索引、学习路径、Rust 1.95/1.96
  特性索引中 L1–L3 核心概念链接已直接指向 `concept/` 权威页。
- **验收**: `kb_auditor.py` 死链 0。

#### T8. 命名规范 WARN 收尾 ✅

- **现状**: `check_naming_convention.py --strict` ERROR=0，WARN=64。其中 52 条为已备案的无序号专题系列，11 条为 content/docs/knowledge 未编号子目录，1 条为 `docs/` 顶层缺 `10_` 空号。
- **状态**: 已按用户指示保持文件名顺序不变。为 `knowledge/02_intermediate/control_flow/`
  与 `knowledge/02_intermediate/macros/` 补 README.md 索引，使其符合 AGENTS.md §4.0-4
  专题系列要求；其余 WARN 均为已批准系列/目录，维持备案。
- **验收**: ERROR=0。

---

### 3.3 低优先级 / 长期：8 月至 Q4

#### T9. Q4 i18n 工具试点

- **来源**: `Q4_I18N_TOOL_DECISION_2026_07_09.md`
- **决策**: 保持 EN/Summary 模式，不强制全面迁移；2026 Q4 在 `concept/00_meta` 或 `concept/01_foundation/00_start` 试点 `mdbook-i18n-helpers` / gettext。
- **动作**:
  1. 选择试点目录。
  2. 评估工具链集成成本（与 `mdbook build`、23 个质量门的兼容性）。
  3. 输出试点报告，决定是否推广。
- **验收**: 试点目录可 `mdbook build` 成功；质量门无新增失败。

#### T10. Sea-ORM 2.0 稳定迁移跟踪

- **来源**: `P2_7_SEA_ORM_2_0_ASSESSMENT_2026_07_09.md`
- **状态**: 上游 Sea-ORM 2.0.0 stable 尚未发布，当前只能跟踪。
- **动作**:
  1. 持续监控上游 release。
  2. stable 发布后：升级 workspace `Cargo.toml`、回归测试、重写 `crates/*/docs/` 中 Sea-ORM 教程示例。
- **验收**: workspace `cargo test --workspace` 通过；教程示例与 2.0 API 一致。

#### T11. AFIDT / dynosaur 跟踪

- **来源**: `P2_8_AFIDT_DYNOSAUR_STATUS_2026_07_09.md`
- **状态**: 跟踪 `rust-lang/rust#133119`（async fn in dyn trait）。
- **动作**:
  1. 每月检查 issue 进展。
  2. 文档侧更新状态页；代码侧保留 `async_trait` 直至稳定方案可用。
- **验收**: 跟踪页日期与状态一致。

#### T12. Rust 1.98 稳定日准备（2026-08-20）✅ 骨架就绪

- **来源**: `reports/VERSION_SEMANTIC_INJECTION_BASELINE_2026_07_15.md`、`check_authority_freshness.py`
- **状态**: 骨架已就绪。`rust_1_98_stabilized.md` 与 `rust_1_98_preview.md` 已存在并维护；
  2026-07-16 复核确认 `check_version_semantic_injection.py --strict` 未映射特性=0；
  待 2026-08-20 稳定后按官方发布笔记实测填充正文。
- **动作（待稳定日执行）**:
  1. 1.98 稳定后填充 `concept/07_future/00_version_tracking/rust_1_98_stabilized.md`。
  2. 将 1.98 语义变更反向注入对应 `concept/` 权威页。
  3. 评估是否更新根 `Cargo.toml` rust-version 至 1.98.0。
- **验收**: `check_version_semantic_injection.py --strict` 覆盖 1.98 新增特性；`check_authority_freshness.py` 无滞后 WARN。

#### T13. 长效机制固化 ✅ 机制已就位

- **来源**: `SEMANTIC_DEEP_AUDIT_AND_SUSTAINABLE_PLAN_2026_07_15.md`
- **状态**: 机制已就位并写入 AGENTS.md。截至 2026-07-16：
  - AGENTS.md §6 已写入 5 条语义密度红线（stub 纯度、KG 谓词、交叉语义域、版本语义注入、决策树 error code 映射）。
  - AGENTS.md §7 已建立月度审计节奏（stub 纯度、交叉语义覆盖、版本注入、KG 谓词、决策树）。
  - `.github/PULL_REQUEST_TEMPLATE.md` 与 `.kimi/templates/monthly_semantic_review.md` 已创建。
  - 23 阻断门 + 5 观察门基线已全绿；观察门 O1–O5 当前均达标，后续按 AGENTS.md §5.2
    "连续 4 周/10 次 CI 稳定" 纪律转正，禁止一次性指示绕过。
- **持续动作**:
  1. 观察门转正：O1–O5 达标后按 §5.2 转正。
  2. 月度语义复核：使用 `.kimi/templates/monthly_semantic_review.md`。
  3. 权威链接新鲜度巡检：`check_authority_freshness.py` 每周手动运行。
  4. KG 全局 `relatedTo` 精化：长期目标将全局 `ex:relatedTo` 占比从 77% 降至 50% 以下。
- **验收**: 机制文档化；观察门基线连续稳定。

---

## 4. 待用户确认的问题

请确认以下事项，以便我按确认结果执行：

### 4.1 范围确认

| # | 问题 | 默认选项 |
|---|---|---|
| Q1 | 是否立即执行 **T1**（提交当前 12 个未提交文件）？ | 是 |
| Q2 | 是否将 **T2（外部链接修复）** 作为下一阶段主线？ | 是 |
| Q3 | 是否优先处理 **T3–T5**（docs canonical 链接、i18n 术语、knowledge 迁移）？ | 是 |
| Q4 | **T5（knowledge/ 大型文件迁移）** 是否只聚焦 L1–L3 核心概念相关文件，其余保留待后续？ | 是 |
| Q5 | 是否启动 **T9（i18n 工具试点）** 的预研？ | 否（Q4 再说） |
| Q6 | 是否由 agent 执行 `git commit`/`git push`？ | 否（仅整理变更，提交由用户完成） |

### 4.2 优先级确认

建议推进顺序：

```
T1 提交未提交变更（含 T2–T8 已完成内容）
  → T12 1.98 稳定日正文填充（2026-08-20 后）
    → T9/T10/T11/T13 长期跟踪
```

> 注：T2/T3/T4/T5/T6/T7/T8 已在本轮完成，T12/T13 骨架/机制已就绪；
> 当前所有可立即执行的任务均已完成，剩余为等待上游发布（Sea-ORM 2.0、AFIDT、Rust 1.98）
> 或长期持续跟踪项。

请确认该顺序，或调整优先级。

---

## 5. 风险与注意事项

1. **不要宣称"100% 完成"**: AGENTS.md §6 明确禁止未经验证的"完成"声明。即使 23 门全过，也须说明"按当前基线通过"。
2. **观察门转正纪律**: O1–O5 当前达标不等于可立即转阻断，必须满足"连续 4 周/10 次 CI 达标"。
3. **报告过时风险**: `COMPREHENSIVE_SEMANTIC_AUDIT_CRITIQUE_2026_07_15.md` 已部分过时，引用时需谨慎。
4. **未提交变更风险**: `AGENTS.md` 等规则文件未提交，若其他协作者基于旧规则工作会产生冲突。

---

## 6. 建议的下一步即时动作

当前所有可立即推进的 TODO 任务（T2–T8）均已完成；T12/T13 骨架与机制已就绪。

若用户确认上述范围，建议立即执行：

1. **T1 提交准备**: review 当前 `git diff`（含 AGENTS.md、Cargo.toml/lock、i18n、
   外部链接修复、docs canonical 链接、knowledge/ stub 标准化、INDEX.md 导航优化），
   按 `.kimi/COMMIT_SUGGESTION_2026_07_16.md` 分批提交。
2. **长期跟踪**: 等待 Rust 1.98（2026-08-20）、Sea-ORM 2.0 stable、AFIDT 上游进展，
   按对应计划触发下一轮更新。

---

**最后更新**: 2026-07-16（本轮 T4–T8 已完成）
**依据**: AGENTS.md §2–§7、`concept/00_meta/00_framework/todos.md`、`.kimi/` 活跃计划文件、`reports/` 2026-07-12 后报告、以及 2026-07-16 实跑的质量门脚本输出。
