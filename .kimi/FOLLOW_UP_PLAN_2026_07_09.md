# 后续计划与任务确认单（2026-07-09）

> **前提**: `crates/*/docs/` AGENTS.md §6.4 合规整治已完成（568/568 文件含 canonical header）。
> **状态**: 待用户确认

---

## 阶段 A：收尾与提交（建议立即执行）

| 编号 | 任务 | 操作内容 | 验收标准 | 预估耗时 |
|---|---|---|---|---|
| A1 | 提交当前 565 个变更文件 | `git add` + `git commit`（可分 2~3 个逻辑 commit：crates/docs 整治、concept 扩展、工具链/验证配置） | 工作区干净；提交信息清晰 | 20 min |
| A2 | 清理 tmp/ 过渡脚本 | 删除本次生成的 `tmp/stub_*.py`、`tmp/add_*.py`、`tmp/migrate_*.py` | `tmp/` 中无本次整治遗留脚本 | 5 min |
| A3 | 归档已完成计划文件 | 将 `.kimi/RECTIFICATION_PLAN_2026_07_09.md` 及早期已完成计划移入 `.kimi/archive/` | 当前周期仅保留一份活跃执行清单 | 5 min |
| A4 | 运行 `cargo vet prune` | 清理历史无效 exemptions 与 imports | `cargo vet` 仍通过；警告减少或消失 | 10 min |
| A5 | 全量验证回归 | 跑通所有质量门禁 | 与本次整治完成时结果一致 | 15 min |

---

## 阶段 B：本周内可完成的剩余技术债

| 编号 | 任务 | 操作内容 | 验收标准 | 优先级 |
|---|---|---|---|---|
| B1 | 清理 `concept/SUMMARY.md` 中 36 个 archive 链接 | 将 archive 文件改为不链接或移入 `archive/` 索引 | SUMMARY.md 中无 archive 路径 | 高 |
| B2 | 处理 2 对预存 Rust 1.97 重复 | 方案二选一：① 将 `docs/09_toolchain/10_rust_1_97_features.md` 改为纯摘要+链接；② 保留 canonical + quick-reference 组合并文档化 | `detect_content_overlap.py` 不再报告或标记为允许 | 中 |
| B3 | 抽查新建 `concept/` 页 EN/Summary | 对本次 subagent 新建的 ~20 个 concept 页做抽样检查 | 抽查文件均含 **EN** 与 **Summary** | 中 |
| B4 | 更新 `AGENTS.md` 如有规则变化 | 若本次整治引入新的目录约定或豁免规则，同步更新根目录 `AGENTS.md` | AGENTS.md 与当前实践一致 | 低 |

---

## 阶段 C：Q4 2026 重点（已创建预备文档）

| 编号 | 任务 | 来源 | 目标产出 | 建议时间 |
|---|---|---|---|---|
| C1 | i18n 工具决策落地 | `.kimi/Q4_2026_i18n_tool_decision.md` | 选定并配置自动化 EN/Summary 检查/补全工具 | 7 月下旬 |
| C2 | 外部失效链接修复 | `.kimi/Q4_2026_external_link_fix_plan.md` | 修复 506 条外部链接；建立定期监控 | 8 月 |
| C3 | Brown inventory i18n 补全 | `.kimi/Q4_2026_brown_inventory_i18n_status.md` | Brown Book 引用段落全部双语化 | 8 月 |
| C4 | 启动 P2-Q3 滚动深化剩余项 | `.kimi/P2_Q3_2026_EXECUTION_PLAN.md` | 按 P2-1 ~ P2-11 优先级继续推进 | Q3 持续 |

---

## 阶段 D：可持续治理机制

| 编号 | 任务 | 频率 | 负责人/工具 |
|---|---|---|---|
| D1 | 内容重叠检测 | 每次 PR / 每周 | `scripts/detect_content_overlap.py` |
| D2 | 死链检查 | 每次大规模合并后 | `scripts/kb_auditor.py --link-check` |
| D3 | 供应链审计清理 | 每月 | `cargo vet prune` |
| D4 | `crates/*/docs/` 新增审查 | 每次新增文件 | Code Review / CI |

---

## 待确认问题

1. **是否现在执行阶段 A（提交 + 清理）？** 建议：是，避免 565 个文件长期悬而未决。
2. **阶段 B1/B2 是否一并处理？** 建议：是，可在 1 个会话内完成。
3. **阶段 C 中优先启动哪一项？** 候选：C1（i18n 工具）或 C2（外部链接修复）。
4. **是否需要我立即开始执行 A1~A5？**

---

*确认后，我将按阶段顺序推进并持续汇报进度。*
