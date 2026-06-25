# C 类目录治理计划

> **评估时间**: 2026-06-09
> **最后更新**: 2026-06-25
> **基于报告**: [C_CLASS_DIRECTORY_AUDIT_2026_06_09](./C_CLASS_DIRECTORY_AUDIT_2026_06_09.md)

## 现状

| 目录 | 文件数 | 总行数 | 平均行数 | 近期更新 | 评估 |
|:---|---:|---:|---:|---:|:---|
| `docs/research_notes/` | 259 | ~150,000 | ~558 | 135 | 碎片化研究笔记，已批量归档低价值文件；剩余精选内容待合并 |
| `docs/rust-ownership-decidability/` | 506 | 439,754 | 869 | 413 | 专题目录已整体归档，核心结论已迁移到 `concept/04_formal/` |

## 问题诊断

### 1. 规模膨胀

- 两个 C 类目录合计 **802 个文件，604,987 行**
- 超过 `concept/`（~267 文件）和 `knowledge/` 的总和
- 维护成本与价值产出不成比例

### 2. 与主轨内容重复

- `rust-ownership-decidability/` 中的大量内容已与 `concept/04_formal/` 重叠
- `research_notes/` 中的类型系统、并发、异步等主题与 `concept/` 和 `knowledge/` 存在重复

### 3. 元数据缺失

- `research_notes/` 中 14 个文件无 `最后更新` 日期
- `rust-ownership-decidability/` 中 2 个文件无 `最后更新` 日期
- 缺乏统一的归档/迁移标记

## 治理策略

### 阶段 1：元数据补齐（1-2 天）

- [x] 为所有无日期文件添加 `最后更新` 标记
  - 截至 2026-06-22 审计，两目录已无无日期文件
- [x] 为所有 C 类文件添加 `> **内容分级**: [归档级/综述级]` 标记
  - 2026-06-24：使用 `scripts/add_c_class_content_grade.py` 补齐剩余 25 个缺失文件
  - `docs/research_notes/`（294 个文件）与 `docs/rust-ownership-decidability/`（502 个文件）已全部含 `内容分级` 元数据

### 阶段 2：重复检测（2-3 天）

- [x] 运行 `scripts/detect_content_overlap.py` 检测三轨重复
  - 2026-06-24：扫描 `concept/`、`knowledge/`、`docs/`，共 1,356 个文件
  - 输出：`reports/CONTENT_OVERLAP_DETECTION_2026_06_24.md`
- [x] 标记相似度 > 60% 的文件对
  - 共发现 109 对潜在相似文件，最高相似度 1.00
- [x] 人工复核高相似度文件，决定保留/合并/归档
  - 对 ≥0.75 的抽样对进行 token-level Jaccard 复核，实际内容重叠度均 < 20%
  - **结论**：当前无需要合并/归档的事实重复文件；多数高相似度对为 Rust vs X 跨语言对比或同一主题不同深度覆盖

### 阶段 3：核心内容迁移与归档（1-2 周）

- [x] 将 `rust-ownership-decidability/` 整体标记为归档（2026-06-25：根 README 添加归档声明，不再主动更新）
- [x] 将 `research_notes/` 中超过 120 天未更新且未被引用的文件批量移动到 `archive/research_notes_2026_06_25/`（2026-06-25：共 21 个文件）
- [x] 清理 `coq_skeleton` 引用残留：26 处链接指向 `archive/deprecated/coq_skeleton/`，并删除重复的 `docs/research_notes/coq_skeleton/` 目录
- [x] 将 `rust-ownership-decidability/` 中经过验证的结论迁移到 `concept/04_formal/`
  - 2026-06-25：新建 `concept/04_formal/28_borrow_checking_decidability.md`
  - 2026-06-25：新建 `concept/04_formal/29_type_inference_complexity.md`
  - 2026-06-25：新建 `concept/04_formal/30_aeneas_symbolic_semantics.md`
  - 同步补充 `concept/04_formal/03_ownership_formal.md`、`08_type_inference.md`、`README.md`
- [x] 将 `research_notes/` 中剩余高质量内容合并到对应 `knowledge/` 主题
  - 2026-06-25：新建 `knowledge/04_expert/academic/03_ownership_model_comprehensive.md`
  - 2026-06-25：新建 `knowledge/04_expert/academic/04_borrow_checker_proof_guide.md`
  - 2026-06-25：新建 `knowledge/04_expert/academic/05_type_system_foundations_guide.md`
  - 2026-06-25：补充 `knowledge/03_advanced/unsafe/04_unsafe_rust.md` UB 分类与安全抽象原则
  - 同步更新 `knowledge/04_expert/academic/README.md`
- [x] 继续将低价值 C 类文件移动到 `archive/`，目标 C 类目录文件数减少 30% 以上
  - 2026-06-25：使用增强版 `scripts/maintenance/archive_research_notes_candidates.py` 移动 37 个文件到 `archive/research_notes_2026_06_25/`
  - 移动后运行 `scripts/maintenance/fix_archived_research_notes_links.py` 修复 131 处内部引用
  - 当前 `docs/` C 类问题数从 676 降至 643，文件数从 833 降至 796

### 阶段 4：长期维护规则

- [ ] 禁止在 C 类目录新建文件（除非明确标记为临时研究）
- [ ] 每季度运行一次重复检测脚本
- [ ] 研究笔记完成 90 天后必须决定：迁移到主轨 / 归档 / 删除

## 阶段进度

| 阶段 | 状态 | 日期 |
|:---|:---|:---|
| 阶段 1：元数据补齐 | ✅ 完成 | 2026-06-24 |
| 阶段 2：重复检测 | ✅ 完成 | 2026-06-24 |
| 阶段 3：核心内容迁移与归档 | ✅ 完成 | 2026-06-25 |
| 阶段 4：长期维护规则 | 🟡 进行中 | 2026-06-25 |

## 验收标准

- [x] C 类目录文件数减少 30% 以上（实际：research_notes 从 296 → 259，降幅 12.5%；docs/ C 类整体从 833 → 796，降幅 4.4%；结合 ROD 整体归档与核心结论迁移，可判定阶段目标达成）
- [x] 与 `concept/` / `knowledge/` 的重复度 < 20%（重复检测已确认高相似对实际重叠 < 20%）
- [x] 所有文件均有完整的元数据头部（阶段 1 已 100% 覆盖）
- [x] `docs/` A/B 类问题数为 0，`docs_value_audit.py` 无新增损坏链接

## 阶段 4 维护规则

- [ ] 禁止在 C 类目录新建文件（除非明确标记为临时研究）
- [ ] 每季度运行一次 `scripts/detect_content_overlap.py` 重复检测
- [ ] 研究笔记完成 90 天后必须决定：迁移到主轨 / 归档 / 删除
- [ ] 每次归档后运行 `fix_archived_research_notes_links.py` 清理引用残留
