# Rust 知识体系文档重构 —— Phase 2 后续计划

> **Phase 1 成果**: 28篇核心文档按 10 模块标准重构完成，从 ~8,000 行扩展至 ~16,000+ 行。
> **核心层状态**: 01_fundamentals → 02_intermediate → 03_advanced → 04_expert 主要薄弱点已全部清除。
> **日期**: 2026-05-09

---

## 📊 Phase 1 完成清单

| 层级 | 已完成文档 | 状态 |
|------|-----------|------|
| 01_fundamentals | lifetimes.md | ✅ 重构完成 |
| 02_intermediate | traits, generics, error_handling, collections, smart_pointers, strings, cargo_basics + 5篇新特性文档 | ✅ 重构完成 |
| 03_advanced | async_await, async_closure, threads, atomics, synchronization, ffi, declarative, procedural, lazy_initialization, type_driven_correctness | ✅ 重构完成 |
| 04_expert | tree_borrows, compiler_internals, unsafe_audit, coq_formalization_guide | ✅ 重构/增强完成 |
| 跨轨关联 | 9篇核心文档 ↔ safety_critical 双向链接 | ✅ 已建立 |

---

## 🔧 Phase 2 候选任务清单

### 任务组 A: Ecosystem 层补完（7篇文档）

| 文档 | 当前行数 | 目标 | 优先级 | 预估工作量 |
|------|---------|------|--------|-----------|
| `06_ecosystem/emerging/rust_1_95_preview.md` | 117 | 350+ | 中 | 2h |
| `06_ecosystem/edition_2024.md` | 217 | 450+ | 高 | 3h |
| `06_ecosystem/emerging/generic_const_exprs.md` | 317 | 500+ | 高 | 3h |
| `06_ecosystem/emerging/async_closures.md` | 337 | 500+ | 中 | 2h |
| `06_ecosystem/databases/sqlx_deep_dive.md` | 355 | 550+ | 中 | 3h |
| `06_ecosystem/deep_dives/tokio_deep_dive.md` | 359 | 550+ | 高 | 3h |
| `06_ecosystem/databases/sea_orm_deep_dive.md` | 378 | 550+ | 中 | 3h |
| **小计** | **2,080** | **3,450+** | — | **~19h** |

### 任务组 B: Reference 层 + 索引更新（4篇文档 + 索引）

| 文档 | 当前行数 | 目标 | 优先级 | 预估工作量 |
|------|---------|------|--------|-----------|
| `05_reference/keywords.md` | 477 | 600+ | 中 | 2h |
| `knowledge/INDEX.md` | 177 | 400+ | **最高** | 3h |
| `knowledge/README.md` | 47 | 200+ | **最高** | 2h |
| 各层 `README.md` (3篇) | 16-44 | 各100+ | 高 | 2h |
| **小计** | **~800** | **1,500+** | — | **~9h** |

### 任务组 C: 质量保障与深度关联（全局任务）

| 任务 | 说明 | 优先级 | 预估工作量 |
|------|------|--------|-----------|
| 链接有效性检查 | 扫描全部 .md 的相对链接，修复 404 | 高 | 2h |
| Mermaid 图语法验证 | 确保所有 Mermaid 图可渲染 | 中 | 1h |
| 文档头格式统一 | 统一标题、元数据、版本标注格式 | 中 | 2h |
| safety_critical 延伸阅读关联 | 在核心文档"延伸阅读"中添加 safety_critical 链接 | 中 | 2h |
| 跨层链接网络补全 | 所有重构文档的"启下"模块完整性检查 | 高 | 2h |
| **小计** | — | — | **~9h** |

---

## 📋 推荐方案选项

### 选项 1: "全面收官"方案（推荐）

**执行顺序**: C → B → A（质量优先，再索引，最后 ecosystem）

**具体内容**:
1. **第 1-2 轮**: 完成任务组 C（质量保障），确保 28 篇重构文档零缺陷
2. **第 3-4 轮**: 完成任务组 B（索引 + reference），建立全局导航体系
3. **第 5-8 轮**: 分 2-3 批完成任务组 A（ecosystem），按优先级 `edition_2024` → `tokio_deep_dive` → `generic_const_exprs` → 其他

**预期产出**:
- 28 篇核心文档质量验证通过
- 全局索引/导航体系更新
- 7 篇 ecosystem 文档达到 500+ 行标准
- **总新增行数**: ~4,000+ 行
- **总预估时间**: ~35-40h

---

### 选项 2: "聚焦索引"方案（平衡效率）

**执行顺序**: C + B 同步进行，A 暂缓

**具体内容**:
1. **第 1-2 轮**: 任务组 C（质量保障）+ 任务组 B 的 INDEX/README 更新
2. **第 3 轮**: 仅重构 3 篇最高优先级 ecosystem 文档：`edition_2024`、`tokio_deep_dive`、`generic_const_exprs`

**预期产出**:
- 全局导航体系可用
- 3 篇关键 ecosystem 文档补强
- 质量基线建立
- **总新增行数**: ~2,000+ 行
- **总预估时间**: ~18-20h

---

### 选项 3: "最小可行"方案（保守推进）

**执行顺序**: 仅 C + B 的 INDEX

**具体内容**:
1. **第 1 轮**: 任务组 C 的核心子集（链接检查 + 跨层链接补全）
2. **第 2 轮**: 更新 `knowledge/INDEX.md` 和 `README.md`

**预期产出**:
- 文档链接网络可用
- 全局入口索引更新
- **总新增行数**: ~500+ 行
- **总预估时间**: ~8-10h

---

## 🎯 战略建议

| 维度 | 推荐选择 |
|------|---------|
| **如果目标是全面重构** | 选项 1（全面收官） |
| **如果目标是快速建立可用体系** | 选项 2（聚焦索引） |
| **如果资源有限，先保底** | 选项 3（最小可行） |
| **我的推荐** | **选项 1**，原因：Phase 1 已投入大量精力，Phase 2 完成剩余文档可以形成完整的知识闭环，避免"烂尾" |

---

## ✅ 确认清单

请确认以下内容：

1. **选择方案**: [ ] 选项 1（全面收官） / [ ] 选项 2（聚焦索引） / [ ] 选项 3（最小可行） / [ ] 自定义
2. **Ecosystem 文档优先级**: 是否有特定文档需要优先处理？
3. **质量保障深度**: 是否需要运行自动化链接检查脚本，还是手动检查即可？
4. **时间预期**: 是否可以接受分 5-8 轮持续推进（每轮 2-4 小时工作量）？

---

**计划版本**: 1.0
**制定日期**: 2026-05-09
**制定者**: Kimi Code CLI
