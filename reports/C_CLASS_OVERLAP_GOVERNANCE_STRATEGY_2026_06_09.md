# C 类目录内容重复治理策略

> **日期**: 2026-06-09
> **审计基线**: A类 0 问题 / B类 1 问题 / C类 883 问题

## 1. 重复检测概况

### 扫描结果

| 指标 | 数值 |
|:---|:---|
| 扫描文件数 | 1,334 |
| 相似度阈值 | 0.6 |
| 潜在重复对 | 146 |
| 相似度 1.0 | 12 对 |
| 相似度 0.8-0.99 | 24 对 |
| 相似度 0.6-0.79 | 110 对 |

### 重复分布

```
concept/  ←───── 主轨（教学文档）
    ↑
    │    知识分层设计（预期内）
    ↓
knowledge/  ←── 辅轨（知识卡片）
    ↑
    │    内容溢出（需治理）
    ↓
docs/research_notes/  ←── C类（研究笔记）
    ↑
    │    历史积累（需归档）
    ↓
docs/rust-ownership-decidability/  ←── C类（形式化工程）
```
## 2. 重复类型分类

### 2.1 预期内重复（无需处理）

**类型**: concept/ ↔ knowledge/ 的知识分层

| 文件对 | 相似度 | 说明 |
|:---|:---|:---|
| `concept/03_advanced/13_inline_assembly.md` ↔ `knowledge/03_advanced/unsafe/02_inline_asm.md` | 1.00 | 同一主题，不同深度 |
| `concept/07_future/rust_1_97_preview.md` ↔ `knowledge/06_ecosystem/emerging/06_rust_1_97_preview.md` | 1.00 | 同一主题，不同深度 |
| `concept/03_advanced/03_unsafe.md` ↔ `knowledge/03_advanced/unsafe/04_unsafe_rust.md` | 0.75 | L3 教学 ↔ 知识卡片 |

**策略**: ✅ 保留。这是**有意设计的知识分层**：

- `concept/`：教学叙事，含示例、解释、练习
- `knowledge/`：精炼卡片，快速查阅

### 2.2 内容溢出（需迁移或引用）

**类型**: concept/ ↔ docs/research_notes/ 或 docs/rust-ownership-decidability/

| 文件对 | 相似度 | 建议 |
|:---|:---|:---|
| `concept/03_advanced/03_unsafe.md` ↔ `docs/05_guides/05_unsafe_rust_guide.md` | 1.00 | `docs/05_guides/` 应引用 `concept/`，避免重复维护 |
| `concept/07_future/19_rust_for_linux.md` ↔ `docs/03_guides/03_rust_for_linux_guide.md` | 0.90 | 合并或明确分工 |
| `knowledge/04_expert/academic/01_coq_formalization_guide.md` ↔ `docs/content/academic/10_coq_formalization_guide.md` | 1.00 | 内容完全相同，应统一 |

**策略**:

1. `docs/05_guides/` 和 `docs/03_guides/` 中的内容应以 `concept/` 为主轨
2. 重复内容添加 `[主轨引用]` 标记，指向 `concept/` 中的权威版本
3. 逐步将 unique 内容迁移到 `concept/`，删除重复副本

### 2.3 历史积累（需归档评估）

**类型**: docs/rust-ownership-decidability/ 内部重复

| 文件对 | 相似度 | 说明 |
|:---|:---|:---|
| `concept/05_comparative/02_cpp_abi_object_model.md` ↔ `docs/rust-ownership-decidability/comparative-analysis/rust-vs-cpp.md` | 0.75 | 两个不同的对比视角 |
| `concept/05_comparative/06_rust_vs_java.md` ↔ `docs/rust-ownership-decidability/comparative-analysis/rust-vs-java.md` | 0.75 | 同上 |

**策略**:

1. `rust-ownership-decidability/comparative-analysis/` 中的对比文件更偏向形式化视角
2. `concept/05_comparative/` 中的文件更偏向教学视角
3. 评估后决定是否：a) 保留双轨 b) 合并 c) 归档 C 类版本

## 3. 治理优先级

### P0（立即处理）

- [ ] `docs/content/academic/10_coq_formalization_guide.md` ↔ `knowledge/04_expert/academic/01_coq_formalization_guide.md`（内容完全相同）
- [ ] `docs/05_guides/05_unsafe_rust_guide.md` 添加主轨引用标记

### P1（本月内）

- [ ] 评估 `concept/05_comparative/` ↔ `rust-ownership-decidability/comparative-analysis/` 的重复对
- [ ] 为 `docs/03_guides/` 和 `docs/05_guides/` 中的重复内容添加 `[主轨引用]`
- [ ] 更新 `docs/content/` 中的映射文档，明确三轨分工

### P2（长期）

- [ ] 建立"内容唯一性"检查流程：新文档创建时检查是否已存在于主轨
- [ ] 定期（季度）运行重复检测脚本
- [ ] 将 C 类目录中的 unique 内容评估后迁移或归档

## 4. 工具与流程

### 检测脚本

```bash
# 运行三轨重复检测
python scripts/detect_content_overlap.py

# 参数
# --threshold 0.75  # 调整相似度阈值
# --output reports/overlap_report.md
```
### 新文档检查清单

创建新文档前，检查：

- [ ] 是否已存在同名/同主题文档于 `concept/`？
- [ ] 是否已存在同名/同主题文档于 `knowledge/`？
- [ ] 如果是 C 类目录，是否明确标注与主轨的关系？

## 5. 附录：完全重复清单（相似度 = 1.0）

| # | 文件1 | 文件2 | 建议 |
|:---|:---|:---|:---|
| 1 | `concept/03_advanced/13_inline_assembly.md` | `knowledge/03_advanced/unsafe/02_inline_asm.md` | 保留双轨（分层设计） |
| 2 | `concept/07_future/rust_1_97_preview.md` | `knowledge/06_ecosystem/emerging/06_rust_1_97_preview.md` | 保留双轨（分层设计） |
| 3 | `concept/03_advanced/03_unsafe.md` | `docs/05_guides/05_unsafe_rust_guide.md` | **迁移/引用** |
| 4 | `concept/03_advanced/03_unsafe.md` | `docs/research_notes/formal_methods/10_unsafe_concept_mindmap.md` | 保留（不同视角） |
| 5 | `concept/03_advanced/03_unsafe.md` | `docs/research_notes/formal_methods/10_unsafe_safety_proof_tree.md` | 保留（不同视角） |
| 6 | `concept/03_advanced/03_unsafe.md` | `docs/rust-ownership-decidability/17-unsafe-rust/01-intro.md` | **评估后归档** |
| 7 | `concept/03_advanced/03_unsafe.md` | `docs/rust-ownership-decidability/extensions/unsafe-rust-patterns.md` | **评估后归档** |
| 8 | `concept/07_future/19_rust_for_linux.md` | `docs/rust-ownership-decidability/extensions/rust-for-linux.md` | **评估后归档** |
| 9 | `knowledge/04_expert/academic/01_coq_formalization_guide.md` | `docs/content/academic/10_coq_formalization_guide.md` | **统一/删除副本** |

---

> **维护者**: Rust 学习项目团队
> **下次复审**: 2026-07-09
