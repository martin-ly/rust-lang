# KG 消费层 v2 → v3 迁移报告

**日期**: 2026-07-12
**范围**: 将全部知识图谱消费工具从 `concept/00_meta/kg_data_v2.json`（已退化为 21 实体 / 10 关系的 stub）切换到 `concept/00_meta/kg_data_v3.json`（474 实体 / 5799 关系，2026-07-11 生成），并退役 v2 与过期的 `concept_index.json`。

---

## 1. v2 / v3 Schema 差异

| 维度 | v2（已退役） | v3（现行） |
| --- | --- | --- |
| 顶层键 | `@context, metadata, classes, properties, entities, relations, decision_trees, fault_trees` | 相同 |
| `entities` 结构 | **按类别分组的 dict**：`{concepts: [...], theories: [...], properties: [...], rules: [...]}` | **扁平 list**：474 个实体直接成数组 |
| 实体 `@type` | Concept / Theory / Model / Property / Rule / Primitive | Concept / Theory / Model / Primitive（实际使用 4 类） |
| 英文摘要字段 | `skos:definition`（中英双语） | **`skos:scopeNote`**（仅 en，474/474）；`skos:definition` 已不存在 |
| 层级字段 | `ex:layer`（L0–L7）、`ex:bloom`、`ex:asp` | **`ex:bloomLevel`**（419/474）、`ex:rustVersion`、`ex:path`（指向 concept/ 相对路径）、`ex:theoremIds` |
| 中文标签 | `skos:prefLabel` zh 有值 | zh 标签存在但**部分为空字符串**（需回退 en） |
| 关系字段 | `ex:subject/predicate/object, ex:source, ex:confidence, ex:version, ex:reviewed, dcterms:created, prov:wasDerivedFrom` | 相同子集（无 `prov:wasDerivedFrom`） |
| 谓词 | dependsOn / entails / mutexWith / refines / equivalentTo / counterExample / instanceOf / appliesTo | 新增 **`ex:relatedTo`**（4446 条）；实际使用 relatedTo / dependsOn / entails |
| 规模 | 21 实体 / 10 关系（stub） | 474 实体 / 5799 关系 |

适配策略：所有消费方的实体迭代统一改为「v3 扁平 list 优先，v2 分组 dict 兼容」；摘要读取统一为 `skos:definition` → `skos:scopeNote` 回退；标签读取增加「zh 为空回退 en」逻辑。

---

## 2. 改动清单

### 2.1 消费层切到 v3（代码）

| 文件 | 改动 |
| --- | --- |
| `tools/kg_rag/kg_rag.py` | `KG_PATH` → v3；`iter_entities` 兼容 v3 扁平 list；新增 `entity_summary()`（definition→scopeNote 回退）并用于 embedding 文本与结果输出；索引缓存增加 `kg_path` 校验，避免复用 v2 旧缓存；docstring/`--kg` help 更新 |
| `tools/kg_rag/README.md` | 数据来源描述 v2 → v3 |
| `scripts/kg_reasoning.py` | 默认 `--kg` → v3；`label_of` 兼容 v3 list 布局 + zh 空值回退 en；docstring 更新 |
| `scripts/owl_consistency_check.py` | `KG_PATH` → v3；`iter_entities` 兼容 v3；报告输出改为 `reports/OWL_CONSISTENCY_CHECK_2026_07_12.md`（保留 06-27 历史报告） |
| `scripts/multilingual_alignment.py` | `KG_PATH` → v3；`iter_entities` 兼容 v3；报告输出改为 `reports/MULTILINGUAL_ALIGNMENT_DRIFT_2026_07_12.md` |
| `scripts/generate_en_skeleton.py` | `KG_PATH` → v3；`label_for` 兼容 v3 list 布局 + 空值跳过 |
| `crates/c14_semantic_web/src/io.rs` | `load_kg_from_json` 支持 v3 扁平数组与 v2 分组字典两种布局 |
| `crates/c14_semantic_web/src/graph.rs` | `Entity` 新增 `scope_note`（skos:scopeNote）、`path`（ex:path）可选字段；新增 `summary_for()`；`label_for` 增加 zh 空值回退 en |
| `crates/c14_semantic_web/src/validation.rs` | `VALID_RELATIONS` 增加 v3 新谓词 `ex:relatedTo` |
| `crates/c14_semantic_web/src/lib.rs` | crate 文档 v2 → v3 |
| `crates/c14_semantic_web/examples/kg_query.rs`、`kg_validate.rs` | 默认路径 → v3 |
| `crates/c14_semantic_web/tests/integration_tests.rs` | `Entity` 构造补齐新字段 |
| `tools/kg_browser/build.py` | 仅注释修正（KG_PATH 此前已是 v3，行为不变） |
| `concept/00_meta/knowledge_topology/kg_tlo_alignment.md` | 3 处 `kg_data_v2.json` 引用 → v3（示例实体 ex:Ownership 等在 v3 中存在） |

### 2.2 退役与死代码处理

| 文件 | 处理 |
| --- | --- |
| `concept/00_meta/kg_data_v2.json` | 移入 `archive/2026/kg_data_v2_retired_2026-07-12.json`（已核实内容：21 实体 / 10 关系 stub，version 2.0） |
| `concept/00_meta/concept_index.json` | 无生成脚本、无代码消费者（仅 4 处文档提及）。移入 `archive/2026/concept_index_retired_2026-05-21.json`；4 处文档（`semantic_space.md`、`audit_checklist.md`、`concept_index.md`、`inter_layer_map.md`）更新为「已退役，以 kg_data_v3.json 为唯一真相源」 |
| `scripts/build_search_index.py` | 加 `.. deprecated:: 2026-07-12` 头注（无 CI/消费者；注：其输入 `concept_kb.json` 实际存在于仓库根目录且为 2026-07-11 新生成，与任务背景描述略有出入，故采用头注而非移动）；`scripts/README.md`、`README.md` 同步标注退役 |
| `tools/doc_search/README.md` | 重写：明确标注「未实现（placeholder），搜索能力由 mdbook 内置 searchindex 与 tools/kg_rag 提供」，删除虚构的 `cargo run` 用法 |

### 2.3 未迁移但保留的引用（记录原因）

- `scripts/migrate_kg_v1_to_v2.py`：v1→v2 的**历史生产脚本**（消费者不消费 v2，而是生成 v2），保留用于溯源；如需重新生成 v2 可运行它，输出已指向被退役路径，属预期。
- `reports/OWL_CONSISTENCY_CHECK_2026_06_27.md`、`reports/KG_V3_COMPLETION_2026_07_11.md`、`reports/CONTENT_COMPLETENESS_AUDIT_2026_07_09.md` 等历史报告中的 v2 引用：历史快照，不改写。
- `archive/` 内历史文件：只读归档，不改写。

---

## 3. 验证结果

| 验证项 | 命令 | 结果 |
| --- | --- | --- |
| kg_rag 真实检索 | `tools/kg_rag/.venv/Scripts/python tools/kg_rag/query.py --query "ownership" --top-k 5` | ✅ 自动检测到缓存 kg_path 不匹配并重建 v3 索引（474 实体）；返回 BrownUniversityOwnershipInventory / RustBelt / Ownership 等多实体，附 scopeNote 摘要与 v3 KG 路径（dependsOn/relatedTo/entails） |
| kg_reasoning 前置推理 | `python scripts/kg_reasoning.py --prerequisites ex:Lifetimes` | ✅ 输出 `Borrowing / Ownership / Type System`（zh 空标签正确回退 en） |
| OWL 一致性检查 | `python scripts/owl_consistency_check.py` | ✅ 正常运行并生成 `reports/OWL_CONSISTENCY_CHECK_2026_07_12.md`；exit=1 因 v3 数据存在真实 `dependsOn` 环 `TypeSystem → Ownership → TypeSystem`（见 §4） |
| SHACL 形态检查 | `python scripts/check_kg_shapes.py` | ✅ exit=0（v2 移出后复跑仍通过） |
| c14 校验示例 | `cargo run -p c14_semantic_web --example kg_validate` | ✅ 加载 474 实体 / 5799 关系，验证通过（仅剩「Concept 缺少 ex:layer」信息级警告——v3 已用 ex:bloomLevel 替代 ex:layer） |
| c14 推理示例 | `cargo run -p c14_semantic_web --example kg_query` | ✅ 输出真实学习路径；同样检测到 Ownership↔TypeSystem 环 |
| c14 单元/集成/文档测试 | `cargo test -p c14_semantic_web` | ✅ 全部通过（3 + 1 + doctests） |
| c14 clippy | `cargo clippy -p c14_semantic_web` | ✅ 无警告 |
| kg_browser | `python -m py_compile tools/kg_browser/build.py` | ✅ KG_PATH 为 v3，行为不受影响 |
| Python 语法 | `python -m py_compile`（全部改动脚本） | ✅ |
| 全仓 v2 残留 | grep `kg_data_v2`（scripts/tools/crates/concept/docs/.github） | ✅ 仅剩 `migrate_kg_v1_to_v2.py`（历史生产脚本，已记录） |

---

## 4. v3 数据质量发现（超出迁移范围，仅记录）

1. **dependsOn 环**：`ex:TypeSystem → ex:Ownership → ex:TypeSystem`（OWL 检查与 c14 推理一致检出）。这是 v3 数据本身的语义问题，建议后续治理（OWL 检查 exit=1 即源于此）。
2. **zh 标签空字符串**：部分实体（如 ex:Ownership、ex:Lifetimes）的 zh prefLabel 为空串；`check_kg_shapes.py` 的 K3 仅检查语言标记存在性，未检查非空，建议加强。
3. **ex:layer 缺失**：v3 以 `ex:bloomLevel` 替代 v2 的 `ex:layer`，c14 校验器的 layer 警告为预期信息级提示。

---

## 5. 退役文件清单

| 原路径 | 归档路径 |
| --- | --- |
| `concept/00_meta/kg_data_v2.json` | `archive/2026/kg_data_v2_retired_2026-07-12.json` |
| `concept/00_meta/concept_index.json` | `archive/2026/concept_index_retired_2026-05-21.json` |

新生成报告：`reports/OWL_CONSISTENCY_CHECK_2026_07_12.md`、`reports/KG_SHAPES_VALIDATION_2026-07-12.{md,json}`。

## 6. 环境备注

迁移过程中观察到工作区被并发进程改动（首轮对 kg_rag.py 等文件的编辑曾被还原为 HEAD 状态，`concept_index.json` 被恢复后重新移除）。所有改动已重新应用并通过验证；建议合并前复核 `git status` 确认本报告 §2 清单中的文件改动仍在。
