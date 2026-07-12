# 深度 Atlas 扩展（W2-b）执行报告

> 日期：2026-07-13 ｜ 范围：示例反例（04）/ 场景决策树（03）/ 推理判定树（09）/ 层间映射（06）四类 atlas
> 纪律：只重生成不手改——全部改动固化进 `scripts/extract_concept_topology.py` 与 `scripts/generate_knowledge_topology_atlas.py`，模板 `scripts/templates/atlas_pages/` 未改动（已验证 LF 行尾）。

---

## 1. 覆盖数：前 → 后（按概念页覆盖数）

| Atlas | 计划基线（人工策展节） | 重生成前（数据驱动索引） | 重生成后 | 目标 | 判定 |
|---|:---:|:---:|:---:|:---:|:---:|
| 04 示例反例 | 40 | 295 | **330** | ≥120 | ✅ |
| 03 场景决策树 | 39 | 244 | **284** | ≥80 | ✅ |
| 09 推理判定树 | 15 | 326 | **387** | ≥40 | ✅ |
| 06 层间映射 | 仅 L0/L1（33 页） | 全层（1388 跨层边） | **全层（1429 跨层边）** | 全层 | ✅ |

分母：concept 概念页 483 → 493（重抽取时拾取并行工作流新增 10 页：W4/W5 的 async_trait_object_safety、tokio_runtime_internals、07_concurrency_semantics ×3、crdt_type_zoo、causal_ordering_vector_clocks、five_models_definition_matrix、06 层 quiz ×2）。

“重生成前”列是 2026-07-12 晚 W2-a 补节（20 页「⚠️ 反例与陷阱」等）+ 既有宽口径关键词已产生的索引覆盖；本次新增抽取规则在此之上再增：04 +35、03 +40、09 +61、06 相关链接边源 +19。

## 2. 抽取规则 diff（scripts/extract_concept_topology.py）

1. **深层标题抽取（核心改动）**：`extract_sections()` 原仅按 `##`（h2）切分；现对每个 `##` 节正文再扫描 `###`/`####` 子标题并按同一 keyword_map 匹配，子节 body 取到下一个同级或更高级标题为止。实测全库 h3 级反例/陷阱标题 158 个、其中 39 页父 `##` 不含示例类关键词（原抽取漏掉）；`### 核心推理链`（五件套定理表，h3 级）覆盖 100+ 页。h2 级 body 语义不变（related_links 等全文抽取不受影响）。
2. **关键词扩展**：theorem_tree 新增 `反命题`（原仅 `反命题树`）——全库 192 个 h2「反命题与边界分析」类节自此可识别（+7 页推理信号，其余页本已由深层 `### 核心推理链` 覆盖）。

来源节真实性：索引行「主题提示」列即概念页中命中的真实节名（页 + 节名），无编造条目；信号不足的目标数全部以真实节命中达成，未触及天花板。

## 3. 生成器改动（scripts/generate_knowledge_topology_atlas.py）

- 仅更新 03/04/09 三个 `build_*_index()` 的口径说明文字（注明 `##`–`####` 级标题来源）；索引生成逻辑（`_layered_index_lines`）未变。
- README 覆盖统计表由 signals 自动重算（04: 330/493=66.9%；03: 284/493=57.6%；09: 387/493=78.5%；06 边源 307/493=62.3%）。
- `scripts/templates/atlas_pages/` 四模板零改动；生成结果全部 LF 行尾。

## 4. 验证数字

| 验证项 | 结果 |
|---|---|
| 生成器幂等性 | 连跑两次 `diff -rq` 零差异 ✅ |
| check_topology_quality.py --strict | exit 0：T1=0.0% / T2 ⟹ 75.2% / **T3=6/189（不回退）** / T3 死端 0 / **T4=100%** / T5=0 / T6=0 ✅ |
| check_decision_trees.py --strict | PASS：15 树，死端 0 / KG 缺失 0 / 定量占比达标 ✅ |
| kb_auditor | exit 0：死链 0 / 跨层 0 / 模板化 ⟹ 0 ✅ |
| mdbook build | exit 0 ✅ |
| semantic_health | total=98.3 grade OK；**topo=98.4（与基线持平不退化）** ✅ |

## 5. 附注

- `concept/00_meta/knowledge_topology/kg_tlo_alignment.md` 为 CRLF 行尾，系 2026-07-12 人工维护文件、非本生成链产物，按「只重生成不手改」纪律未动；建议后续由其维护流程统一转 LF。
- 03 索引新增少量 quiz 页条目（quiz 页内 `### Q…场景/陷阱` 题目小节为真实场景判定/反例资产），节名即题面，属真实来源非编造。
- 基线快照留存于 `tmp/w2b_backup/`（不提交）。
