# KG relatedTo 压缩基线报告（2026-10-12）

> **EN**: KG relatedTo Compression Baseline Report (2026-10-12)
> **Summary**: 统计 `concept/00_meta/kg_data_v3.json` 全局 `ex:relatedTo` 占比基线（长期目标 <50%），并按 `scripts/compress_kg_relatedto.py` 的启发式规则做只读 dry 模拟，给出可压缩候选数。未执行 `--apply`，KG 数据文件未改动。
> **数据来源**: `concept/00_meta/kg_data_v3.json`（只读）、`concept/00_meta/kg_index.json`（只读）、`scripts/compress_kg_relatedto.py`（dry-run）
> **关联任务**: 长期跟踪项刷新（轨道 E）

---

## 1. 当前全局谓词占比（基线）

`kg_data_v3.json` → `relations` 共 **10625** 条：

| 谓词 (`ex:predicate`) | 数量 | 占比 |
|---|---:|---:|
| `ex:relatedTo` | **8353** | **78.62%** |
| `ex:dependsOn` | 1192 | 11.22% |
| `ex:entails` | 1080 | 10.16% |

**基线结论**: `ex:relatedTo` 占比 **78.62%**，距长期目标 **<50%** 尚差 **≥28.62 个百分点**（需至少压缩 3041 条 relatedTo 边才能达标）。

## 2. compress_kg_relatedto.py dry-run 实测结果

```
python scripts/compress_kg_relatedto.py   # 默认 dry-run
[compress] changed=0 relatedTo -> precise predicates
[compress] unchanged=0
```

⚠️ **脚本与数据 schema 不匹配（本次发现，未修改脚本）**：脚本第 150 行按 `r.get("@type") != "ex:relatedTo"` 过滤，但当前 `kg_data_v3.json` 中所有 relation 的 `@type` 均为 `ex:RelationAnnotation`，谓词存放在 `ex:predicate` 字段。因此脚本对当前数据命中 0 条（历史报告 2026_07_16 起各期同样全为 0）。**主代理若决定 `--apply`，需先修正脚本过滤条件**（改为按 `ex:predicate == "ex:relatedTo"` 过滤，并同步写回 `ex:predicate`）。

## 3. 可压缩候选数（只读 dry 模拟，复刻脚本 H0–H17 规则、按 ex:predicate 过滤）

对 8353 条 `ex:relatedTo` 逐条套用脚本启发式（不写回任何文件）：

| 目标谓词 | 命中数 | 主要规则 |
|---|---:|---|
| `ex:hasPart` | 4355 | H1-index-hasPart 2961 · H0-readme-summary 1122 · H7-meta-organizer 203 · H14 69 |
| `ex:dependsOn` | 1147 | H4-higher-layer 1108 · H17 39 |
| `ex:refines` | 711 | H3-same-dir-refines |
| `ex:entails` | 547 | H5-lower-layer-entails |
| `ex:partOf` | 447 | H2-index-partOf 426 · H15 21 |
| `ex:appliesTo` | 112 | H8-quiz-appliesTo |
| **可压缩候选合计** | **7319** | 占 relatedTo 的 87.6% |
| 未命中（仍 relatedTo） | 1034 | 兜底弱语义边 |

**若全部候选压缩（模拟值，未执行）**: relatedTo 占比将由 78.62% 降至 **1034/10625 = 9.73%**，远低于 50% 目标线。

## 4. 建议（供主代理决策，本报告不执行 --apply）

1. 先修正 `compress_kg_relatedto.py` 的 `@type` 过滤 bug，再跑 dry-run 复核候选数（预期与 §3 模拟一致）。
2. 压缩分两批执行以降低风险：第一批 H0/H1/H2（导航页 hasPart/partOf，5407 条，语义最确定）；第二批 H3–H17（711+1147+547+447+112 条，建议抽查 evidence 质量）。
3. 保留 1034 条未命中 relatedTo 作为兜底弱语义边，符合脚本设计意图。
4. 每批 `--apply` 后重跑本报告统计口径（§1 脚本命令）验证占比变化。

## 5. 验证口径（可复现）

```bash
python - <<'EOF'
import json, collections
kg = json.load(open('concept/00_meta/kg_data_v3.json', encoding='utf-8'))
rel = kg['relations']
c = collections.Counter(r.get('ex:predicate') for r in rel)
print(len(rel), c.most_common())
EOF
```

---

*生成时间: 2026-10-12（轨道 E 长期跟踪刷新）。KG 数据文件（kg_data_v3.json / concept_kb.json）本次只读未改动；未执行 --apply。*
