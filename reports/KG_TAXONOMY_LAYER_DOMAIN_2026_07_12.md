# KG 领域/层级模型建设报告（taxonomy + layer/domain 增强）

**日期**: 2026-07-12
**范围**: `concept/00_meta/kg_data_v3.json`（474 实体 / 5799→5797 关系）、`scripts/` KG 工具链
**结论**: ✅ 全部质量门通过（`check_kg_shapes.py --strict` exit=0；`owl_consistency_check.py` exit=0；`semantic_health.py` kg 维度 90，不下降）

---

## 1. 机器可读领域/层级模型：`concept/00_meta/taxonomy.yaml`

新建 `taxonomy.yaml`（v1.0），作为领域/层级分类的**唯一配置源**，包含三部分：

1. **layers（L0-L7）**：每层含 `id / directory / name_zh / name_en / responsibility / bloom_range`：
   - L0 元框架（00_meta，Bloom Meta）· L1 基础（01_foundation，L1-L2）· L2 中级（02_intermediate，L2-L3）·
     L3 高级（03_advanced，L3-L4）· L4 形式化（04_formal，L4-L5）· L5 比较（05_comparative，L5）·
     L6 生态（06_ecosystem，L5-L6）· L7 未来（07_future，L6）。
   - Bloom 范围依据 concept/ 文件 `**Bloom 层级**: Lx` 标注的实际分布（L1×23 / L2×144 / L3×114 / L4×171 / L5×17）标定。
2. **domains（20 个）**：从 concept/ 二级目录归纳——`meta_framework / ownership_memory / type_system /
   language_core / macros_metaprogramming / concurrency / async / process_ipc / unsafe_lowlevel /
   formal_methods / comparative / ecosystem_toolchain / ecosystem_design / ecosystem_web /
   ecosystem_embedded / ecosystem_data / ecosystem_security / ecosystem_domains / version_evolution`，
   外加兜底 `uncategorized`。每个领域含名、描述、`path_prefixes`（推断依据）、代表概念。
3. **matrix_rules**：层×领域矩阵 `M[L][D]` 生成规则——layer 取 path 第一段查 `layers[*].directory`
   （根目录散落文件按 `extra_prefixes` 归 L0）；domain 取 `path_prefixes` **最长前缀匹配**，无匹配归
   `uncategorized`；每实体单 layer 单 domain；`uncategorized` 非空即 taxonomy 与目录失同步的治理信号。

## 2. KG 增强脚本：`scripts/add_kg_layer_domain.py`

- 读 `taxonomy.yaml` + `kg_data_v3.json`，按 `ex:path` 为每实体补 `ex:layer` / `ex:domain`，写回 v3。
- **备份**：首次运行写 `concept/00_meta/kg_data_v3.json.bak`（`.gitignore` 已覆盖 `*.bak`）；重跑不覆盖原始备份。
- **幂等**：重跑 `changed=0`，结果完全一致。
- **结果**：474/474 覆盖，**覆盖率 100.00%，未归类 0**。
- 层分布：L0=71 L1=56 L2=39 L3=58 L4=54 L5=20 L6=116 L7=60。
- 领域分布（Top）：meta_framework=71 · version_evolution=60 · formal_methods=54 · language_core=49 ·
  ecosystem_toolchain=38 · type_system=27 · unsafe_lowlevel=24 · ecosystem_design=23，其余 15 个领域合计 122。
- 明细报告：`reports/KG_LAYER_DOMAIN_2026-07-12.{md,json}`。

## 3. `scripts/check_kg_shapes.py` 扩展 K7（向后兼容）

- 新增 **K7**：实体必须含非空 `ex:layer` 与 `ex:domain`；缺失计入 `K7_missing_layer_domain`。
- 阈值 0：`--strict` 时 K7>0 即 exit 1；默认 warning 模式行为不变。
- K1-K6、K1b、报告格式与既有消费方（`semantic_health.py` 只读 K1-K6/K1b）完全兼容。

## 4. dependsOn 环修复：`TypeSystem → Ownership → TypeSystem`

**成因分析**：

- `ex:TypeSystem dependsOn ex:Ownership`（_:rel89）源自
  `concept/01_foundation/02_type_system/04_type_system.md:20`
  「**前置概念**: [Ownership](...)」——语义正确：类型系统（L1 基础，目录序 02）以所有权（目录序 01）为前提。
- `ex:Ownership dependsOn ex:TypeSystem`（_:rel73/_:rel74，重复两条）源自
  `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md:25`
  「**前置概念**: [Stack vs Heap](../02_type_system/04_type_system.md) · [Scope and Drop](同)」。
  该标注自相矛盾且链接错误：
  1. 同文件第 20 行明确声明「**前置依赖**: 无（L1 入口概念）」；
  2. 两条锚文本（Stack vs Heap / Scope and Drop）均指向同一篇 `04_type_system.md`，且 concept/ 中不存在
     对应的独立文档，属误链；
  3. 所有权是知识库 L1 入口概念，依赖类型系统违反层级方向（保守方向：低层不依赖高层）。

**修正**（保守方向，保留 `TypeSystem → Ownership`）：

- v3 数据：删除 _:rel73/_:rel74 两条错误边，`relation_count` 5799→5797（已备份于 `.bak`）。
- 源头文档：`01_ownership.md:25` 改为「**相关概念**: [Type System](...)（本文无前置依赖）」，
  消除与「前置依赖: 无」的矛盾，并防止 `generate_kg_index.py`（`PRECONCEPT_RE` 只匹配「前置概念」）
  重新生成时再次引入该环。
- 验证：`python scripts/owl_consistency_check.py` → **exit=0，dependsOn 无环**。

## 5. zh 空标签修复

- **统计**：v3 中 311/474 实体的 `skos:prefLabel` zh 项为空字符串（en 均存在）。
- **根因**：`kg_index.json` 中这 311 个条目 `title` 为空（仅有 `en`），`generate_kg_v3.py` 直接
  `{"@value": title, "@language": "zh"}` 写入空串。
- **修复**：
  - 生成端（易修，已修）：`scripts/generate_kg_v3.py` 增加回退链
    `title or en or Path(path).stem`，重新生成不再产生空 zh 标签。
  - 数据端：v3 中 311 个空 zh 标签已用对应 en 标签回填（语义占位，中文译名留待 i18n 治理补全）。
- **待办**：311 个回填实体 zh=英文占位，建议后续 i18n 批次补中文译名（可结合
  `scripts/add_bilingual_annotations.py` 治理流）。

## 6. 验证结果

| 检查 | 命令 | 结果 |
|---|---|---|
| KG SHACL（含新 K7） | `python scripts/check_kg_shapes.py --strict` | ✅ exit=0，K1-K7 全 0（K1b 缺 bloomLevel 55，仅记录） |
| OWL 一致性 | `python scripts/owl_consistency_check.py` | ✅ exit=0，无环/无悬空/对称性通过 |
| 语义健康 | `python scripts/semantic_health.py` | ✅ kg=90（与 07-11 基线持平，不下降）；总分 64.5→69.1（WARN，提升来自元数据维度） |
| 幂等性 | `add_kg_layer_domain.py` 重跑 | ✅ changed=0，覆盖率 100% |

## 7. 产出清单

| 文件 | 变更 |
|---|---|
| `concept/00_meta/taxonomy.yaml` | 新建：L0-L7 层级 + 20 领域 + 矩阵规则 |
| `scripts/add_kg_layer_domain.py` | 新建：layer/domain 增强（备份、幂等、--strict、--report） |
| `scripts/check_kg_shapes.py` | 扩展 K7 检查（向后兼容） |
| `scripts/generate_kg_v3.py` | zh 标签空值回退链 |
| `concept/00_meta/kg_data_v3.json` | +474 实体 layer/domain；−2 错误 dependsOn 边；311 zh 回填；relation_count 5797 |
| `concept/00_meta/kg_data_v3.json.bak` | 原始备份（gitignored） |
| `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | 前置概念→相关概念（断环源头修复） |
| `reports/KG_LAYER_DOMAIN_2026-07-12.{md,json}` | 增强明细 |
| `reports/KG_SHAPES_VALIDATION_2026-07-12.{md,json}` · `reports/OWL_CONSISTENCY_CHECK_2026_07_12.md` · `reports/SEMANTIC_HEALTH_2026-07-12.{md,json}` | 质量门输出 |

## 8. 后续建议

1. 将 `python scripts/add_kg_layer_domain.py --strict` 接入 `scripts/run_quality_gates.sh`（KG 数据变更后需先重跑增强再过 K7）。
2. i18n 批次补全 311 个 zh=英文占位标签的中文译名。
3. `K1b`（55 实体缺 `ex:bloomLevel`）按 taxonomy 的 `bloom_range` 批量回填，可进一步抬升 semantic_health 的 kg 分。
4. AGENTS.md §5.1 质量门清单可在下次维护时补记 K7 与 taxonomy.yaml 的同步规则。
