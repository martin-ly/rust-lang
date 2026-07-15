# 决策树 rustc error code 覆盖报告

**EN**: Decision Tree rustc Error Code Coverage Report
**Summary**: Extend `concept/00_meta/knowledge_topology/decision_trees.yaml` with optional `rustc_error_codes` mappings, validate format/uniqueness/merging, and generate an error-code lookup index.

> **Rust 版本**: 1.97.0+ (Edition 2024)
> **日期**: 2026-07-15
> **相关文件**:
>
> - `concept/00_meta/knowledge_topology/decision_trees.yaml`
> - `concept/00_meta/knowledge_topology/decision_tree_error_code_index.json`
> - `concept/00_meta/knowledge_topology/09_reasoning_judgment_tree_atlas.md`
> - `scripts/check_decision_trees.py`

---

## 1. 变更概述

1. **Schema 扩展**：在 `decision_trees.yaml` 的树级元数据中新增可选字段 `rustc_error_codes: [E\d{4}, ...]`。
2. **错误码映射**：为 **10 棵已有决策树** 添加 rustc error code 标注，并新增 **2 棵决策树** 覆盖此前未包含的 E0433 / E0609，共覆盖 **12 棵决策树 / 14 个唯一错误码 / 26 条映射**。
3. **校验增强**：扩展 `scripts/check_decision_trees.py`：
   - 校验每个错误码符合 `^E\d{4}$` 模式；
   - 检测跨树重复映射并作为「合并」报告，不阻断（因为 E0277/E0597 等天然跨多个语义域）；
   - 新增 `--generate-index` 生成错误码 → 决策树索引 JSON。
4. **索引生成**：生成 `decision_tree_error_code_index.json`，包含来源文件、锚点、合并信息。
5. **文档补全**：在 `09_reasoning_judgment_tree_atlas.md` 新增 §7，以 mermaid 图展示两棵补充判定树。

---

## 2. 错误码映射表

| rustc 错误码 | 错误含义 | 映射决策树 | 树标题 |
|:---|:---|:---|:---|
| E0106 | missing lifetime specifier | J-LIFE-02, DF-LIFE-03 | 生命周期判定树 |
| E0119 | conflicting implementations of trait | DF-TRAIT-04 | Trait 判定树 |
| E0277 | trait bound not satisfied | J-TYPE-03, DF-TRAIT-04, DF-GENERIC-05, DF-CONC-06 | 类型不匹配 / Trait / 泛型 / 并发判定树 |
| E0283 | type annotations needed | J-TYPE-03, DF-GENERIC-05 | 类型不匹配 / 泛型判定树 |
| E0308 | mismatched types | J-TYPE-03 | 类型不匹配判定树 |
| E0373 | closure may outlive current function | DF-ASYNC-07 | 异步判定树 |
| E0382 | use of moved value | DF-OWN-01 | 所有权判定树 |
| E0433 | failed to resolve use of undeclared crate/module | J-MODULE-07 | 名称解析判定树（新增） |
| E0499 | cannot borrow as mutable more than once | J-BORROW-01, DF-BORROW-02 | 借用冲突 / 借用判定树 |
| E0501 | cannot borrow as immutable because it is also borrowed as mutable | J-BORROW-01, DF-BORROW-02 | 借用冲突 / 借用判定树 |
| E0502 | cannot borrow as mutable because it is also borrowed as immutable | J-BORROW-01, DF-BORROW-02 | 借用冲突 / 借用判定树 |
| E0597 | value does not live long enough | J-LIFE-02, DF-BORROW-02, DF-LIFE-03, DF-ASYNC-07 | 生命周期 / 借用 / 异步判定树 |
| E0609 | no field on type | J-FIELD-08 | 字段访问判定树（新增） |
| E0621 | explicit lifetime required | J-LIFE-02, DF-LIFE-03 | 生命周期判定树 |

### 2.1 映射到任务要求的 8 个核心错误码

任务列出的 8 个核心错误码均已覆盖：

- ✅ E0502 → J-BORROW-01, DF-BORROW-02
- ✅ E0597 → J-LIFE-02, DF-BORROW-02, DF-LIFE-03, DF-ASYNC-07
- ✅ E0373 → DF-ASYNC-07
- ✅ E0382 → DF-OWN-01
- ✅ E0308 → J-TYPE-03
- ✅ E0609 → J-FIELD-08
- ✅ E0433 → J-MODULE-07
- ✅ E0277 → J-TYPE-03, DF-TRAIT-04, DF-GENERIC-05, DF-CONC-06

---

## 3. 校验结果

执行命令：

```bash
python scripts/check_decision_trees.py --generate-index --strict
```

输出摘要：

```text
[decision-trees] file=concept/00_meta/knowledge_topology/decision_trees.yaml
  trees=17 nodes=276 edges=296
  decisions=52 quantitative=52 quant_rate=100.0% (基线 ≥50%)
  dead_ends=0 unknown_concepts=0
  rustc_error_codes=26 unique=14 merged=8
[decision-trees] PASS
```

- **结构错误**：0
- **死端**：0
- **缺失 KG 概念引用**：0
- **错误码格式错误**：0
- **跨树合并映射**：8 个错误码（E0106, E0277, E0283, E0499, E0501, E0502, E0597, E0621），均为语义域共享，已登记于索引 `merged_codes`。

---

## 4. Schema 变更详情

在 `decision_trees.yaml` 每棵树的树级字段中，可选新增：

```yaml
- id: J-BORROW-01
  title_zh: 借用冲突判定树
  title_en: Borrow Conflict Judgment Tree
  source:
    file: concept/00_meta/knowledge_topology/09_reasoning_judgment_tree_atlas.md
    anchor: "#31-借用冲突判定树"
  covered_concepts: [ex:Borrowing, ex:InteriorMutability, ex:SmartPointers]
  rustc_error_codes: [E0499, E0501, E0502]   # 新增可选字段
  nodes: ...
```

`scripts/check_decision_trees.py` 已更新以识别并校验该字段。

---

## 5. 生成文件

- `concept/00_meta/knowledge_topology/decision_tree_error_code_index.json`
  - `index`: `错误码 -> [{tree_id, source_file, source_anchor}, ...]`
  - `merged_codes`: 跨多树共享的错误码清单

---

## 6. 质量门状态

已运行 `python scripts/check_decision_trees.py --strict`：**PASS**。

> 注：本脚本目前是独立校验工具，未直接挂载到 `scripts/run_quality_gates.sh` 的 23 个阻断门中。本次变更未引入新的阻断失败；建议在 CI 夜间报告中将其作为观察项运行（默认 exit 0，结构错误时 exit 1）。

---

## 7. 备注与后续建议

1. **跨树重复为 intentional merge**：E0277、E0597 等错误码在不同决策树中代表不同侧面的根因（如 E0277 可同时是泛型 bound、trait bound、Send/Sync bound），因此允许重复映射；索引文件已明确记录合并关系。
2. **新增树来源锚点**：J-MODULE-07 / J-FIELD-08 的 Markdown 对应图已追加到 `09_reasoning_judgment_tree_atlas.md` §7，保持 YAML/MD 一致性。
3. **未覆盖的运行时错误**：J-PANIC-04、J-UNSAFE-05、DF-UNSAFE-08、DF-CROSS-09 主要对应运行时 panic / UB / unsafe 边界，不直接绑定到 rustc 编译期错误码，因此未添加 `rustc_error_codes`。
