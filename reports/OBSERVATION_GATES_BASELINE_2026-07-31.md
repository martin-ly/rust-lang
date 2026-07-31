# 语义观察门基线报告（O1–O5）

> **日期**: 2026-07-31
> **说明**: 本报告记录 5 个语义观察门的最新 `--strict` 运行结果，作为后续转正/持续达标的基线。

## 运行结果摘要

| 观察门 | 命令 | 结果 | 关键指标 |
|---:|---|:---:|---|
| O1 | `python scripts/check_stub_purity.py --strict` | ✅ PASS | 伪 stub 0 / 空壳页 0 / 高重复正文 0 |
| O2 | `python scripts/check_cross_domain_coverage.py --strict` | ✅ PASS | 关键交叉/边界语义域 16/16 覆盖 = 100% |
| O3 | `python scripts/check_kg_relation_precision.py --strict` | ✅ PASS | 核心 50 实体 generic_ratio=0.00% |
| O4 | `python scripts/check_decision_trees.py --strict` | ✅ PASS | 节点歧义 0 / Top 30 error code 映射覆盖 18/30 = 60% |
| O5 | `python scripts/check_version_semantic_injection.py --strict` | ✅ PASS | 1.90–1.97 稳定特性双向链接覆盖 74/74 = 100% |

## 详细输出

### O1 — Stub 纯净度

```
## 高重复正文 (0)
未发现。
```

判定标准：

- 声明为 stub：正文含任一标记（如『本文件为学习入口 stub』、『redirect』等）。
- 伪 stub：声明为 stub，但去元数据后正文 > 25 行 或 > 2000 字节。
- 空壳页：未声明 stub，但去元数据后正文 < 5 行。
- 高重复正文：去代码块后与 concept/ 权威页相似度 > 0.25。

### O2 — 交叉/边界语义域覆盖

```
- ✅ 01_foundation/04_control_flow/02_patterns.md — match ergonomics / default binding mode in Edition 2024
- ✅ 04_formal/05_rustc_internals/09_destructors.md — temporary scope / tail expression drop (Edition 2024)
- ✅ 07_future/02_preview_features/06_const_trait_impl_preview.md — const trait impl (effects system)
- ✅ 07_future/02_preview_features/17_type_alias_impl_trait_preview.md — RTN / RPITIT / TAIT precise capturing
- ✅ 03_advanced/01_async/01_async.md — async fn / Future equivalence + Send across await
- ✅ 03_advanced/02_unsafe/01_unsafe.md — unsafe op in unsafe fn (Edition 2024)
```

### O3 — KG 关系谓词精度

```
[KG relation precision] total_relations=9773 generic_ratio=0.00%
  core_entities=50 core_relations=2685 core_generic_ratio=0.00%
  core_lacking_semantic=0
```

### O4 — 决策树 rustc error code 映射

```
E0106 -> ['J-LIFE-02', 'DF-LIFE-03']
E0117 -> ['DF-TRAIT-04', 'DF-ALGDS-01']
E0277 -> ['J-TYPE-03', 'DF-TRAIT-04', 'DF-GENERIC-05', 'DF-CONC-06']
E0283 -> ['J-TYPE-03', 'DF-GENERIC-05']
E0301 -> ['J-BORROW-01', 'DF-SECARCH-01']
E0499 -> ['J-BORROW-01', 'DF-BORROW-02']
E0501 -> ['J-BORROW-01', 'DF-BORROW-02']
E0502 -> ['J-BORROW-01', 'DF-BORROW-02']
E0597 -> ['J-LIFE-02', 'DF-BORROW-02', 'DF-LIFE-03', 'DF-ASYNC-07']
E0621 -> ['J-LIFE-02', 'DF-LIFE-03']
E0733 -> ['DF-ASYNC-07', 'DF-PIN-01']
[decision-trees] PASS
```

### O5 — 版本语义注入双向链接

```
- crates-io 移除 curl 依赖 (§5.5) ← 06_ecosystem/01_cargo/23_cargo_197_features.md
- --emit 标志 (§6.1) → 06_ecosystem/00_toolchain/07_rustdoc_196_changes.md
- --remap-path-prefix (§6.2) ← 06_ecosystem/00_toolchain/07_rustdoc_196_changes.md, 07_future/05_quizzes/01_quiz_version_and_preview.md
- pin! 示例 (§7.1) ← 00_meta/knowledge_topology/04_example_counterexample_atlas.md
- 空 export_name 示例 (§7.2) ← 00_meta/knowledge_topology/04_example_counterexample_atlas.md
```

## 后续可持续行动

1. **O4 覆盖率提升**: Top 30 常见 rustc error code 当前映射 18/30（60%），距离 ≥80% 转正条件尚有 6 个码的缺口。下一步应补充 E0027、E0308、E0384、E0392、E0495、E0700 等常见码的决策树节点映射。
2. **每月 rerun**: 按 AGENTS.md §7 月度审计节奏，重新运行 O1–O5 并更新本报告。
3. **转正评估**: O2/O3/O5 已达 100%，若连续 4 周/10 次 CI 稳定，可申请按 §5.2 转正为阻断门；O1 当前伪 stub=0，维持稳定即可；O4 需先补齐映射覆盖率。
