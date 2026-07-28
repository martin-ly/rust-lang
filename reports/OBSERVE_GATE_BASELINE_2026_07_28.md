# 语义观察门基线报告（2026-07-28）

**EN**: Semantic Observe Gates Baseline Report
**Summary**: 记录全部 6 个语义观察门在 2026-07-28 的基线状态，供后续季度/月度监控对比。所有观察门默认 `continue-on-error: true`，不阻断 PR。

> **Rust 版本**: 1.97.1 (Edition 2024)
> **生成时间**: 2026-07-28
> **挂载位置**: `scripts/run_quality_gates.sh` 观察段、`.github/workflows/quality_gates.yml`

---

## 观察门清单（共 6 个）

| # | 观察门 | 脚本 | 当前基线 | 状态 |
|---:|---|---|---|:---:|
| O1 | Stub Purity | `scripts/check_stub_purity.py` | 伪 stub=0 / 空壳页=0 / 高重复=0 | ✅ |
| O2 | Cross-Domain Coverage | `scripts/check_cross_domain_coverage.py --strict` | 16/16 覆盖 = 100% | ✅ |
| O3 | KG Relation Precision | `scripts/check_kg_relation_precision.py --strict` | generic_ratio=0.00%（核心 50 实体） | ✅ |
| O4 | Decision Tree rustc Error Code Coverage | `scripts/check_decision_trees.py --strict` | 节点歧义=0 / Top 30 覆盖率=30/30=100% | ✅ |
| O5 | Version Semantic Injection | `scripts/check_version_semantic_injection.py --strict` | 74/74 映射 = 100% | ✅ |
| O6 | Authority Semantic Diff | `scripts/authority_semantic_diff.py --strict` | P0=0 / P1=0 | ✅ |

---

## 各门详细输出

### O1 Stub Purity

```text
扫描页数：1029
伪 stub（声明为 stub 但正文过长）：0
空壳页（未声明 stub 但正文极短）：0
高重复正文（vs concept/ 权威页相似度 > 0.25）：0
```

### O2 Cross-Domain Coverage

```text
总主题数：16
已覆盖：16 (100.0%)
未覆盖：0
```

覆盖主题包括：let chains、unsafe extern blocks、async + unsafe、FFI + async、no_std + async、const generics + trait objects、GAT + async、Send/Sync boundaries、Pin projection、allocator_api、match ergonomics、temporary scope、const trait impl、RPITIT/TAIT、async fn / Future equivalence、unsafe op in unsafe fn。

### O3 KG Relation Precision

```text
total_relations=8410 generic_ratio=0.00%
core_entities=50 core_relations=2470 core_generic_ratio=0.00%
core_lacking_semantic=0
```

### O4 Decision Tree rustc Error Code Coverage

```text
trees=21 nodes=368 edges=416
quant_rate=78.6% (基线 ≥50%)
dead_ends=0 unknown_concepts=0
node_rustc_codes=32 unique=32 ambiguous=0
top30_coverage=30/30 (100%)
[decision-trees] PASS
```

### O5 Version Semantic Injection

```text
版本范围：1.90 – 1.97（共 8 个稳定版本）
提取特性数：74
已映射：74 (100.0%)
未映射：0
```

### O6 Authority Semantic Diff

```text
[authority_semantic_diff] P0=0 P1=0
✅ 所有核心页均覆盖权威语义关键词。
```

---

## 使用方式

1. **每次 PR**：CI 自动运行全部 6 个观察门，`continue-on-error: true`，结果写入 PR summary。
2. **每月/每季度**：人工对比本基线，观察指标是否退化。
3. **转正评估**：任一观察门连续 4 周或连续 10 次 CI 达标且 `--strict` exit=0，可按 AGENTS.md §5.2 流程申请转阻断。

---

## 历史变更

- 2026-07-28：新增 O6 `authority_semantic_diff`；其余 O1–O5 基线与 AGENTS.md §5.1 一致。
