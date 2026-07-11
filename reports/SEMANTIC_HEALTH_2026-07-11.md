# 语义健康仪表盘（P4）

**日期**: 2026-07-11  **语义健康总分**: **64.5 / 100**  **等级**: **WARN** (OK≥85 / WARN≥60 / FAIL<60)

> 与 `kb_quality_dashboard.md`（数量型：⟹/mermaid/代码块计数）互补；本仪表盘衡量语义质量（一致性/闭环/交叉/唯一/KG 完整）。

| 维度 | 权重 | 得分 | 关键证据 |
|---|:---:|:---:|:---|
| 元数据一致性 | 30% | 49.2 | flagged 242/476（D1互斥/D2脱节/D3重声明/D4版本/D5 nightly/D6套话） |
| 拓扑实质度 | 25% | 41.2 | 定义套话率 0.255 / 关系塌缩 0.992 / 跳出 0.166 / 死端 0 / 判定定量 0.578 |
| 去重健康 | 20% | 84.7 | 重叠命中 558，可处理（MERGE+DOCS_INTERNAL） 54 |
| KG 完整性 | 25% | 90 | K1-K6={'K1_missing_required': 0, 'K1b_missing_bloomLevel': 55, 'K2_bad_path': 0, 'K3_not_bilingual': 0, 'K4_duplicate_id': 0, 'K5_dangling_relations': 0, 'K6_bad_tree_nodes': 0} |

**总分**: 64.5 = 0.30×49.2 + 0.25×41.2 + 0.20×84.7 + 0.25×90

## 趋势与可持续使用

- 每次 P0/P3 检查器跑后重跑本脚本，写入 `SEMANTIC_HEALTH_<date>.json`，即可绘制趋势。
- 建议接入 `run_quality_gates.sh` 作为第 15 个 observe 门；--strict 可在 grade=FAIL 时退出 1。
- 目标基线：metadata≥60、topology≥40、dedup≥80、kg≥90、total≥60（脱离 FAIL）。

## 机器可读

- JSON: `reports/SEMANTIC_HEALTH_2026-07-11.json`
