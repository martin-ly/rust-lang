#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""P4 语义质量门：语义健康聚合仪表盘。

聚合今日 4 份语义基线（metadata_consistency / topology_quality / content_overlap_v2 /
kg_shapes_validation）为一份"语义健康仪表盘"，与旧的"数量型 kb_quality_dashboard"互补：
旧仪表盘数数量（⟹/mermaid/代码块），本仪表盘衡量语义（一致性/闭环/交叉/唯一/KG 完整）。

语义健康分（0-100，加权，越高越好；低于阈值记 WARN/FAIL）：
  元数据一致性  30%  由 flagged_files 占比推导（flag 越少越高）
  拓扑实质度    25%  定义套话率/关系塌缩/跳出率/死端/定量占比/泄漏/占位 综合
  去重健康      20%  MERGE+DOCS_INTERNAL（应处理重复）越少越高
  KG 完整性     25%  K1..K6 全过为满分，K1b 缺 bloomLevel 小幅扣分
输出 reports/SEMANTIC_HEALTH_<date>.{md,json}
"""
from __future__ import annotations

import argparse
import datetime as _dt
import glob
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REP = os.path.join(ROOT, "reports")


def latest(prefix, date):
    p = os.path.join(REP, f"{prefix}_{date}.json")
    if os.path.exists(p):
        return p
    c = sorted(glob.glob(os.path.join(REP, f"{prefix}_*.json")))
    return c[-1] if c else None


def load(p):
    return json.load(open(p, encoding="utf-8")) if p and os.path.exists(p) else None


def clamp(x, lo=0.0, hi=100.0):
    return max(lo, min(hi, x))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--date", default=_dt.date.today().isoformat())
    ap.add_argument("--strict", action="store_true")
    args = ap.parse_args()
    d = args.date

    meta = load(latest("METADATA_CONSISTENCY_BASELINE", d))
    topo = load(latest("TOPOLOGY_QUALITY", d))
    over = load(latest("CONTENT_OVERLAP_V2", d))
    kg = load(latest("KG_SHAPES_VALIDATION", d))
    triage = load(latest("OVERLAP_TRIAGE", d))

    missing = [n for n, x in [("metadata", meta), ("topology", topo), ("overlap", over), ("kg", kg)] if x is None]
    if missing:
        print(f"missing baselines: {missing}; run the P0/P3 checkers first")
        return 2

    # 1) 元数据一致性分：flagged 占比 -> 分
    ms = meta["summary"]
    meta_flag_pct = ms["flagged_files"] / ms["scanned"] if ms["scanned"] else 0
    metadata_score = clamp(100 * (1 - meta_flag_pct))

    # 2) 拓扑实质度分
    ts = topo["summary"]
    topo_pen = 0
    if ts.get("T1_def_low_rate") is not None:
        topo_pen += min(40, ts["T1_def_low_rate"] * 100)          # 套话率，满分扣 40
    if ts.get("T2_top_rate") is not None and ts["T2_top_rate"] >= 0.95:
        topo_pen += 20                                            # 关系塌缩
    topo_pen += min(15, ts.get("T3_jump_rate", 0) * 50)           # 跳出率
    topo_pen += min(10, ts.get("T3_dead_ends", 0) * 3)            # 死端
    if ts.get("T4_quant_rate", 1) < 0.5:
        topo_pen += 10                                            # 判定缺定量
    topo_pen += min(3, ts.get("T5_leaks", 0))
    topo_pen += min(2, ts.get("T6_placeholders", 0))
    topology_score = clamp(100 - topo_pen)

    # 3) 去重健康分：应处理重复（MERGE+DOCS_INTERNAL）相对索引量
    oi = over
    actionable = 0
    if triage:
        actionable = triage["summary"].get("MERGE", 0) + triage["summary"].get("DOCS_INTERNAL", 0)
    else:
        actionable = oi.get("hits", 0)
    indexed = oi.get("indexed", 1) or 1
    dup_ratio = actionable / indexed
    dedup_score = clamp(100 - dup_ratio * 400)  # ~ 每 25% 可处理重复扣到 0

    # 4) KG 完整性分
    ks = kg["summary"]
    kg_pen = 0
    for k in ["K1_missing_required", "K2_bad_path", "K3_not_bilingual",
              "K4_duplicate_id", "K5_dangling_relations", "K6_bad_tree_nodes"]:
        kg_pen += 15 if ks.get(k, 0) > 0 else 0
    kg_pen += min(10, ks.get("K1b_missing_bloomLevel", 0) * 0.2)  # 缺 bloomLevel 小幅
    kg_score = clamp(100 - kg_pen)

    total = clamp(0.30 * metadata_score + 0.25 * topology_score + 0.20 * dedup_score + 0.25 * kg_score)
    grade = "OK" if total >= 85 else ("WARN" if total >= 60 else "FAIL")

    summary = {
        "date": d, "total_score": round(total, 1), "grade": grade,
        "metadata_score": round(metadata_score, 1),
        "topology_score": round(topology_score, 1),
        "dedup_score": round(dedup_score, 1),
        "kg_score": round(kg_score, 1),
        "inputs": {
            "metadata_flagged": f"{ms['flagged_files']}/{ms['scanned']}",
            "topology_T1_def_low_rate": ts.get("T1_def_low_rate"),
            "topology_T2_top_rate": ts.get("T2_top_rate"),
            "overlap_hits": oi.get("hits"),
            "overlap_actionable_MERGE_DOCSINTERNAL": actionable,
            "kg": {k: ks.get(k) for k in ["K1_missing_required", "K1b_missing_bloomLevel", "K2_bad_path",
                                          "K3_not_bilingual", "K4_duplicate_id", "K5_dangling_relations", "K6_bad_tree_nodes"]},
        },
    }

    out_md = os.path.join(REP, f"SEMANTIC_HEALTH_{d}.md")
    out_json = os.path.join(REP, f"SEMANTIC_HEALTH_{d}.json")
    with open(out_json, "w", encoding="utf-8") as f:
        json.dump(summary, f, ensure_ascii=False, indent=2)
    with open(out_md, "w", encoding="utf-8") as f:
        f.write(f"# 语义健康仪表盘（P4）\n\n")
        f.write(f"**日期**: {d}  **语义健康总分**: **{summary['total_score']} / 100**  **等级**: **{grade}** "
                f"(OK≥85 / WARN≥60 / FAIL<60)\n\n")
        f.write("> 与 `kb_quality_dashboard.md`（数量型：⟹/mermaid/代码块计数）互补；本仪表盘衡量语义质量（一致性/闭环/交叉/唯一/KG 完整）。\n\n")
        f.write("| 维度 | 权重 | 得分 | 关键证据 |\n|---|:---:|:---:|:---|\n")
        f.write(f"| 元数据一致性 | 30% | {summary['metadata_score']} | flagged {ms['flagged_files']}/{ms['scanned']}（D1互斥/D2脱节/D3重声明/D4版本/D5 nightly/D6套话） |\n")
        f.write(f"| 拓扑实质度 | 25% | {summary['topology_score']} | 定义套话率 {ts.get('T1_def_low_rate')} / 关系塌缩 {ts.get('T2_top_rate')} / 跳出 {ts.get('T3_jump_rate')} / 死端 {ts.get('T3_dead_ends')} / 判定定量 {ts.get('T4_quant_rate')} |\n")
        f.write(f"| 去重健康 | 20% | {summary['dedup_score']} | 重叠命中 {oi.get('hits')}，可处理（MERGE+DOCS_INTERNAL） {actionable} |\n")
        f.write(f"| KG 完整性 | 25% | {summary['kg_score']} | K1-K6={summary['inputs']['kg']} |\n")
        f.write(f"\n**总分**: {summary['total_score']} = 0.30×{summary['metadata_score']} + 0.25×{summary['topology_score']} + 0.20×{summary['dedup_score']} + 0.25×{summary['kg_score']}\n\n")
        f.write("## 趋势与可持续使用\n\n")
        f.write("- 每次 P0/P3 检查器跑后重跑本脚本，写入 `SEMANTIC_HEALTH_<date>.json`，即可绘制趋势。\n")
        f.write("- 建议接入 `run_quality_gates.sh` 作为第 15 个 observe 门；--strict 可在 grade=FAIL 时退出 1。\n")
        f.write("- 目标基线：metadata≥60、topology≥40、dedup≥80、kg≥90、total≥60（脱离 FAIL）。\n")
        f.write(f"\n## 机器可读\n\n- JSON: `reports/SEMANTIC_HEALTH_{d}.json`\n")

    print(f"[P4] semantic health total={summary['total_score']} grade={grade} "
          f"(meta={summary['metadata_score']} topo={summary['topology_score']} "
          f"dedup={summary['dedup_score']} kg={summary['kg_score']})")
    print(f"[P4] report: {os.path.relpath(out_md, ROOT).replace(chr(92),'/')}")
    if args.strict and grade == "FAIL":
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
