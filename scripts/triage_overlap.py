#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""P1 前置：对 CONTENT_OVERLAP_V2 的命中对做分类（triage），产出可执行改写清单。

输入：reports/CONTENT_OVERLAP_V2_<date>.json（由 detect_content_overlap_v2.py 生成）
分类规则：
  SERIES  合理系列重复（保留但标注）：路径/标题含版本快照/分章（rust_1NN、readme_rust_、_partN、_vN、
          _19N、_comprehensive_enhancement_report 等），或同一 crate 的版本序列。
  MERGE   应合并近克隆：sim>=0.85 且非 SERIES（模板复制，如 design_patterns_formal 多 README）。
  DOCS_INTERNAL  docs/ 内同主题互抄：两文件都在 docs/ 且 sim>=0.7（指南/研究笔记间重复）。
  REVIEW  其余需人工复核。
输出：reports/OVERLAP_TRIAGE_<date>.{md,json}
"""
from __future__ import annotations

import argparse
import datetime as _dt
import glob
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

SERIES_RE = re.compile(
    r"rust_1\d\d|rust_19\d|readme_rust_|_part\d|_v\d+|_19\d\d|20\d\d_\d\d_\d\d|"
    r"comprehensive_enhancement_report|examples_collection|snapshot", re.IGNORECASE)


def is_series(o):
    if SERIES_RE.search(o["f1"]) or SERIES_RE.search(o["f2"]):
        return True
    if SERIES_RE.search(o.get("t1", "")) or SERIES_RE.search(o.get("t2", "")):
        return True
    # 同一 crate 内的版本序列
    p1 = o["f1"].split("/")
    p2 = o["f2"].split("/")
    if p1[0] == "crates" and p2[0] == "crates" and len(p1) > 1 and p1[1] == p2[1]:
        if re.search(r"19\d|1\d\d|part", o["f1"] + o["f2"]):
            return True
    return False


def triage(o):
    top1 = o["f1"].split("/")[0]
    top2 = o["f2"].split("/")[0]
    if is_series(o):
        return "SERIES"
    if o["sim"] >= 0.85:
        return "MERGE"
    if top1 == "docs" and top2 == "docs" and o["sim"] >= 0.7:
        return "DOCS_INTERNAL"
    return "REVIEW"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    src = os.path.join(ROOT, "reports", f"CONTENT_OVERLAP_V2_{args.date}.json")
    if not os.path.exists(src):
        # 取最新
        cands = sorted(glob.glob(os.path.join(ROOT, "reports", "CONTENT_OVERLAP_V2_*.json")))
        if not cands:
            print("no CONTENT_OVERLAP_V2 json found; run detect_content_overlap_v2.py first")
            return 2
        src = cands[-1]
    data = json.load(open(src, encoding="utf-8"))
    overlaps = data.get("overlaps", [])

    buckets = {"SERIES": [], "MERGE": [], "DOCS_INTERNAL": [], "REVIEW": []}
    for o in overlaps:
        buckets[triage(o)].append(o)

    summary = {k: len(v) for k, v in buckets.items()}
    summary["total"] = len(overlaps)
    summary["source"] = os.path.relpath(src, ROOT).replace("\\", "/")

    out_md = os.path.join(ROOT, "reports", f"OVERLAP_TRIAGE_{args.date}.md")
    out_json = os.path.join(ROOT, "reports", f"OVERLAP_TRIAGE_{args.date}.json")
    with open(out_json, "w", encoding="utf-8") as f:
        json.dump({"summary": summary, "buckets": buckets}, f, ensure_ascii=False, indent=2)

    with open(out_md, "w", encoding="utf-8") as f:
        f.write(f"# 重叠对分类（P1 改写执行清单）\n\n")
        f.write(f"**来源**: `{summary['source']}`  **总对数**: {summary['total']}\n\n")
        f.write("| 分类 | 数量 | 处置 |\n|---|:---:|:---|\n")
        disp = {"SERIES": "保留但标注为版本系列/分章（白名单）", "MERGE": "应合并近克隆（留一删余或 stub 化）",
                "DOCS_INTERNAL": "docs/ 内同主题互抄（合并或互链）", "REVIEW": "人工复核"}
        for k in ["MERGE", "DOCS_INTERNAL", "SERIES", "REVIEW"]:
            f.write(f"| {k} | {summary[k]} | {disp[k]} |\n")
        for k in ["MERGE", "DOCS_INTERNAL", "SERIES", "REVIEW"]:
            f.write(f"\n## {k}（{summary[k]}）Top 25\n\n")
            f.write("| sim | 文件1 | 文件2 |\n|:---:|:---|:---|\n")
            for o in buckets[k][:25]:
                f.write(f"| {o['sim']} | `{o['f1']}` | `{o['f2']}` |\n")
        f.write(f"\n## 机器可读\n\n- JSON: `reports/OVERLAP_TRIAGE_{args.date}.json`\n")

    print(f"[P1-triage] total={summary['total']} MERGE={summary['MERGE']} DOCS_INTERNAL={summary['DOCS_INTERNAL']} "
          f"SERIES={summary['SERIES']} REVIEW={summary['REVIEW']}")
    print(f"[P1-triage] report: {os.path.relpath(out_md, ROOT).replace(chr(92),'/')}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
