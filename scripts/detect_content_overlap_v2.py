#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""P0-3 语义质量门：内容重叠检测 v2（揭穿"0 重复"假象）。

相对旧版 scripts/detect_content_overlap.py 的修正：
  1. 目录全覆盖：concept/knowledge/docs/content/crates（旧版漏 crates）。
  2. 不豁免"贴 stub/归档免责声明"的文件：仅豁免"<=40 行且含重定向标记"的真 stub；
     >150 行却贴免责声明的"假 stub 真正文"必检。
  3. 关键词用全文（旧版 flat_terms[:50] 严重稀释长文）。
  4. 同目录也检测（旧版只跨顶层目录，docs/ 内部、concept/ 内部重复全漏）。
  5. 综合分去掉"标题 x1.5"主导（旧版标题不同即逃过），改为 max(title_sim, kw_sim)。
  6. 倒排索引 + 最小共享词剪枝，避免 O(N^2) 全笛卡尔。

用法：
  python scripts/detect_content_overlap_v2.py            # warning 模式，默认阈值 0.5
  python scripts/detect_content_overlap_v2.py --strict   # 命中数>预算退出 1
  python scripts/detect_content_overlap_v2.py --threshold 0.4 --budget 200
输出：
  reports/CONTENT_OVERLAP_V2_<date>.md / .json
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import re
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

SCAN_DIRS = ["concept", "knowledge", "docs", "content", "crates"]
EXCLUDE_PARTS = {"archive", "book", "target", ".git", ".kimi", "reports", "tmp", "node_modules"}
REAL_STUB_MAX_LINES = 40
STUB_MARKERS = ["权威来源", "重定向", "已迁移", "归档说明", "stub/archive redirect",
                "superseded", "content moved", "正文已移除", "本文件不再维护"]

TERM_RE = re.compile(r"\*\*([^*]{2,40})\*\*|`([^`]{2,40})`")
HEADER_RE = re.compile(r"^#{1,4}\s+(.+)$", re.MULTILINE)
CN_RE = re.compile(r"[\u4e00-\u9fff]{2,}")
EN_RE = re.compile(r"[a-z][a-z0-9_]{2,}")
STOP_EN = {"the", "and", "for", "with", "from", "this", "that", "are", "you", "your",
           "rust", "note", "see", "use", "used", "using"}


def is_excluded(path):
    parts = set(path.replace("\\", "/").split("/"))
    return bool(parts & EXCLUDE_PARTS)


def is_real_stub(text):
    lines = text.strip().splitlines()
    if len(lines) > REAL_STUB_MAX_LINES:
        return False
    low = text.lower()
    return sum(1 for m in STUB_MARKERS if m.lower() in low) >= 2


def tokenize(text):
    words = set()
    for w in CN_RE.findall(text):
        words.add(w)
    for w in EN_RE.findall(text.lower()):
        if w not in STOP_EN and len(w) > 2:
            words.add(w)
    return words


def extract(path):
    try:
        text = open(path, encoding="utf-8", errors="ignore").read()
    except Exception:
        return None
    title_m = re.search(r"^#\s+(.+)$", text, re.MULTILINE)
    title = title_m.group(1).strip() if title_m else ""
    headers = HEADER_RE.findall(text)
    terms = []
    for a, b in TERM_RE.findall(text):
        terms.append(a or b)
    blob = " ".join([title] + headers + terms)
    kw = tokenize(blob)
    title_kw = tokenize(title)
    return {"title": title, "kw": kw, "title_kw": title_kw,
            "stub": is_real_stub(text), "lines": text.count("\n") + 1}


def jaccard(a, b):
    if not a or not b:
        return 0.0
    inter = len(a & b)
    if inter == 0:
        return 0.0
    return inter / len(a | b)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--threshold", type=float, default=0.5)
    ap.add_argument("--min-shared", type=int, default=5)
    ap.add_argument("--budget", type=int, default=300, help="strict 模式下允许的最大命中对数")
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--same-dir", action="store_true", default=True, help="检测同目录重复（默认开）")
    ap.add_argument("--top", type=int, default=60)
    ap.add_argument("--out-date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    files = []
    for d in SCAN_DIRS:
        base = os.path.join(ROOT, d)
        if not os.path.isdir(base):
            continue
        for dirpath, _, names in os.walk(base):
            for nm in names:
                if not nm.endswith(".md"):
                    continue
                p = os.path.join(dirpath, nm)
                if is_excluded(os.path.relpath(p, ROOT)):
                    continue
                files.append(p)

    data = {}
    for p in files:
        r = extract(p)
        if r is None or r["stub"] or not r["kw"]:
            continue
        data[p] = r

    # 倒排索引：词 -> 文件集合
    inv = defaultdict(set)
    idx = list(data.keys())
    for i, p in enumerate(idx):
        for w in data[p]["kw"]:
            inv[w].add(i)

    # 候选对：共享词数 >= min_shared
    pair_shared = defaultdict(int)
    for w, fs in inv.items():
        fs = list(fs)
        if len(fs) > 200:  # 超高频词（如"概念"）跳过，避免爆炸
            continue
        for a in range(len(fs)):
            for b in range(a + 1, len(fs)):
                pair_shared[(fs[a], fs[b])] += 1

    overlaps = []
    for (i, j), shared in pair_shared.items():
        if shared < args.min_shared:
            continue
        p1, p2 = idx[i], idx[j]
        r1, r2 = data[p1], data[p2]
        kw_sim = jaccard(r1["kw"], r2["kw"])
        if kw_sim < args.threshold * 0.6:  # 关键词太弱直接剪枝
            continue
        title_sim = jaccard(r1["title_kw"], r2["title_kw"]) if (r1["title_kw"] and r2["title_kw"]) else 0.0
        combined = max(kw_sim, title_sim)
        if combined >= args.threshold:
            rel1 = os.path.relpath(p1, ROOT).replace("\\", "/")
            rel2 = os.path.relpath(p2, ROOT).replace("\\", "/")
            same = rel1.split("/")[0] == rel2.split("/")[0]
            overlaps.append({
                "sim": round(combined, 3), "kw_sim": round(kw_sim, 3),
                "title_sim": round(title_sim, 3), "shared": shared,
                "same_dir": same, "f1": rel1, "f2": rel2,
                "t1": r1["title"][:40], "t2": r2["title"][:40],
                "lines1": r1["lines"], "lines2": r2["lines"],
            })

    overlaps.sort(key=lambda x: (-x["sim"], -x["shared"]))

    # 输出
    out_md = os.path.join(ROOT, "reports", f"CONTENT_OVERLAP_V2_{args.out_date}.md")
    out_json = os.path.join(ROOT, "reports", f"CONTENT_OVERLAP_V2_{args.out_date}.json")
    with open(out_json, "w", encoding="utf-8") as f:
        json.dump({"date": args.out_date, "scanned": len(files), "indexed": len(data),
                   "threshold": args.threshold, "min_shared": args.min_shared,
                   "candidates": len(pair_shared), "hits": len(overlaps),
                   "overlaps": overlaps}, f, ensure_ascii=False, indent=2)

    same_dir_hits = sum(1 for o in overlaps if o["same_dir"])
    cross_dir_hits = len(overlaps) - same_dir_hits
    with open(out_md, "w", encoding="utf-8") as f:
        f.write(f"# 内容重叠检测 v2（语义质量门 P0-3）\n\n")
        f.write(f"**日期**: {args.out_date}  **扫描**: {len(files)} 文件（concept/knowledge/docs/content/crates，排除 archive/book/target）\n")
        f.write(f"**纳入索引**: {len(data)}（已剔除真 stub/空关键词）  **候选对(共享>={args.min_shared}词)**: {len(pair_shared)}\n")
        f.write(f"**阈值**: {args.threshold}  **命中对**: {len(overlaps)}（同目录 {same_dir_hits} / 跨目录 {cross_dir_hits}）\n\n")
        f.write("> 本版修正旧版『0 重复』假象：全文关键词（非前50）、纳入 crates、不豁免假 stub、同目录也检、去掉标题 x1.5 主导。\n\n")
        f.write(f"## Top {args.top} 重复对\n\n")
        f.write("| sim | kw | title | 共享词 | 同目录 | 文件1（行） | 文件2（行） |\n")
        f.write("|:---:|:---:|:---:|:---:|:---:|:---|:---|\n")
        for o in overlaps[:args.top]:
            f.write(f"| {o['sim']} | {o['kw_sim']} | {o['title_sim']} | {o['shared']} | "
                    f"{'Y' if o['same_dir'] else 'N'} | `{o['f1']}`({o['lines1']}) | `{o['f2']}`({o['lines2']}) |\n")
        f.write(f"\n## 机器可读\n\n- JSON: `reports/CONTENT_OVERLAP_V2_{args.out_date}.json`\n")

    print(f"[P0-3] scanned={len(files)} indexed={len(data)} candidates={len(pair_shared)} "
          f"hits={len(overlaps)} (same_dir={same_dir_hits} cross_dir={cross_dir_hits}) threshold={args.threshold}")
    print(f"[P0-3] report: {os.path.relpath(out_md, ROOT).replace(chr(92),'/')}")
    for o in overlaps[:8]:
        print(f"   [{o['sim']}] {o['f1']}  <->  {o['f2']}")
    if args.strict and len(overlaps) > args.budget:
        print(f"[P0-3] FAIL: hits {len(overlaps)} > budget {args.budget}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
