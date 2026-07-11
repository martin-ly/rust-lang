#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""crates/*/docs 对齐 concept/ 权威层审计（AGENTS.md §2/§3.4：crates docs 只留 crate 直接内容，通用 Rust 概念解释须链 concept/，不复制）。

只读、不改正文。扫 crates/*/docs/*.md：
  - 是否含指向 concept/ 的相对链接（已对齐权威）
  - 无 concept 链接且 >80 行 且含通用概念关键词（所有权/借用/生命周期/trait/泛型/unsafe/async）的页 → 列为『疑似复述，待人工判断是否应链 concept』（不误判，crate 特定 API/示例含概念词属正常）
输出 reports/CRATES_DOCS_AUTHORITY_ALIGNMENT_<date>.{md,json}。永远 exit 0。
"""
from __future__ import annotations

import datetime as _dt
import glob
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TODAY = _dt.date.today().isoformat()
CONCEPT_LINK = re.compile(r"\.\./|\.\./\.\./|concept/")
GENERIC_KW = re.compile(r"所有权|借用|生命周期|trait|泛型|unsafe|async/await|Send\s*/\s*Sync|Pin| monomorphization", re.IGNORECASE)


def rows():
    out = []
    for p in glob.glob(os.path.join(ROOT, "crates", "*", "docs", "**", "*.md"), recursive=True):
        if "/archive/" in p.replace("\\", "/"):
            continue
        try:
            t = open(p, encoding="utf-8", errors="ignore").read()
        except Exception:
            continue
        lines = t.count("\n") + 1
        has_concept = "concept/" in t
        kw = len(GENERIC_KW.findall(t))
        out.append({"path": os.path.relpath(p, ROOT).replace("\\", "/"), "lines": lines,
                    "has_concept_link": has_concept, "generic_kw_hits": kw,
                    "suspect": (not has_concept) and lines > 80 and kw >= 3})
    return out


def main():
    r = rows()
    n = len(r)
    linked = sum(1 for x in r if x["has_concept_link"])
    suspects = [x for x in r if x["suspect"]]
    suspects.sort(key=lambda x: -x["generic_kw_hits"])
    md = [f"# crates/*/docs 对齐 concept/ 权威层审计（{TODAY}）", "",
          "**EN**: crates docs → concept Authority Alignment",
          "**Summary**: 审计 crates/*/docs 是否按 AGENTS.md §2/§3.4 把通用 Rust 概念解释链接到 concept/ 权威层（不复制）。只读，不改正文。", "",
          f"> 扫描 crates/*/docs md: **{n}** · 含 concept/ 链接: **{linked}** ({round(100*linked/n,1) if n else 0}%) · 疑似复述待人工: **{len(suspects)}**", "",
          "## 口径", "- `has_concept_link` = 正文含 `concept/` 子串（相对链接到权威层）。",
          "- `suspect` = 无 concept 链接 且 >80 行 且 通用概念关键词命中 ≥3（**仅提示**，crate 特定 API/示例/实战含概念词属正常，需人工判断是否真复述通用概念）。", "",
          "## 疑似复述清单（前 60，按关键词命中降序）",
          "| 文件 | 行数 | 概念词命中 |",
          "|:---|---:|---:|"]
    for s in suspects[:60]:
        md.append(f"| `{s['path']}` | {s['lines']} | {s['generic_kw_hits']} |")
    if len(suspects) > 60:
        md.append(f"> … 另有 {len(suspects)-60} 页，见 JSON。")
    if not suspects:
        md.append("✅ 无疑似复述（所有 >80 行且多概念词的 crates docs 已含 concept/ 链接）。")
    md += ["", "## 诚信", "- 本审计只读；`suspect` 是启发式提示，不自动判定违规、不自动改文件。",
           "- crates/*/docs 允许保留 crate 直接相关独特内容（API/示例/构建/实战）；仅当确为『复制通用概念解释』时才需改为链 concept/（AGENTS.md §3.4）。",
           "", "*由 `scripts/check_crates_docs_alignment.py` 生成*"]
    os.makedirs(os.path.join(ROOT, "reports"), exist_ok=True)
    md_path = os.path.join(ROOT, "reports", f"CRATES_DOCS_AUTHORITY_ALIGNMENT_{TODAY}.md")
    json_path = os.path.join(ROOT, "reports", f"CRATES_DOCS_AUTHORITY_ALIGNMENT_{TODAY}.json")
    open(md_path, "w", encoding="utf-8", newline="\n").write("\n".join(md))
    json.dump({"date": TODAY, "scanned": n, "has_concept_link": linked,
               "suspect_count": len(suspects), "suspects": [s["path"] for s in suspects]},
              open(json_path, "w", encoding="utf-8"), ensure_ascii=False, indent=2)
    print(f"[crates-align] scanned={n} linked={linked} ({round(100*linked/n,1) if n else 0}%) suspect={len(suspects)}")
    print(f"[crates-align] report: {os.path.relpath(md_path, ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
