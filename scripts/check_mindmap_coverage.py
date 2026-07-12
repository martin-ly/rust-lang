#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""W2-a 思维表征观察：内容页 mindmap 覆盖率与反例节存在率。

背景：2026-07-12 思维表征审计发现：全库 mermaid 覆盖约 50%，但 99% 为
flowchart/graph；真正的 `mindmap` 图在 L1–L7 内容层仅 14 页。五件套
（定义-属性-关系-示例-反例）中「反例」最弱（06 层 13%、07 层 11%）。
本脚本将两个指标纳入持续观察（语义观察门，默认 exit 0）。

检查口径（只读 concept/，排除 00_meta/、README.md、重定向 stub）：
    M1 mindmap 覆盖率：内容页中包含 ```mermaid 真 `mindmap` 图（非 graph/flowchart）的比例。
       分层（01_foundation … 07_future）与全库汇总。
    M2 反例节存在率：内容页中包含「反例」字样的章节标题或 `compile_fail` 代码块的比例。

用法：
    python scripts/check_mindmap_coverage.py            # 默认观察，exit 0
    python scripts/check_mindmap_coverage.py --strict   # 低于基线阈值时 exit 1
    python scripts/check_mindmap_coverage.py --path concept/06_ecosystem

基线（2026-07-12 W2-a 后实跑）：见脚本常量 BASELINE。
"""
from __future__ import annotations

import argparse
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

MERMAID_BLOCK_RE = re.compile(r"```mermaid\s*\n(.*?)```", re.S)
MINDMAP_RE = re.compile(r"^\s*mindmap\s*$", re.M)
COUNTEREXAMPLE_HEADING_RE = re.compile(r"^#{1,6}.*反例", re.M)
COMPILE_FAIL_RE = re.compile(r"```rust[,\w ]*compile_fail")

# --strict 阈值（2026-07-12 W2-a 基线，留 1% 容差）
BASELINE = {"mindmap": 0.10, "counterexample": 0.40}

LAYERS = [
    "01_foundation", "02_intermediate", "03_advanced", "04_formal",
    "05_comparative", "06_ecosystem", "07_future",
]


def is_stub(text: str) -> bool:
    lines = text.splitlines()
    if len(lines) > 40:
        return False
    return "重定向" in text or ("权威来源" in text and "stub" in text.lower())


def has_mindmap(text: str) -> bool:
    for m in MERMAID_BLOCK_RE.finditer(text):
        if MINDMAP_RE.search(m.group(1)):
            return True
    return False


def has_counterexample(text: str) -> bool:
    return bool(COUNTEREXAMPLE_HEADING_RE.search(text) or COMPILE_FAIL_RE.search(text))


def scan(base: str):
    stats: dict[str, dict[str, int]] = {}
    for root, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if d != "archive"]
        if os.sep + "00_meta" in root or root.endswith(os.sep + "00_meta"):
            continue
        rel_root = os.path.relpath(root, base)
        layer = rel_root.split(os.sep)[0]
        if layer not in LAYERS:
            layer = "_other"
        bucket = stats.setdefault(layer, {"pages": 0, "mindmap": 0, "counter": 0})
        for f in sorted(files):
            if not f.endswith(".md") or f == "README.md":
                continue
            path = os.path.join(root, f)
            try:
                text = open(path, encoding="utf-8").read()
            except (UnicodeDecodeError, OSError):
                continue
            if is_stub(text):
                continue
            bucket["pages"] += 1
            if has_mindmap(text):
                bucket["mindmap"] += 1
            if has_counterexample(text):
                bucket["counter"] += 1
    return stats


def pct(part: int, total: int) -> float:
    return part / total if total else 0.0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--strict", action="store_true",
                    help="低于 BASELINE 阈值时 exit 1")
    ap.add_argument("--path", default=os.path.join("concept"),
                    help="扫描根目录（默认 concept/）")
    args = ap.parse_args()

    base = os.path.join(ROOT, args.path) if not os.path.isabs(args.path) else args.path
    stats = scan(base)

    total_pages = total_mm = total_ce = 0
    print("== 内容页思维表征覆盖率（W2-a 观察门，默认 exit 0）==")
    print(f"{'层':<16}{'内容页':>7}{'mindmap':>16}{'反例存在':>16}")
    for layer in LAYERS + ["_other"]:
        b = stats.get(layer)
        if not b or b["pages"] == 0:
            continue
        mm_rate = pct(b["mindmap"], b["pages"])
        ce_rate = pct(b["counter"], b["pages"])
        print(f"{layer:<16}{b['pages']:>7}"
              f"{b['mindmap']:>8} ({mm_rate:6.1%})"
              f"{b['counter']:>8} ({ce_rate:6.1%})")
        total_pages += b["pages"]
        total_mm += b["mindmap"]
        total_ce += b["counter"]

    mm_all = pct(total_mm, total_pages)
    ce_all = pct(total_ce, total_pages)
    print("-" * 55)
    print(f"{'TOTAL':<16}{total_pages:>7}"
          f"{total_mm:>8} ({mm_all:6.1%})"
          f"{total_ce:>8} ({ce_all:6.1%})")
    print(f"基线阈值（--strict）: mindmap >= {BASELINE['mindmap']:.0%}, "
          f"反例 >= {BASELINE['counterexample']:.0%}")

    if args.strict and (mm_all < BASELINE["mindmap"] or ce_all < BASELINE["counterexample"]):
        print("STRICT: 覆盖率低于基线", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
