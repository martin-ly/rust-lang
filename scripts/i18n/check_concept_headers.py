#!/usr/bin/env python3
"""Check that all concept/ Markdown files have **EN** and **Summary** headers."""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CONCEPT_DIR = ROOT / "concept"

HEADER_RE = re.compile(r"^>\s*\*\*EN\*\*:\s*(.+)$", re.MULTILINE)
SUMMARY_RE = re.compile(r"^>\s*\*\*Summary\*\*:\s*(.+)$", re.MULTILINE)


def main() -> int:
    files = sorted(p for p in CONCEPT_DIR.rglob("*.md") if "archive" not in p.parts)
    missing_en: list[Path] = []
    missing_summary: list[Path] = []
    short_summary: list[Path] = []
    ok = 0

    for path in files:
        text = path.read_text(encoding="utf-8")
        en = HEADER_RE.search(text)
        summary = SUMMARY_RE.search(text)

        if not en:
            missing_en.append(path)
        if not summary:
            missing_summary.append(path)
        elif len(summary.group(1).split()) < 5:
            short_summary.append(path)

        if en and summary and len(summary.group(1).split()) >= 5:
            ok += 1

    total = len(files)
    print(f"概念文件总数（不含 archive）: {total}")
    print(f"符合 EN + Summary 要求: {ok} ({ok / total * 100:.1f}%)")

    if missing_en:
        print(f"\n缺失 **EN** 头 ({len(missing_en)}):")
        for p in missing_en:
            print(f"  - {p.relative_to(ROOT)}")

    if missing_summary:
        print(f"\n缺失 **Summary** 头 ({len(missing_summary)}):")
        for p in missing_summary:
            print(f"  - {p.relative_to(ROOT)}")

    if short_summary:
        print(f"\nSummary 过短（< 5 词）({len(short_summary)}):")
        for p in short_summary:
            print(f"  - {p.relative_to(ROOT)}")

    return 1 if (missing_en or missing_summary) else 0


if __name__ == "__main__":
    sys.exit(main())
