#!/usr/bin/env python3
"""检查 Markdown 文件中 Mermaid 图的关键语法问题。

本脚本做保守检查，重点发现：
- 未闭合的 mermaid 代码块
- 未闭合的 subgraph

对于跨多行的节点标签中的括号不平衡，由于 Mermaid 本身支持多行标签，
本脚本暂不将其视为错误（避免大量误报）。
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCAN_DIRS = [ROOT / "concept", ROOT / "knowledge", ROOT / "docs", ROOT / "content"]

MERMAID_START = re.compile(r"^\s*```\s*mermaid\b", re.MULTILINE)
MERMAID_END = re.compile(r"^\s*```\s*$", re.MULTILINE)
SUBGRAPH_START = re.compile(r"^\s*subgraph\b", re.IGNORECASE | re.MULTILINE)
SUBGRAPH_END = re.compile(r"^\s*end\b", re.MULTILINE)


def check_file(path: Path) -> list[str]:
    errors: list[str] = []
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()

    in_mermaid = False
    mermaid_start_line = 0
    subgraph_depth = 0

    for i, raw_line in enumerate(lines, start=1):
        line = raw_line.rstrip()

        if re.match(MERMAID_START.pattern, line, re.IGNORECASE):
            in_mermaid = True
            mermaid_start_line = i
            subgraph_depth = 0
            continue

        if re.match(MERMAID_END.pattern, line):
            if in_mermaid:
                if subgraph_depth != 0:
                    errors.append(
                        f"{path}:{mermaid_start_line}: subgraph not closed (depth {subgraph_depth})"
                    )
                in_mermaid = False
                subgraph_depth = 0
            continue

        if not in_mermaid:
            continue

        if re.match(SUBGRAPH_START.pattern, line):
            subgraph_depth += 1
        elif re.match(SUBGRAPH_END.pattern, line):
            subgraph_depth = max(0, subgraph_depth - 1)

    if in_mermaid:
        errors.append(f"{path}:{mermaid_start_line}: mermaid block not closed")

    return errors


def main() -> int:
    all_errors: list[str] = []
    files = 0
    blocks = 0

    for d in SCAN_DIRS:
        if not d.exists():
            continue
        for path in d.rglob("*.md"):
            files += 1
            errs = check_file(path)
            if errs:
                all_errors.extend(errs)
            text = path.read_text(encoding="utf-8")
            blocks += len(MERMAID_START.findall(text))

    print(f"Scanned {files} markdown files, found {blocks} mermaid blocks.")

    if all_errors:
        print(f"\nFound {len(all_errors)} critical syntax issues:")
        for e in all_errors[:50]:
            print(f"  - {e}")
        if len(all_errors) > 50:
            print(f"  ... and {len(all_errors) - 50} more")
        return 1

    print("✅ No critical Mermaid syntax issues found.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
