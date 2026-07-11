#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""D3 字段重声明去重（P0-1 metadata consistency）。

规则：concept/ 活跃 md 文首 `>` 元数据块内，`> **字段名**:` 若重复出现，删除后续重复行
（保留第一次声明）。若同一字段后续出现**不同内容**，不删除，记录冲突待人工复核。
只改文首元数据块，不动正文。--dry-run 预览。
"""
from __future__ import annotations

import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
CONCEPT = os.path.join(ROOT, "concept")
DRY = "--dry-run" in sys.argv

FIELD_RE = re.compile(r"^>\s*\*\*([^*]+)\*\*\s*[:：]")


def find_metadata_block(lines):
    """找到 # 标题后的连续 `>` 元数据块（含空行）。返回 (start_idx, end_idx_exclusive)。"""
    # 找第一个 # 标题
    title_idx = None
    for i, line in enumerate(lines):
        if line.startswith("# "):
            title_idx = i
            break
    if title_idx is None:
        return None
    # 从标题下一行开始，找连续 `>` 行（允许中间有空行但空行属于块）
    start = title_idx + 1
    end = start
    while end < len(lines):
        stripped = lines[end].rstrip()
        if stripped == "":
            end += 1
            continue
        if stripped.startswith(">"):
            end += 1
        else:
            break
    return (start, end) if end > start else None


def process_file(path):
    try:
        text = open(path, encoding="utf-8", errors="ignore").read()
    except Exception:
        return None
    lines = text.splitlines()
    block = find_metadata_block(lines)
    if block is None:
        return None
    start, end = block
    seen = {}  # field -> first content after colon (strip)
    remove_indices = set()
    conflicts = []
    for i in range(start, end):
        line = lines[i]
        m = FIELD_RE.match(line)
        if not m:
            continue
        field = m.group(1).strip()
        content = line.split(":", 1)[-1].split("：", 1)[-1].strip()
        if field not in seen:
            seen[field] = content
        else:
            if seen[field] != content:
                # 内容不同：可能是补充信息或冲突，保留并记录待人工复核
                conflicts.append((field, seen[field], content))
            else:
                # 内容完全相同的重声明：删除
                remove_indices.add(i)
    if not remove_indices:
        return None
    new_lines = [l for idx, l in enumerate(lines) if idx not in remove_indices]
    return {"removed": len(remove_indices), "conflicts": conflicts,
            "removed_fields": sorted(set(lines[i].split(":", 1)[0].strip("> *") for i in remove_indices)),
            "new_text": "\n".join(new_lines) + ("" if text.endswith("\n") else "")}


def main():
    files = glob.glob(os.path.join(CONCEPT, "**", "*.md"), recursive=True)
    changed = 0
    total_removed = 0
    conflict_report = []
    for p in files:
        if "/archive/" in p.replace("\\", "/"):
            continue
        res = process_file(p)
        if not res:
            continue
        rel = os.path.relpath(p, ROOT).replace("\\", "/")
        changed += 1
        total_removed += res["removed"]
        print(f"  {'DRY ' if DRY else ''}{rel}: -{res['removed']} lines, conflicts={len(res['conflicts'])}")
        if res["conflicts"]:
            conflict_report.append((rel, res["conflicts"]))
        if not DRY:
            open(p, "w", encoding="utf-8", newline="\n").write(res["new_text"])
    print(f"[fix-d3] files_changed={changed} lines_removed={total_removed} dry={DRY}")
    if conflict_report:
        print("[fix-d3] content conflicts (kept first, needs review):")
        for rel, cfs in conflict_report[:20]:
            for f, first, later in cfs:
                print(f"   {rel}: {f!r} first={first!r} later={later!r}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
