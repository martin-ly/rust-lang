#!/usr/bin/env python3
"""批量补齐 concept/ 非 L0 文件的受众与内容分级双标签。

规则：
- 00_meta 视为 L0，不参与补齐（调用方应确保 kb_auditor 也不计入）。
- 仅处理 01_foundation-07_future 下的 .md 文件。
- 已有标签则保留；缺失则根据层级推断默认值。
- 默认映射：
  L1 -> 受众=[初学者], 内容分级=[综述级]
  L2 -> 受众=[进阶],   内容分级=[参考级]
  L3 -> 受众=[专家],   内容分级=[专家级]
  L4/L5/L6/L7 -> 受众=[研究者], 内容分级=[研究级]
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

CONCEPT_DIR = Path("concept")
EXCLUDE_DIRS = {"archive", "deprecated", "sources"}

# 目录名 -> 层级
LAYER_MAP = {
    "01_foundation": "L1",
    "02_intermediate": "L2",
    "03_advanced": "L3",
    "04_formal": "L4",
    "05_comparative": "L5",
    "06_ecosystem": "L6",
    "07_future": "L7",
}

DEFAULTS = {
    "L1": ("初学者", "综述级"),
    "L2": ("进阶", "参考级"),
    "L3": ("专家", "专家级"),
    "L4": ("研究者", "研究级"),
    "L5": ("研究者", "研究级"),
    "L6": ("研究者", "研究级"),
    "L7": ("研究者", "研究级"),
}

AUDIENCE_RE = re.compile(r">\s*\*\*受众\*\*[:：]\s*\[([^\]]+)\](?:\s*/\s*\[([^\]]+)\])?")
LEVEL_RE = re.compile(r">\s*\*\*内容分级\*\*[:：]\s*\[([^\]]+)\]")


def layer_from_dir(path: Path) -> str | None:
    rel = path.relative_to(CONCEPT_DIR)
    first = rel.parts[0] if rel.parts else ""
    return LAYER_MAP.get(first)


def normalize_existing_level(content: str) -> str:
    """将 > **内容分级**:\n>\n> [X] 或 > **内容分级**:\n> [X] 的多行形式合并为单行。"""
    pattern = re.compile(r">\s*\*\*内容分级\*\*[:：]\s*\n(?:>\s*\n)?>\s*\[([^\]]+)\]", re.MULTILINE)
    return pattern.sub(lambda m: f"> **内容分级**: [{m.group(1).strip()}]", content)


def fix_file(path: Path, layer: str, dry_run: bool) -> list[str]:
    changes: list[str] = []
    original_content = path.read_text(encoding="utf-8")
    content = normalize_existing_level(original_content)
    normalized = content != original_content

    default_audience, default_level = DEFAULTS[layer]

    audience_match = AUDIENCE_RE.search(content)
    level_match = LEVEL_RE.search(content)

    new_lines: list[str] = []

    if not audience_match:
        new_lines.append(f"> **受众**: [{default_audience}]")
        changes.append(f"add audience [{default_audience}]")

    if not level_match:
        new_lines.append(f"> **内容分级**: [{default_level}]")
        changes.append(f"add content level [{default_level}]")

    if not new_lines and not normalized:
        return []

    if normalized:
        changes.append("normalize content level format")

    if dry_run:
        return changes

    # 在文件最开头插入缺失的元数据行，避免破坏标题后的结构化摘要
    if new_lines:
        content = "\n".join(new_lines) + "\n" + content
    path.write_text(content, encoding="utf-8")
    return changes


def main() -> int:
    dry_run = "--dry-run" in sys.argv
    total = 0
    for path in sorted(CONCEPT_DIR.rglob("*.md")):
        if any(part in EXCLUDE_DIRS for part in path.relative_to(CONCEPT_DIR).parts):
            continue
        layer = layer_from_dir(path)
        if not layer:
            continue
        changes = fix_file(path, layer, dry_run)
        if changes:
            total += 1
            print(f"{path}: {', '.join(changes)}")
    print(f"\n{'[dry-run] ' if dry_run else ''}Updated {total} files.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
