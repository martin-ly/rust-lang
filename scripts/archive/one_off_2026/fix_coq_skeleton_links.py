#!/usr/bin/env python3
"""
将 docs/research_notes/ 中指向旧 coq_skeleton/ 的链接改为 archive/deprecated/coq_skeleton/。
旧 coq_skeleton/ 目录随后会被删除，因此只处理 docs/research_notes/ 内除 coq_skeleton 本身外的文件。
"""

import os
import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[2]
SOURCE_DIR = PROJECT_ROOT / "docs" / "research_notes"
ARCHIVE_DIR = PROJECT_ROOT / "archive" / "deprecated" / "coq_skeleton"

LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")


def fix_file(md: Path) -> int:
    content = md.read_text(encoding="utf-8")
    new_content = content
    changed = 0

    for match in LINK_RE.finditer(content):
        text, target = match.group(1), match.group(2)
        if re.match(r"^(https?://|mailto:|#|/)", target):
            continue
        if "archive/deprecated/coq_skeleton" in target:
            continue
        if "coq_skeleton" not in target:
            continue

        # Normalize target to suffix inside coq_skeleton/
        suffix = target.split("coq_skeleton/", 1)[1]
        if not suffix or suffix.endswith("/"):
            suffix = "README.md"

        archived = (ARCHIVE_DIR / suffix).resolve()
        original = (md.parent / target).resolve()

        if archived.exists():
            rel = Path(os.path.relpath(archived, md.parent)).as_posix()
            old_link = f"[{text}]({target})"
            new_link = f"[{text}]({rel})"
            new_content = new_content.replace(old_link, new_link, 1)
            changed += 1

    if new_content != content:
        md.write_text(new_content, encoding="utf-8")
        print(f"已修复 {changed} 处链接: {md.relative_to(PROJECT_ROOT)}")
    return changed


def main():
    total = 0
    for md in sorted(SOURCE_DIR.rglob("*.md")):
        if "coq_skeleton" in md.relative_to(SOURCE_DIR).parts:
            continue
        total += fix_file(md)
    print(f"\n总计修复 {total} 处 coq_skeleton 链接")


if __name__ == "__main__":
    main()
