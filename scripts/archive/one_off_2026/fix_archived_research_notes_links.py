#!/usr/bin/env python3
"""
Fix broken links in docs/ that point to files moved into
archive/research_notes_2026_06_06_25/.

Only replaces targets where the original resolved file no longer exists
and the corresponding archived file exists.
"""

import os
import re
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[2]
DOCS_DIR = PROJECT_ROOT / "docs"
ARCHIVE_DIR = PROJECT_ROOT / "archive" / "research_notes_2026_06_25"

LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")


def archived_suffix(target: str) -> str | None:
    """Return the path suffix inside research_notes/ if present."""
    if "research_notes/" in target:
        return target.split("research_notes/", 1)[1]
    return None


def fix_file(md: Path) -> int:
    content = md.read_text(encoding="utf-8")
    new_content = content
    changed = 0
    source_in_research_notes = "research_notes" in md.relative_to(DOCS_DIR).parts

    for match in LINK_RE.finditer(content):
        text, target = match.group(1), match.group(2)
        # Skip URLs, anchors, e-mails, absolute paths
        if re.match(r"^(https?://|mailto:|#|/)", target):
            continue

        # Preserve anchor for the final link, but strip it when looking up archive
        bare_target, anchor = target, ""
        if "#" in bare_target and not bare_target.startswith("#"):
            bare_target, anchor = bare_target.split("#", 1)
            anchor = "#" + anchor

        suffix = archived_suffix(bare_target)
        if not suffix:
            if source_in_research_notes and not bare_target.startswith("../"):
                # Targets like ./10_proof_index.md or formal_methods/00_completeness_gaps.md
                suffix = bare_target.lstrip("./")
            else:
                continue

        original = (md.parent / bare_target).resolve()
        archived = (ARCHIVE_DIR / suffix).resolve()

        if archived.exists() and not original.exists():
            rel = Path(os.path.relpath(archived, md.parent)).as_posix() + anchor
            # Replace only this specific occurrence to avoid collisions
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
    for md in sorted(DOCS_DIR.rglob("*.md")):
        total += fix_file(md)
    print(f"\n总计修复 {total} 处链接")


if __name__ == "__main__":
    main()
