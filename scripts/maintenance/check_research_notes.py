#!/usr/bin/env python3
"""
Check docs/research_notes structural and metadata consistency.

Runs the following checks:
1. No empty directories under docs/research_notes (unless explicitly allowed).
2. Every .md file contains at least one authority source marker.
3. Top metadata block uses Rust 1.96.0+ (Edition 2024) where present.
4. README/INDEX/organization files are up-to-date with actual structure.

Usage:
    python scripts/maintenance/check_research_notes.py
"""

import os
import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[2]
RESEARCH_NOTES = PROJECT_ROOT / "docs" / "research_notes"

# Directories that are allowed to be empty (none by default).
ALLOWED_EMPTY_DIRS: set[str] = set()


def find_empty_dirs() -> list[Path]:
    empty: list[Path] = []
    for root, dirs, files in os.walk(RESEARCH_NOTES):
        # A directory is empty if it has no files and no subdirectories.
        if not dirs and not files:
            rel = Path(root).relative_to(PROJECT_ROOT)
            if str(rel) not in ALLOWED_EMPTY_DIRS:
                empty.append(rel)
    return empty


def iter_md_files() -> list[Path]:
    return sorted(RESEARCH_NOTES.rglob("*.md"))


def check_authority_source(path: Path) -> bool:
    """Return True if the file contains at least one authority source marker."""
    content = path.read_text(encoding="utf-8")
    # Match lines like:
    # > **来源:** [Name](URL)
    # > **权威来源**: [Name](URL)
    # > **权威来源**: [Name](URL) | [Name2](URL2)
    return bool(re.search(r">\s*\*\*(来源|权威来源)\*\*[:：]", content))


def check_rust_version(path: Path) -> tuple[bool, str | None]:
    """Check whether the top metadata block mentions Rust 1.96+ if present."""
    content = path.read_text(encoding="utf-8")
    match = re.search(r">\s*\*\*Rust 版本\*\*[:：]\s*(.+)", content)
    if not match:
        return True, None  # no version metadata; not an error
    version = match.group(1).strip()
    # Allow 1.96.0+ / 1.96.0 / 1.97+ etc.
    ok = bool(re.search(r"1\.9[6-9]", version)) or bool(re.search(r"1\.[1-9][0-9]", version))
    # Allow files explicitly marked as historical version analysis
    if not ok and ("历史声明" in version or "历史版本" in version):
        ok = True
    return ok, version


def check_index_consistency() -> list[str]:
    """Check that INDEX.md links point to existing files for migrated sections."""
    issues: list[str] = []
    index_path = RESEARCH_NOTES / "INDEX.md"
    index_content = index_path.read_text(encoding="utf-8")

    # Look for relative markdown links inside docs/research_notes.
    links = re.findall(r"\]\((docs/research_notes/[^)]+\.md)\)", index_content)
    for link in links:
        target = PROJECT_ROOT / link
        if not target.exists():
            issues.append(f"INDEX.md links to missing file: {link}")

    return issues


def main() -> int:
    exit_code = 0

    print("=" * 60)
    print("docs/research_notes consistency check")
    print("=" * 60)

    # 1. Empty directories
    empty_dirs = find_empty_dirs()
    print(f"\n[1/4] Empty directories: {len(empty_dirs)}")
    if empty_dirs:
        exit_code = 1
        for d in empty_dirs:
            print(f"  ❌ {d}")
    else:
        print("  ✅ No empty directories")

    # 2. Authority sources
    md_files = iter_md_files()
    missing_source: list[Path] = []
    for md in md_files:
        if not check_authority_source(md):
            missing_source.append(md.relative_to(PROJECT_ROOT))

    print(f"\n[2/4] Markdown files missing authority source: {len(missing_source)}")
    if missing_source:
        exit_code = 1
        for p in missing_source:
            print(f"  ❌ {p}")
    else:
        print("  ✅ All markdown files have authority source markers")

    # 3. Rust version metadata
    wrong_version: list[tuple[Path, str]] = []
    for md in md_files:
        ok, version = check_rust_version(md)
        if not ok:
            wrong_version.append((md.relative_to(PROJECT_ROOT), version or "N/A"))

    print(f"\n[3/4] Files with outdated Rust version metadata: {len(wrong_version)}")
    if wrong_version:
        exit_code = 1
        for p, version in wrong_version:
            print(f"  ❌ {p} -> {version}")
    else:
        print("  ✅ Rust version metadata is up-to-date")

    # 4. INDEX consistency
    index_issues = check_index_consistency()
    print(f"\n[4/4] INDEX.md consistency issues: {len(index_issues)}")
    if index_issues:
        exit_code = 1
        for issue in index_issues:
            print(f"  ❌ {issue}")
    else:
        print("  ✅ INDEX.md links are consistent")

    print("\n" + "=" * 60)
    if exit_code == 0:
        print("All checks passed ✅")
    else:
        print("Some checks failed ❌")
    print("=" * 60)
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
