#!/usr/bin/env python3
"""
Check code example anchors in docs/research_notes/.

Scans all Markdown files under docs/12_research_notes/ for relative links that
point to local Rust source files (e.g. `../examples/...`, `../../crates/.../*.rs`,
`../crates/.../*.rs`) and reports links whose targets do not exist.

This check is purely informational: broken code example anchors do not affect
the exit code, because many anchors intentionally reference optional or
future examples.

Usage:
    python scripts/maintenance/check_code_example_anchors.py
"""

import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[2]
RESEARCH_NOTES = PROJECT_ROOT / "docs" / "research_notes"

# Relative link patterns that are considered local code example anchors.
CODE_EXAMPLE_SUFFIXES = (".rs",)


def iter_md_files() -> list[Path]:
    return sorted(RESEARCH_NOTES.rglob("*.md"))


def resolve_link(source_file: Path, link: str) -> Path | None:
    """Resolve a relative Markdown link against the source file's directory.

    Returns None for links that are not relative local paths
    (external URLs, absolute paths, anchor-only links, etc.).
    """
    # Strip optional URL fragment and query string.
    base = link.split("#")[0].split("?")[0]
    if not base:
        return None

    # Skip external, archive, anchor-only, and absolute links.
    if (
        base.startswith("http")
        or base.startswith("mailto:")
        or base.startswith("#")
        or base.startswith("/")
        or "archive/" in base
    ):
        return None

    # Only consider links that end with a Rust source extension.
    if not base.endswith(CODE_EXAMPLE_SUFFIXES):
        return None

    # Resolve relative to the markdown file's directory.
    target = (source_file.parent / base).resolve()
    return target


def check_code_example_anchors() -> list[str]:
    """
    Scan docs/12_research_notes/*.md for relative links to local .rs files.

    Returns a list of broken or missing code example anchors in the form
    "<source.md> -> <link>", sorted.  The result is informational and should
    not affect callers' exit codes.
    """
    issues: list[str] = []
    link_pattern = re.compile(r"!?\[[^\]]*\]\(([^)]+)\)")

    for md in iter_md_files():
        text = md.read_text(encoding="utf-8", errors="ignore")
        rel = md.relative_to(PROJECT_ROOT).as_posix()
        for m in link_pattern.finditer(text):
            link = m.group(1)
            target = resolve_link(md, link)
            if target is None:
                continue
            if not target.exists():
                issues.append(f"{rel} -> {link}")

    return sorted(set(issues))


def main() -> int:
    print("=" * 60)
    print("Code example anchor check (informational)")
    print("=" * 60)

    broken = check_code_example_anchors()
    print(f"\nBroken or missing code example anchors: {len(broken)}")
    if broken:
        for item in broken[:50]:
            print(f"  ⚠️  {item}")
        if len(broken) > 50:
            print(f"  ... and {len(broken) - 50} more")
    else:
        print("  ✅ All referenced code example files exist")

    print("\n" + "=" * 60)
    print("Code example anchor check complete (informational)")
    print("=" * 60)
    return 0


if __name__ == "__main__":
    sys.exit(main())
