#!/usr/bin/env python3
"""
Bulk-add a generic P1 academic-authority reference section to
``docs/research_notes/`` alignment sub-documents.

Scope:
- Files whose concept family (概念族) starts with ``权威来源对齐``.
- Hub / meta documents about the alignment network itself are skipped.
- Files that already contain any P1 academic URL are skipped (idempotent).

P1 academic domains are taken from ``check_authoritative_source_gaps.py``.

Usage:
    python scripts/maintenance/bulk_add_p1_to_alignment_docs.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[2]
RESEARCH_NOTES = PROJECT_ROOT / "docs" / "research_notes"

# Same P1 domain list as check_authoritative_source_gaps.py.
P1_DOMAINS = [
    r"plv\.mpi-sws\.org",
    r"arxiv\.org",
    r"acm\.org",
    r"dl\.acm\.org",
    r"ieee\.org",
    r"springer\.com",
    r"link\.springer\.com",
    r"plf\.inf\.ethz\.ch",
    r"aeneas-verification\.github\.io",
    r"aeneas-verif\.org",
]

CONCEPT_FAMILY_RE = re.compile(r">\s*\*\*概念族\*\*[:：]\s*(.+)")
LINK_RE = re.compile(r"!?\[[^\]]*\]\(([^)]+)\)")

# Hub / meta documents that organize the alignment network itself.
# These are intentionally left untouched.
HUB_FILENAMES = {
    "10_authoritative_source_alignment_network.md",
    "10_authoritative_alignment_guide.md",
    "10_authoritative_alignment_status.md",
    "10_authoritative_alignment_gap_matrix.md",
    "10_authoritative_content_alignment_report.md",
    "10_authoritative_source_gap_and_backref_index.md",
    "10_authoritative_source_line_anchors.md",
    "10_authoritative_source_version_tracking.md",
    "10_authoritative_alignment_gap_analysis.md",
}

P1_SECTION_HEADER = "## 学术权威参考"

P1_SECTION_BODY = """\
本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)
"""


def iter_md_files() -> list[Path]:
    return sorted(RESEARCH_NOTES.rglob("*.md"))


def extract_concept_family(content: str) -> str | None:
    match = CONCEPT_FAMILY_RE.search(content)
    if not match:
        return None
    family = match.group(1).strip()
    family = re.sub(r"[\|\[\]\(\)\*]+$", "", family).strip()
    return family or None


def extract_urls(content: str) -> set[str]:
    urls: set[str] = set()
    for m in LINK_RE.finditer(content):
        link = m.group(1)
        if link.startswith("http"):
            urls.add(link.split("#")[0].split("?")[0])
    return urls


def has_p1_url(content: str) -> bool:
    urls = extract_urls(content)
    if not urls:
        return False
    text = " ".join(urls)
    return any(re.search(domain, text) for domain in P1_DOMAINS)


def append_p1_section(path: Path) -> None:
    content = path.read_text(encoding="utf-8", errors="ignore")

    # Defensive idempotency: skip if the section header already exists.
    if P1_SECTION_HEADER in content:
        return

    # Ensure the file ends with a blank line before appending.
    separator = "\n\n---\n\n" if content.rstrip() else "---\n\n"
    new_content = content.rstrip() + separator + P1_SECTION_HEADER + "\n\n" + P1_SECTION_BODY
    path.write_text(new_content, encoding="utf-8")


def main() -> int:
    files = iter_md_files()

    total = 0
    skipped_hub = 0
    skipped_has_p1 = 0
    skipped_wrong_family = 0
    modified: list[Path] = []

    for f in files:
        content = f.read_text(encoding="utf-8", errors="ignore")
        family = extract_concept_family(content)

        if family is None or not family.startswith("权威来源对齐"):
            skipped_wrong_family += 1
            continue

        total += 1

        if f.name in HUB_FILENAMES:
            skipped_hub += 1
            continue

        if has_p1_url(content):
            skipped_has_p1 += 1
            continue

        append_p1_section(f)
        modified.append(f)

    print("=" * 60)
    print("Bulk P1 academic authority addition for alignment docs")
    print("=" * 60)
    print(f"Total docs/research_notes .md files scanned: {len(files)}")
    print(f"Files in '权威来源对齐' family: {total}")
    print(f"  Skipped (hub documents): {skipped_hub}")
    print(f"  Skipped (already have P1 URL): {skipped_has_p1}")
    print(f"  Modified: {len(modified)}")
    print("-" * 60)
    if modified:
        for f in modified:
            print(f"  + {f.relative_to(PROJECT_ROOT).as_posix()}")
    print("=" * 60)

    return 0


if __name__ == "__main__":
    sys.exit(main())
