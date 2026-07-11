#!/usr/bin/env python3
"""
Bulk append P1/P2 authoritative source reference sections to docs/research_notes
files based on their concept family (概念族).

This script is idempotent: files that already contain a section titled
"权威来源参考" or "学术/社区来源参考" are skipped.

Usage:
    python scripts/maintenance/bulk_add_p1p2_by_family.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[2]
RESEARCH_NOTES = PROJECT_ROOT / "docs" / "research_notes"

CONCEPT_FAMILY_RE = re.compile(r">\s*\*\*概念族\*\*[:：]\s*(.+)")
EXISTING_SECTION_RE = re.compile(r"^##\s*(权威来源参考|学术/社区来源参考)", re.MULTILINE | re.IGNORECASE)

# Hub documents that should not be modified.
HUB_PATHS = {
    RESEARCH_NOTES / "README.md",
    RESEARCH_NOTES / "INDEX.md",
}

# P1/P2 source pools grouped by concept family prefix or exact name.
FAMILY_SOURCES: dict[str, list[tuple[str, str]]] = {
    "形式化模块": [
        ("RustBelt", "https://plv.mpi-sws.org/rustbelt/"),
        ("Aeneas", "https://aeneas-verification.github.io/"),
        ("Rust Design Patterns", "https://rust-unofficial.github.io/patterns/"),
    ],
    "形式化方法 / 宏系统": [
        ("The Little Book of Rust Macros", "https://veykril.github.io/tlborm/"),
        ("Rust Reference – Macros", "https://doc.rust-lang.org/reference/macros.html"),
        ("proc-macro-workshop", "https://github.com/dtolnay/proc-macro-workshop"),
    ],
    "形式化方法 / 证明助手": [
        ("Aeneas", "https://aeneas-verification.github.io/"),
        ("coq-of-rust", "https://github.com/formal-land/coq-of-rust"),
    ],
    "形式化方法总览": [
        ("RustBelt", "https://plv.mpi-sws.org/rustbelt/"),
        ("Aeneas", "https://aeneas-verification.github.io/"),
        ("Rust Design Patterns", "https://rust-unofficial.github.io/patterns/"),
    ],
    "软件设计 / Crate 架构": [
        ("Rust API Guidelines", "https://rust-lang.github.io/api-guidelines/"),
        ("Rust Design Patterns", "https://rust-unofficial.github.io/patterns/"),
        ("This Week in Rust", "https://this-week-in-rust.org/"),
    ],
    "类型系统 / Trait / 反例边界": [
        ("Oxide", "https://arxiv.org/abs/1903.00982"),
        ("RustSEM", "https://link.springer.com/article/10.1007/s10703-024-00460-3"),
        ("Rust Design Patterns", "https://rust-unofficial.github.io/patterns/"),
    ],
    "类型系统 / 基础": [
        ("Oxide", "https://arxiv.org/abs/1903.00982"),
        ("RustSEM", "https://link.springer.com/article/10.1007/s10703-024-00460-3"),
        ("Rust Design Patterns", "https://rust-unofficial.github.io/patterns/"),
    ],
    "类型系统 / 高级类型": [
        ("Oxide", "https://arxiv.org/abs/1903.00982"),
        ("RustSEM", "https://link.springer.com/article/10.1007/s10703-024-00460-3"),
        ("Rust Design Patterns", "https://rust-unofficial.github.io/patterns/"),
    ],
    "运维 / 链接审计": [
        ("Rust Official Docs", "https://doc.rust-lang.org/"),
        ("This Week in Rust", "https://this-week-in-rust.org/"),
    ],
}


def iter_md_files() -> list[Path]:
    return sorted(RESEARCH_NOTES.rglob("*.md"))


def extract_concept_family(content: str) -> str | None:
    match = CONCEPT_FAMILY_RE.search(content)
    if not match:
        return None
    family = match.group(1).strip()
    family = re.sub(r"[\|\[\]\(\)\*]+$", "", family).strip()
    return family or None


def resolve_family_group(family: str) -> str | None:
    """Map a concept family to one of the configured source pools."""
    if family in FAMILY_SOURCES:
        return family
    # Prefix match for families like "形式化模块 / 代码实践".
    for key in FAMILY_SOURCES:
        if family.startswith(key + " /"):
            return key
    return None


def build_section(title: str, links: list[tuple[str, str]]) -> str:
    lines = ["", "---", "", f"## {title}", ""]
    for name, url in links:
        lines.append(f"> **来源**: [{name}]({url})")
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    modified = 0
    skipped_existing = 0
    skipped_hub = 0

    for path in iter_md_files():
        if path in HUB_PATHS:
            skipped_hub += 1
            continue

        content = path.read_text(encoding="utf-8", errors="ignore")
        family = extract_concept_family(content)
        if family is None:
            continue

        group = resolve_family_group(family)
        if group is None:
            continue

        if EXISTING_SECTION_RE.search(content):
            skipped_existing += 1
            continue

        title = "学术/社区来源参考" if group.startswith("形式化") else "权威来源参考"
        section = build_section(title, FAMILY_SOURCES[group])

        # Ensure the file ends with a newline before appending.
        if not content.endswith("\n"):
            content += "\n"
        # Avoid a redundant separator if the file already ends with one.
        if content.rstrip().endswith("---"):
            section = section.lstrip("\n").lstrip("-").lstrip("\n")
            # section is now "\n## ..."; prepend a single newline.
            section = "\n" + section
        content += section

        path.write_text(content, encoding="utf-8")
        modified += 1
        print(f"✅ {path.relative_to(PROJECT_ROOT).as_posix()}")

    print(f"\nModified: {modified}, skipped (existing section): {skipped_existing}, skipped (hub): {skipped_hub}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
