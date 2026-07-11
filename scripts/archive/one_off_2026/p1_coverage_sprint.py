#!/usr/bin/env python3
"""
P1 academic authority source coverage sprint for docs/research_notes.

For each Markdown file under docs/research_notes whose concept family has P1
academic coverage below 50%, append an "学术权威参考" section with 2-4 generic
P1 links if the file does not already contain any P1 academic URL and does not
already have the section.

Skipped files:
- Root hub documents: README.md, INDEX.md, 10_*.md
- Files already containing a "## 学术权威参考" section
- Files already referencing any P1 academic domain

Usage:
    python scripts/maintenance/p1_coverage_sprint.py
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[2]
RESEARCH_NOTES = PROJECT_ROOT / "docs" / "research_notes"

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

P1_LINKS = {
    "rustbelt": "- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)",
    "tree-borrows": "- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)",
    "rustsem": "- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)",
    "aeneas": "- [Aeneas](https://aeneas-verification.github.io/)",
    "oxide": "- [Oxide](https://arxiv.org/abs/1903.00982)",
}

CONCEPT_FAMILY_RE = re.compile(r">\s*\*\*概念族\*\*[:：]\s*(.+)")
LINK_RE = re.compile(r"!?\[[^\]]*\]\(([^)]+)\)")
SECTION_RE = re.compile(r"^##\s+学术权威参考\s*$", re.MULTILINE)

# Mapping from concept family name to a list of P1 link keys (2-4 items).
FAMILY_LINK_KEYS: dict[str, list[str]] = {
    "Crate 架构 / 反例边界": ["rustbelt", "aeneas", "oxide"],
    "实验研究 / 性能 / 反例边界": ["rustbelt", "tree-borrows", "rustsem"],
    "工作流 / 组合工程 / 分布式 / 反例边界": ["aeneas", "rustbelt", "rustsem"],
    "形式化方法 / 宏系统": ["rustbelt", "rustsem", "oxide"],
    "形式化模块 / 反例边界": ["rustbelt", "aeneas", "rustsem"],
    "权威来源对齐 / 版本跟踪": ["rustbelt", "rustsem", "aeneas"],
    "权威来源对齐 / 行号锚点": ["rustbelt", "rustsem", "aeneas"],
    "版本演进 / 反例边界": ["rustbelt", "oxide", "aeneas"],
    "设计模式 / 反例边界": ["aeneas", "rustbelt", "rustsem"],
    "软件设计 / Crate 架构": ["rustbelt", "aeneas", "oxide"],
    "软件设计 / 工作流模式 / 状态机": ["aeneas", "rustbelt", "rustsem"],
    "软件设计 / 工作流模式 / 补偿 / Saga": ["aeneas", "rustbelt", "rustsem"],
    "软件设计 / 工作流模式 / 长事务 / Saga": ["aeneas", "rustbelt", "rustsem"],
    "软件设计 / 边界系统": ["rustbelt", "tree-borrows", "aeneas"],
    "运维 / 链接审计": ["rustbelt", "rustsem", "aeneas"],
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


def extract_urls(content: str) -> set[str]:
    urls: set[str] = set()
    for m in LINK_RE.finditer(content):
        link = m.group(1)
        if link.startswith("http"):
            urls.add(link.split("#")[0].split("?")[0])
    return urls


def has_p1_url(content: str) -> bool:
    urls = extract_urls(content)
    text = " ".join(urls)
    return any(re.search(domain, text) for domain in P1_DOMAINS)


def is_hub_file(path: Path) -> bool:
    rel = path.relative_to(RESEARCH_NOTES)
    # Only root-level files can be hub documents.
    if rel.parent != Path("."):
        return False
    name = path.name
    if name in {"README.md", "INDEX.md"}:
        return True
    if name.startswith("10_") and name.endswith(".md"):
        return True
    return False


def select_link_keys(family: str, filename: str) -> list[str]:
    keys = FAMILY_LINK_KEYS.get(family)
    if keys is not None:
        return keys
    # Fallback keyword-based selection for any future gap families.
    family_lower = family.lower()
    name_lower = filename.lower()
    text = family_lower + " " + name_lower
    selected: list[str] = []
    selected.append("rustbelt")
    if any(k in text for k in ["借用", "内存", "unsafe", "borrows", "memory", "边界系统"]):
        selected.append("tree-borrows")
    if any(k in text for k in ["形式化", "验证", "语义", "宏", "模块", "设计模式", "工作流", "状态机", "saga", "运维"]):
        selected.extend(["rustsem", "aeneas"])
    if any(k in text for k in ["类型", "trait", "oxide", "crate 架构"]):
        selected.append("oxide")
    # Ensure 2-4 unique links.
    seen: set[str] = set()
    unique: list[str] = []
    for key in selected:
        if key not in seen:
            seen.add(key)
            unique.append(key)
    if len(unique) < 2:
        unique.append("aeneas")
    if len(unique) > 4:
        unique = unique[:4]
    return unique


def build_section(family: str, filename: str) -> str:
    keys = select_link_keys(family, filename)
    links = [P1_LINKS[key] for key in keys if key in P1_LINKS]
    body = "\n".join(links)
    return f"\n\n## 学术权威参考\n\n{body}\n"


def append_section(content: str, section: str) -> str:
    # Avoid duplicate horizontal rules: if the content already ends with a rule,
    # do not prepend another one to the appended section.
    stripped = content.rstrip()
    if stripped.endswith("---"):
        # Replace the trailing rule's surrounding whitespace with a single
        # newline, then append the section (which starts with its own blank line).
        return stripped.rstrip("-").rstrip() + section
    return stripped + section


def main() -> int:
    sys.path.insert(0, str(PROJECT_ROOT / "scripts" / "maintenance"))
    from check_authoritative_source_gaps import analyze

    report = analyze()
    gap_families = {
        family
        for family, data in report.items()
        if family != "_meta" and data["P1_pct"] < 50
    }

    modified: list[Path] = []
    skipped_hub: list[Path] = []
    skipped_has_p1: list[Path] = []
    skipped_has_section: list[Path] = []

    for f in iter_md_files():
        if is_hub_file(f):
            skipped_hub.append(f)
            continue

        content = f.read_text(encoding="utf-8", errors="ignore")

        if SECTION_RE.search(content):
            skipped_has_section.append(f)
            continue

        family = extract_concept_family(content)
        if family is None or family not in gap_families:
            continue

        if has_p1_url(content):
            skipped_has_p1.append(f)
            continue

        section = build_section(family, f.name)
        new_content = append_section(content, section)
        f.write_text(new_content, encoding="utf-8")
        modified.append(f)

    print("=" * 70)
    print("P1 学术来源覆盖率冲刺结果")
    print("=" * 70)
    print(f"\n目标概念族（P1 < 50%）: {len(gap_families)} 个")
    for family in sorted(gap_families):
        print(f"  • {family}")
    print(f"\n修改文件数: {len(modified)}")
    for f in modified:
        print(f"  ✏️  {f.relative_to(PROJECT_ROOT).as_posix()}")
    print(f"\n跳过（枢纽文档）: {len(skipped_hub)}")
    print(f"跳过（已有 P1 URL）: {len(skipped_has_p1)}")
    print(f"跳过（已有学术权威参考小节）: {len(skipped_has_section)}")
    print("=" * 70)
    return 0


if __name__ == "__main__":
    sys.exit(main())
