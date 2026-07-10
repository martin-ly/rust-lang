#!/usr/bin/env python3
"""Check that concept/ **EN** titles are specific and match file topics.

This script does NOT enforce a 1:1 mapping between file titles and glossary
entries, because many concept files cover broader or more specific topics than
a single glossary term. Instead it flags:

1. Files whose **EN** title is a known generic fallback (e.g. "Formal Methods",
   "Type System", "Compiler Internals") that does not reflect the H1 title.
   A generic EN is accepted when the H1 explicitly contains that term.
2. Files whose H1 exactly matches a glossary term but whose **EN** title differs.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
CONCEPT_DIR = ROOT / "concept"
GLOSSARY_PATH = CONCEPT_DIR / "00_meta" / "01_terminology" / "terminology_glossary.md"

EN_RE = re.compile(r"^>\s*\*\*EN\*\*:\s*(.+)$", re.MULTILINE)
GLOSS_RE = re.compile(r"-\s*\*\*([^*]+)\*\*\s*\(([^)]+)\)")

# Generic EN titles that are acceptable only when the H1 explicitly contains
# the corresponding concept.
GENERIC_FALLBACKS = {
    "Formal Methods": {"formal methods", "形式化方法", "形式化"},
    "Type System": {"type system", "类型系统"},
    "Compiler Internals": {"compiler", "编译器"},
    "Design Patterns": {"design patterns", "设计模式", "patterns"},
    "Rust": {"rust"},
    "Programming": {"programming", "编程"},
}


def load_glossary() -> dict[str, str]:
    text = GLOSSARY_PATH.read_text(encoding="utf-8")
    terms: dict[str, str] = {}
    for cn, en in GLOSS_RE.findall(text):
        cn = cn.strip()
        en = en.strip()
        terms[cn] = en
    return terms


def normalize(title: str) -> str:
    return " ".join(title.strip().lower().split())


def h1_covers_generic(h1: str, generic_en: str) -> bool:
    h1_lower = h1.lower()
    for token in GENERIC_FALLBACKS.get(generic_en, set()):
        if token in h1_lower:
            return True
    return False


def main() -> int:
    glossary = load_glossary()
    files = sorted(p for p in CONCEPT_DIR.rglob("*.md") if "archive" not in p.parts)

    generic_mismatches: list[tuple[Path, str, str]] = []
    exact_mismatches: list[tuple[Path, str, str, str]] = []
    checked = 0

    for path in files:
        text = path.read_text(encoding="utf-8")
        m = EN_RE.search(text)
        if not m:
            continue
        checked += 1
        en_title = m.group(1).strip()

        h1_match = re.search(r"^#\s+(.+)$", text, re.MULTILINE)
        if not h1_match:
            continue
        cn_title = h1_match.group(1).strip()

        # 1. Generic fallback check
        for generic in GENERIC_FALLBACKS:
            if normalize(en_title) == normalize(generic):
                if not h1_covers_generic(cn_title, generic):
                    generic_mismatches.append((path, en_title, cn_title))
                break

        # 2. Exact glossary match check
        if cn_title in glossary:
            expected_en = glossary[cn_title]
            if normalize(en_title) != normalize(expected_en):
                exact_mismatches.append((path, cn_title, en_title, expected_en))

    print(f"已检查 **EN** 头文件数: {checked}")
    print(f"术语表精确条目数: {len(glossary)}")

    if generic_mismatches:
        print(f"\nEN 标题为通用占位符且 H1 未明确包含该主题 ({len(generic_mismatches)}):")
        for path, en, cn in generic_mismatches:
            print(f"  - {path.relative_to(ROOT)}")
            print(f"      H1:    {cn}")
            print(f"      EN:    {en}")
    else:
        print("\n未发现通用占位符误用。")

    if exact_mismatches:
        print(f"\nH1 与术语表精确匹配但 EN 不一致 ({len(exact_mismatches)}):")
        for path, cn, en, expected in exact_mismatches:
            print(f"  - {path.relative_to(ROOT)}")
            print(f"      H1:      {cn}")
            print(f"      文件 EN: {en}")
            print(f"      术语表:  {expected}")

    return 1 if (generic_mismatches or exact_mismatches) else 0


if __name__ == "__main__":
    sys.exit(main())
