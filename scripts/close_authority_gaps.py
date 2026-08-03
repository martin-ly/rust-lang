#!/usr/bin/env python3
"""Append P1/P2 international authority references to concept/ gap pages.

Reads the gap lists from reports/CONCEPT_AUTHORITY_COVERAGE_2026-08-04.md and
adds a small, relevant references section when missing.
"""

import re
from pathlib import Path

ROOT = Path("E:/_src/rust-lang").resolve()
REPORT = ROOT / "reports/CONCEPT_AUTHORITY_COVERAGE_2026-08-04.md"

P1 = {
    "rustbelt": "https://dl.acm.org/doi/10.1145/3158154",
    "stacked_borrows": "https://dl.acm.org/doi/10.1145/3371106",
    "typed_closure": "https://dl.acm.org/doi/10.1145/237721.237791",
    "hygienic_macros": "https://dl.acm.org/doi/10.1145/319838.319859",
    "csp": "https://dl.acm.org/doi/10.1145/359576.359585",
    "gof": "https://dl.acm.org/doi/book/10.5555/186897",
    "embedded_survey": "https://arxiv.org/abs/2311.05063",
    "operational_semantics": "https://arxiv.org/abs/1804.07608",
    "owl_dl": "https://dl.acm.org/doi/10.1145/263690.263805",
}

P2 = {
    "rust_patterns": ["https://rust-unofficial.github.io/patterns/"],
    "embedded_book": ["https://docs.rust-embedded.org/book/"],
    "rust_blog": ["https://blog.rust-lang.org/"],
    "rfcs": ["https://rust-lang.github.io/rfcs/"],
    "owl": ["https://www.w3.org/TR/owl2-overview/"],
    "shacl": ["https://www.w3.org/TR/shacl/"],
}


def choose_refs(rel_path: str) -> tuple[list[str], list[str]]:
    rp = rel_path.replace("\\", "/").lower()

    # Core crates
    if "/02_core_crates/" in rp:
        return [P1["rustbelt"]], P2["rust_patterns"] + P2["rust_blog"]

    # Design patterns
    if "/03_design_patterns/" in rp:
        return [P1["gof"]], P2["rust_patterns"]

    # Embedded / no_std
    if "/05_systems_and_embedded/" in rp:
        return [P1["embedded_survey"]], P2["embedded_book"] + P2["rust_patterns"]

    # Formal semantics / operational / concurrency / system
    if "/04_formal/" in rp:
        if "kg_owl_shacl" in rp:
            return [P1["owl_dl"]], P2["owl"] + P2["shacl"] + P2["rust_patterns"]
        return [P1["rustbelt"], P1["operational_semantics"]], P2["rust_patterns"] + P2["rust_blog"]

    # FFI
    if "/03_advanced/04_ffi/" in rp:
        return [P1["rustbelt"]], P2["rust_patterns"] + P2["rust_blog"]

    # Macros
    if "macro" in rp or "procedural_macros" in rp:
        return [P1["hygienic_macros"]], P2["rust_patterns"] + P2["rust_blog"]

    # Closures
    if "closure" in rp:
        return [P1["typed_closure"]], P2["rust_patterns"] + P2["rust_blog"]

    # Inline assembly
    if "inline_assembly" in rp:
        return [P1["rustbelt"]], P2["rust_patterns"] + P2["rust_blog"]

    # Kubernetes / web
    if "kubernetes" in rp:
        return [P1["gof"]], P2["rust_patterns"] + P2["rust_blog"]

    # Algorithms / zero-copy / ownership-aware
    if "algorithm" in rp or "zero_copy" in rp or "ownership_aware" in rp:
        return [P1["rustbelt"]], P2["rust_patterns"] + P2["rust_blog"]

    # Enterprise architecture
    if "/14_enterprise_architecture/" in rp:
        return [P1["gof"]], P2["rust_patterns"] + P2["rust_blog"]

    # Version tracking / edition differences
    if "/07_future/" in rp:
        return [P1["rustbelt"]], P2["rust_blog"] + P2["rfcs"]

    # Foundation start pages
    if "/01_foundation/00_start/" in rp:
        return [P1["rustbelt"]], P2["rust_blog"]

    return [P1["rustbelt"]], P2["rust_patterns"] + P2["rust_blog"]


def extract_gaps() -> tuple[list[str], list[str]]:
    text = REPORT.read_text(encoding="utf-8")
    p1, p2 = [], []
    for line in text.splitlines():
        if "内容页 P1 缺口" in line or "内容页 P2 缺口" in line:
            paths = re.findall(r"`(concept/[^`]+\.md)`", line)
            if "P1" in line:
                p1 = paths
            else:
                p2 = paths
    return p1, p2


def add_refs(rel_path: str) -> bool:
    path = ROOT / rel_path.replace("\\", "/")
    if not path.exists():
        print(f"skip missing: {rel_path}")
        return False

    text = path.read_text(encoding="utf-8")
    p1_urls, p2_urls = choose_refs(rel_path)
    all_urls = p1_urls + p2_urls

    # Avoid duplicates already present in the file
    new_urls = [u for u in all_urls if u not in text]
    if not new_urls:
        return False

    section = "\n\n## 国际化权威来源补充（International Authority Sources）\n\n"
    for u in new_urls:
        section += f"- {u}\n"

    # Append before trailing whitespace if any
    text = text.rstrip() + section
    path.write_text(text, encoding="utf-8")
    return True


def main() -> int:
    p1_gaps, p2_gaps = extract_gaps()
    all_gaps = sorted(set(p1_gaps + p2_gaps))
    print(f"P1 gaps: {len(p1_gaps)}, P2 gaps: {len(p2_gaps)}, unique: {len(all_gaps)}")

    updated = 0
    for rel in all_gaps:
        if add_refs(rel):
            updated += 1
            print(f"updated: {rel}")
    print(f"updated {updated} files")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
