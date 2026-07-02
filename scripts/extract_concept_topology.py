#!/usr/bin/env python3
"""
Extract concept topology from concept/**/*.md into a structured JSON.

Output: tmp/concept_topology_raw.json
"""
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
CONCEPT_DIR = ROOT / "concept"
OUT_PATH = ROOT / "tmp" / "concept_topology_raw.json"

EXCLUDE_DIRS = {"archive", "deprecated", "sources"}
EXCLUDE_FILES = {"README.md", "SUMMARY.md", "00.md", "01.md", "02.md", "03.md", "04.md", "05.md", "06.md", "07.md"}


def should_include(path: Path) -> bool:
    rel = path.relative_to(CONCEPT_DIR)
    parts = rel.parts
    if any(p in EXCLUDE_DIRS for p in parts):
        return False
    if path.name in EXCLUDE_FILES:
        return False
    if path.name.startswith("sandbox"):
        return False
    # Must be under a numeric layer directory like 01_foundation
    if not parts or not re.match(r"^\d{2}_", parts[0]):
        return False
    return True


def detect_layer(rel_path: Path) -> str:
    parts = rel_path.parts
    if not parts:
        return "L0"
    first = parts[0]
    m = re.match(r"^(\d{2})_", first)
    if not m:
        return "L0"
    num = int(m.group(1))
    return f"L{num}"


def parse_header_metadata(content: str) -> dict[str, Any]:
    """Parse the block-quotes metadata at the top of concept files."""
    meta: dict[str, Any] = {
        "zh_name": "",
        "en_name": "",
        "summary": "",
        "audience": "",
        "level": "",
        "bloom": "",
        "asp": "",
        "dual": "",
        "positioning": "",
        "prereqs": [],
        "postreqs": [],
        "theorem_chain": "",
        "sources": [],
    }

    # First line is usually # Concept Name
    title_match = re.search(r"^#\s+(.+?)(?:（(.+)）)?\s*$", content, re.MULTILINE)
    if title_match:
        meta["zh_name"] = title_match.group(1).strip()
        if title_match.group(2):
            meta["en_name"] = title_match.group(2).strip()

    # EN name may also be explicitly stated
    en_match = re.search(r">\s*\*\*EN\*\*[:：]\s*(.+)", content)
    if en_match:
        meta["en_name"] = en_match.group(1).strip()

    summary_match = re.search(r">\s*\*\*Summary\*\*[:：]\s*(.+)", content, re.IGNORECASE)
    if summary_match:
        meta["summary"] = summary_match.group(1).strip()

    audience_match = re.search(r">\s*\*\*受众\*\*[:：]\s*\[?([^\]]+)\]?", content)
    if audience_match:
        meta["audience"] = audience_match.group(1).strip()

    level_match = re.search(r">\s*\*\*内容分级\*\*[:：]\s*\[?([^\]]+)\]?", content)
    if level_match:
        meta["level"] = level_match.group(1).strip()

    bloom_match = re.search(r">\s*\*\*Bloom\s*层级\*\*[:：]\s*(.+)", content, re.IGNORECASE)
    if bloom_match:
        meta["bloom"] = bloom_match.group(1).strip()

    asp_match = re.search(r">\s*\*\*A/S/P\s*标记\*\*[:：]\s*\*\*(\w)\*\*", content)
    if asp_match:
        meta["asp"] = asp_match.group(1).strip()

    dual_match = re.search(r">\s*\*\*双维定位\*\*[:：]\s*(.+)", content)
    if dual_match:
        meta["dual"] = dual_match.group(1).strip()

    positioning_match = re.search(r">\s*\*\*定位\*\*[:：]\s*(.+)", content)
    if positioning_match:
        meta["positioning"] = positioning_match.group(1).strip()

    # prereqs/postreqs can be 前置依赖/后置概念 or 前置概念/后置概念
    prereq_match = re.search(r">\s*\*\*前置(?:概念|依赖)\*\*[:：]\s*(.+)", content)
    if prereq_match:
        meta["prereqs"] = extract_links(prereq_match.group(1))

    postreq_match = re.search(r">\s*\*\*后置概念\*\*[:：]\s*(.+)", content)
    if postreq_match:
        meta["postreqs"] = extract_links(postreq_match.group(1))

    theorem_match = re.search(r">\s*\*\*定理链\*\*[:：]\s*(.+)", content)
    if theorem_match:
        meta["theorem_chain"] = theorem_match.group(1).strip()

    # Sources: collect all [来源: ...] markers and 主要来源 lines
    meta["sources"] = extract_sources(content)

    return meta


def extract_links(text: str) -> list[dict[str, str]]:
    """Extract markdown links like [Name](path) or [Name](url)."""
    links: list[dict[str, str]] = []
    for m in re.finditer(r"\[([^\]]+)\]\(([^)]+)\)", text):
        links.append({"title": m.group(1).strip(), "href": m.group(2).strip()})
    return links


def extract_block_after_marker(content: str, marker: str) -> str:
    """Extract all quoted lines after a marker like **主要来源**: until a non-quoted line."""
    out = ""
    marker_re = re.compile(r">\s*\*\*" + re.escape(marker) + r"\*\*[:：]")
    lines = content.splitlines(keepends=True)
    i = 0
    while i < len(lines):
        if marker_re.search(lines[i]):
            # Include this line and subsequent quoted lines
            out += lines[i]
            i += 1
            while i < len(lines) and re.match(r"\s*>", lines[i]):
                out += lines[i]
                i += 1
            continue
        i += 1
    return out


def extract_sources(content: str) -> list[dict[str, str]]:
    sources: list[dict[str, str]] = []
    # Pattern 1: > [来源: [Name](url)]
    for m in re.finditer(r"\[来源[:：]\s*(?:\[([^\]]+)\]\(([^)]+)\)|([^\]]+))\s*\]", content):
        name = m.group(1) or m.group(3) or ""
        url = m.group(2) or ""
        sources.append({"name": name.strip(), "url": url.strip()})

    # Patterns 2-4: multi-line source blocks (来源 / 主要来源 / 权威来源)
    for marker in ["来源", "主要来源", "权威来源"]:
        block = extract_block_after_marker(content, marker)
        for link in extract_links(block):
            sources.append({"name": link["title"], "url": link["href"]})

    # Deduplicate by url
    seen: set[str] = set()
    unique: list[dict[str, str]] = []
    for s in sources:
        key = (s["name"], s["url"])
        if key not in seen:
            seen.add(key)
            unique.append(s)
    return unique


def extract_sections(content: str) -> dict[str, list[str]]:
    """Extract sections with specific knowledge-representation keywords."""
    sections: dict[str, list[str]] = {
        "mindmap": [],
        "decision_tree": [],
        "boundary_tree": [],
        "attribute_matrix": [],
        "definition_matrix": [],
        "examples_counterexamples": [],
        "theorem_tree": [],
        "multidim_matrix": [],
        "related_concepts": [],
        "source_relations": [],
    }

    keyword_map = {
        "思维导图": "mindmap",
        "决策树": "decision_tree",
        "边界判定树": "boundary_tree",
        "属性矩阵": "attribute_matrix",
        "概念定义矩阵": "definition_matrix",
        "示例与反例": "examples_counterexamples",
        "定理推理树": "theorem_tree",
        "多维矩阵": "multidim_matrix",
        "相关概念关联": "related_concepts",
        "知识来源关系": "source_relations",
    }

    # Split by level-2 sections
    section_pattern = re.compile(r"^##\s+(.+)$", re.MULTILINE)
    parts = section_pattern.split(content)
    if len(parts) > 1:
        for i in range(1, len(parts), 2):
            title = parts[i].strip()
            body = parts[i + 1] if i + 1 < len(parts) else ""
            for kw, key in keyword_map.items():
                if kw in title:
                    sections[key].append({"title": title, "body": body.strip()})

    return sections


def extract_mermaid_diagrams(content: str) -> list[str]:
    """Extract all mermaid diagrams."""
    diagrams: list[str] = []
    for m in re.finditer(r"```mermaid\n(.*?)\n```", content, re.DOTALL):
        diagrams.append(m.group(1).strip())
    return diagrams


def extract_code_blocks(content: str) -> list[dict[str, str]]:
    """Extract rust code blocks as examples."""
    blocks: list[dict[str, str]] = []
    for m in re.finditer(r"```rust(.*?)\n(.*?)\n```", content, re.DOTALL):
        info = m.group(1).strip()
        code = m.group(2).strip()
        blocks.append({"info": info, "code": code[:500]})  # truncate for JSON size
    return blocks


def extract_tables(content: str) -> list[list[list[str]]]:
    """Extract markdown tables."""
    tables: list[list[list[str]]] = []
    for block in re.finditer(r"((?:\|.*\|\n)+)", content):
        lines = block.group(1).strip().splitlines()
        rows = []
        for line in lines:
            if re.match(r"\|[-:\s|]+\|", line):
                continue
            cells = [c.strip() for c in line.strip("|").split("|")]
            rows.append(cells)
        if rows:
            tables.append(rows)
    return tables


def classify_source_tier(source: dict[str, str]) -> str:
    url = source.get("url", "")
    name = source.get("name", "")
    combined = (url + " " + name).lower()
    if "doc.rust-lang.org/reference" in url:
        return "L1_specification"
    if "doc.rust-lang.org/book" in url:
        return "L1_trpl"
    if "rust-lang.github.io/rfcs" in url:
        return "L1_rfc"
    if "doc.rust-lang.org/nomicon" in url:
        return "L1_rustonomicon"
    if "doc.rust-lang.org/cargo" in url:
        return "L1_cargo"
    if "doc.rust-lang.org/std" in url:
        return "L1_std"
    if "doc.rust-lang.org/nightly/nightly-rustc" in url:
        return "L1_std"
    if "rustc-dev-guide.rust-lang.org" in url:
        return "L1_specification"
    if "rust-lang.github.io" in url and "rfcs" not in url:
        return "L1_github"
    if "www.rust-lang.org" in combined or "foundation.rust-lang.org" in combined:
        return "L1_blog"
    if any(x in combined for x in ["unicode.org", "iso.org", "ieee.org", "ietf.org", "itanium-cxx-abi"]):
        return "L5_standard"
    if any(x in combined for x in ["popl", "pldi", "ecoops", "oopsla", "icfp", "arxiv.org", "mpi-sws.org/rustbelt"]):
        return "L2_academic"
    if any(x in combined for x in [".edu", "cs.brown.edu", "cmu", "mit.edu", "stanford", "upenn"]):
        return "L3_course"
    if any(x in combined for x in ["wikipedia.org"]):
        return "L0_wikipedia"
    if any(x in combined for x in ["github.com/rust-lang"]):
        return "L1_github"
    if any(x in combined for x in ["blog.rust-lang.org", "inside rust"]):
        return "L1_blog"
    return "Lx_other"


def process_file(path: Path) -> dict[str, Any] | None:
    try:
        content = path.read_text(encoding="utf-8")
    except Exception as e:
        print(f"Error reading {path}: {e}")
        return None

    rel = path.relative_to(CONCEPT_DIR)
    layer = detect_layer(rel)
    meta = parse_header_metadata(content)
    sections = extract_sections(content)
    diagrams = extract_mermaid_diagrams(content)
    code_blocks = extract_code_blocks(content)
    tables = extract_tables(content)

    # Classify sources
    source_tiers: dict[str, int] = {}
    for s in meta["sources"]:
        tier = classify_source_tier(s)
        source_tiers[tier] = source_tiers.get(tier, 0) + 1

    return {
        "id": path.stem,
        "path": str(rel).replace("\\", "/"),
        "layer": layer,
        "zh_name": meta["zh_name"],
        "en_name": meta["en_name"],
        "summary": meta["summary"],
        "audience": meta["audience"],
        "level": meta["level"],
        "bloom": meta["bloom"],
        "asp": meta["asp"],
        "dual": meta["dual"],
        "positioning": meta["positioning"],
        "prereqs": meta["prereqs"],
        "postreqs": meta["postreqs"],
        "theorem_chain": meta["theorem_chain"],
        "sources": meta["sources"],
        "source_tiers": source_tiers,
        "sections": sections,
        "mermaid_diagrams": diagrams,
        "code_blocks_count": len(code_blocks),
        "code_blocks_sample": code_blocks[:3],
        "tables_count": len(tables),
        "tables_sample": tables[:2],
        "line_count": len(content.splitlines()),
    }


def main() -> None:
    files = sorted(p for p in CONCEPT_DIR.rglob("*.md") if should_include(p))
    print(f"Found {len(files)} concept files to process")

    concepts: list[dict[str, Any]] = []
    for path in files:
        data = process_file(path)
        if data:
            concepts.append(data)

    result = {
        "metadata": {
            "total_files": len(concepts),
            "extracted_at": "2026-07-02",
            "schema_version": "1.0",
        },
        "concepts": concepts,
    }

    OUT_PATH.parent.mkdir(parents=True, exist_ok=True)
    OUT_PATH.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Wrote {OUT_PATH}")

    # Print quick stats
    tier_counts: dict[str, int] = {}
    section_counts: dict[str, int] = {}
    for c in concepts:
        for tier, cnt in c["source_tiers"].items():
            tier_counts[tier] = tier_counts.get(tier, 0) + cnt
        for sec_key, sec_list in c["sections"].items():
            if sec_list:
                section_counts[sec_key] = section_counts.get(sec_key, 0) + 1

    print("\nSource tier counts:")
    for tier, cnt in sorted(tier_counts.items(), key=lambda x: -x[1]):
        print(f"  {tier}: {cnt}")

    print("\nSection representation counts:")
    for sec, cnt in sorted(section_counts.items(), key=lambda x: -x[1]):
        print(f"  {sec}: {cnt}")


if __name__ == "__main__":
    main()
