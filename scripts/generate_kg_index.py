#!/usr/bin/env python3
"""从 concept/ 元数据生成知识图谱索引 (KG Index)。

本脚本扫描 concept/ 目录下的 markdown 文件，提取：
- 概念 ID（相对路径）
- 中英标题与摘要
- Bloom 层级
- Rust 版本
- 前置/后置概念链接
- 定理链编号
- 关联的 crates/ 代码示例（通过路径推断）

输出: concept/00_meta/kg_index.json
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CONCEPT_DIR = ROOT / "concept"
OUTPUT = CONCEPT_DIR / "00_meta" / "kg_index.json"

# Regex patterns
EN_RE = re.compile(r"^\s*>\s*\*\*EN\*\*:\s*(.+)$", re.MULTILINE)
SUMMARY_RE = re.compile(r"^\s*>\s*\*\*Summary\*\*:\s*(.+)$", re.MULTILINE)
BLOOM_RE = re.compile(r"^\s*>\s*\*\*Bloom 层级\*\*:\s*(.+)$", re.MULTILINE)
VERSION_RE = re.compile(r"^\s*>\s*\*\*(?:Rust 版本|对应 Rust 版本)\*\*:\s*(.+)$", re.MULTILINE)
PRECONCEPT_RE = re.compile(r"^\s*>\s*\*\*前置概念\*\*:\s*(.+)$", re.MULTILINE)
POSTCONCEPT_RE = re.compile(r"^\s*>\s*\*\*后置概念\*\*:\s*(.+)$", re.MULTILINE)
THEOREM_RE = re.compile(r"T-\d+")
LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")


def extract_first(pattern: re.Pattern, text: str) -> str | None:
    m = pattern.search(text)
    return m.group(1).strip() if m else None


def extract_links(line: str) -> list[dict[str, str]]:
    """Extract markdown links from a metadata line."""
    return [{"title": t.strip(), "path": p.strip()} for t, p in LINK_RE.findall(line)]


def infer_crates(path: Path) -> list[str]:
    """Infer related crates from concept path."""
    rel = path.relative_to(CONCEPT_DIR).as_posix()
    crate_map = {
        "01_ownership_borrow_lifetime": "c01_ownership_borrow_scope",
        "02_type_system": "c02_type_system",
        "04_control_flow": "c03_control_fn",
        "01_generics": "c04_generic",
        "00_concurrency": "c05_threads",
        "01_async": "c06_async",
        "02_process_ipc": "c07_process",
        "00_traits": "c09_design_pattern",
        "03_proc_macros": "c11_macro_system_proc",
        "05_comparative": "c14_semantic_web",
        "04_model_checking": "c15_verification_tools",
    }
    crates: list[str] = []
    for key, crate in crate_map.items():
        if key in rel:
            crates.append(crate)
    return crates


def main() -> int:
    entities: list[dict] = []

    for path in sorted(CONCEPT_DIR.rglob("*.md")):
        rel = path.relative_to(CONCEPT_DIR).as_posix()
        # Skip archive-ish files inside concept/
        if "archive" in rel or "legacy" in rel:
            continue

        text = path.read_text(encoding="utf-8")
        title_line = text.lstrip().splitlines()[0]
        title = title_line.lstrip("# ").strip() if title_line.startswith("#") else ""

        en = extract_first(EN_RE, text)
        if not en:
            continue  # Only index files with EN metadata

        summary = extract_first(SUMMARY_RE, text)
        bloom = extract_first(BLOOM_RE, text)
        version = extract_first(VERSION_RE, text)

        pre_line = extract_first(PRECONCEPT_RE, text)
        post_line = extract_first(POSTCONCEPT_RE, text)

        entities.append(
            {
                "id": f"concept:{rel}",
                "path": rel,
                "title": title,
                "en": en,
                "summary": summary,
                "bloom": bloom,
                "rust_version": version,
                "prerequisites": extract_links(pre_line) if pre_line else [],
                "postrequisites": extract_links(post_line) if post_line else [],
                "theorems": sorted(set(THEOREM_RE.findall(text))),
                "related_crates": infer_crates(path),
            }
        )

    kg = {
        "metadata": {
            "version": "1.0",
            "generated": "2026-07-11",
            "rust_version": "1.97.0+",
            "source": "concept/",
            "entity_count": len(entities),
            "schema": "simple KG index",
        },
        "entities": entities,
    }

    OUTPUT.write_text(json.dumps(kg, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"Generated KG index with {len(entities)} entities: {OUTPUT}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
