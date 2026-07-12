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

EXCLUDE_DIRS = {"archive", "deprecated", "sources", "placeholders"}
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


_FIELD_START_RE = re.compile(r"^\*\*[^*]+\*\*[:：]")


def normalize_blockquote_header(content: str, max_lines: int = 150) -> str:
    """把文件顶部 blockquote 元数据规整为“每字段一行”的文本。

    原文件常见多行 blockquote 写法::

        > **后置概念**:
        >
        > [Lifetimes](03_lifetimes.md)

    直接跨行正则抽取会把续行符 `>` 抽成脏数据（如 `> > [元层`，
    即 atlas 02 的 T5 单元格泄漏）或丢失链接。规整后该字段变为
    `**后置概念**: [Lifetimes](03_lifetimes.md)`，供逐字段正则使用。
    """
    fields: list[str] = []
    for ln in content.splitlines()[:max_lines]:
        s = ln.strip()
        if s == "---":
            break
        if not s.startswith(">"):
            continue
        body = s[1:].strip()
        if not body:
            continue
        if _FIELD_START_RE.match(body):
            fields.append(body)
        elif body.startswith(("```", "<")):
            # 代码围栏/HTML 片段是“概念卡片”正文而非元数据续行，独立成段，
            # 避免被并入 Summary/EN 等字段（atlas 定义列出现 ``` 泄漏的根因）。
            fields.append(body)
        elif fields:
            fields[-1] += " " + body
    return "\n".join(fields)


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

    # 其余字段在规整后的 blockquote 头部上抽取（多行续行已合并为单行）；
    # 若头部未命中（字段写在 --- 之后等非常规位置），回退到全文旧式正则。
    header = normalize_blockquote_header(content)

    def field(header_pat: str, legacy_pat: str, flags: int = 0) -> re.Match | None:
        m = re.search(header_pat, header, flags)
        if m:
            return m
        return re.search(legacy_pat, content, flags)

    # EN name may also be explicitly stated
    en_match = field(r"\*\*EN\*\*[:：]\s*(.+)", r">\s*\*\*EN\*\*[:：]\s*(.+)")
    if en_match:
        meta["en_name"] = en_match.group(1).strip()

    summary_match = field(r"\*\*Summary\*\*[:：]\s*(.+)", r">\s*\*\*Summary\*\*[:：]\s*(.+)", re.IGNORECASE)
    if summary_match:
        meta["summary"] = summary_match.group(1).strip()

    audience_match = field(r"\*\*受众\*\*[:：]\s*\[?([^\]]+)\]?", r">\s*\*\*受众\*\*[:：]\s*\[?([^\]]+)\]?")
    if audience_match:
        meta["audience"] = audience_match.group(1).strip()

    level_match = field(r"\*\*内容分级\*\*[:：]\s*\[?([^\]]+)\]?", r">\s*\*\*内容分级\*\*[:：][ \t]*\[?([^\]\n]+)\]?")
    if level_match:
        meta["level"] = level_match.group(1).strip()

    bloom_match = field(r"\*\*Bloom\s*层级\*\*[:：]\s*(.+)", r">\s*\*\*Bloom\s*层级\*\*[:：]\s*(.+)", re.IGNORECASE)
    if bloom_match:
        meta["bloom"] = bloom_match.group(1).strip()

    asp_match = field(r"\*\*A/S/P\s*标记\*\*[:：]\s*\*\*(\w)\*\*", r">\s*\*\*A/S/P\s*标记\*\*[:：]\s*\*\*(\w)\*\*")
    if asp_match:
        meta["asp"] = asp_match.group(1).strip()

    dual_match = field(r"\*\*双维定位\*\*[:：]\s*(.+)", r">\s*\*\*双维定位\*\*[:：]\s*(.+)")
    if dual_match:
        meta["dual"] = dual_match.group(1).strip()

    positioning_match = field(r"\*\*定位\*\*[:：]\s*(.+)", r">\s*\*\*定位\*\*[:：]\s*(.+)")
    if positioning_match:
        meta["positioning"] = positioning_match.group(1).strip()

    # prereqs/postreqs can be 前置概念/前置依赖/后置概念/后置延伸
    prereq_match = field(r"\*\*前置(?:概念|依赖)\*\*[:：]\s*(.+)", r">\s*\*\*前置(?:概念|依赖)\*\*[:：][ \t]*([^\n]+)")
    if prereq_match:
        meta["prereqs"] = extract_links(prereq_match.group(1))

    postreq_match = field(r"\*\*后置(?:概念|延伸)\*\*[:：]\s*(.+)", r">\s*\*\*后置(?:概念|延伸)\*\*[:：][ \t]*([^\n]+)")
    if postreq_match:
        meta["postreqs"] = extract_links(postreq_match.group(1))

    theorem_match = field(r"\*\*定理链\*\*[:：]\s*(.+)", r">\s*\*\*定理链\*\*[:：]\s*(.+)")
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

    # 关键词 → 表征类型。按子串匹配章节标题（`kw in title`），覆盖各层历史遗留的
    # 多种标题写法（如「⚠️ 反例与陷阱」「四、反命题与边界分析」「三、选型决策矩阵」）。
    # 注意「示例」会匹配「对应代码示例/实际应用示例」，「场景」匹配「实际应用场景」，
    # 均为 03/04 atlas 期望的宽口径信号。
    keyword_map = {
        "思维导图": "mindmap",
        "决策树": "decision_tree",
        "决策矩阵": "decision_tree",
        "判定树": "decision_tree",
        "判断推理": "decision_tree",
        "选型": "decision_tree",
        "何时用": "decision_tree",
        "场景": "decision_tree",
        "边界判定树": "boundary_tree",
        "属性矩阵": "attribute_matrix",
        "概念定义矩阵": "definition_matrix",
        "示例": "examples_counterexamples",
        "反例": "examples_counterexamples",
        "陷阱": "examples_counterexamples",
        "边界测试": "examples_counterexamples",
        "误用": "examples_counterexamples",
        "易错": "examples_counterexamples",
        "定理推理树": "theorem_tree",
        "推理链": "theorem_tree",
        "定理链": "theorem_tree",
        "反命题树": "theorem_tree",
        "证明树": "theorem_tree",
        "逆向推理": "theorem_tree",
        "反向推理": "theorem_tree",
        "多维矩阵": "multidim_matrix",
        "相关概念关联": "related_concepts",
        "相关概念": "related_concepts",
        "相关主题": "related_concepts",
        "相关资源": "related_concepts",
        "延伸阅读": "related_concepts",
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


def extract_representation_signals(content: str, sections: dict[str, list[str]],
                                   diagrams: list[str]) -> dict[str, Any]:
    """抽取 03/04/06/09 atlas 生成所需的结构化表征信号。

    - compile_fail_count: ```rust compile_fail 代码块数（反例的强信号）
    - mermaid_decision_count: 含菱形判定节点 `{...}` 的 mermaid 图数（决策树信号）
    - implies_count: 定理链符号 ⟹ 出现次数（推理链信号）
    - example/decision/reasoning_sections: 命中章节标题清单（去重保序）
    - related_links: 「相关概念/延伸阅读」等章节正文中的 markdown 链接
      （层间映射 06 的跨层引用扩展来源）
    """

    def titles(key: str) -> list[str]:
        seen: list[str] = []
        for sec in sections.get(key, []):
            t = re.sub(r"^[一二三四五六七八九十零]+[、.．]\s*", "", sec["title"]).strip()
            t = re.sub(r"^\d+(?:\.\d+)*\s+", "", t).strip()
            if t and t not in seen:
                seen.append(t)
        return seen

    related_links: list[dict[str, str]] = []
    for sec in sections.get("related_concepts", []):
        related_links.extend(extract_links(sec["body"]))

    return {
        "compile_fail_count": len(re.findall(r"```rust[^\n`]*compile_fail", content)),
        "mermaid_decision_count": sum(1 for d in diagrams if re.search(r"\w+\s*\{[^}]*\}", d)),
        "implies_count": content.count("\u27f9"),  # ⟹
        "example_sections": titles("examples_counterexamples"),
        "decision_sections": titles("decision_tree") + titles("boundary_tree"),
        "reasoning_sections": titles("theorem_tree"),
        "related_links": related_links,
    }


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
    signals = extract_representation_signals(content, sections, diagrams)

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
        "signals": signals,
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

    # 表征信号统计（03/04/06/09 atlas 生成依据）
    sig_stats = {
        "example_signal(节或compile_fail)": sum(1 for c in concepts if c["signals"]["example_sections"] or c["signals"]["compile_fail_count"]),
        "decision_signal(节或mermaid判定)": sum(1 for c in concepts if c["signals"]["decision_sections"] or c["signals"]["mermaid_decision_count"]),
        "reasoning_signal(节或定理链)": sum(1 for c in concepts if c["signals"]["reasoning_sections"] or c["theorem_chain"]),
        "related_links(相关概念节)": sum(1 for c in concepts if c["signals"]["related_links"]),
    }
    print("\nRepresentation signal counts:")
    for k, v in sig_stats.items():
        print(f"  {k}: {v}")


if __name__ == "__main__":
    main()
