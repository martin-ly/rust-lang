#!/usr/bin/env python3
"""
Canonical Boundary Patrol

Scan docs/ and content/ for content that may duplicate or overlap with
concept/ canonical pages, per AGENTS.md §2 canonical rules.

Usage:
    python scripts/check_canonical_boundary.py
    python scripts/check_canonical_boundary.py --strict

Exit code:
    0 if no high-risk duplicates found
    1 if --strict and high-risk duplicates > 0
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from pathlib import Path
from collections import Counter
from typing import Dict, List, Tuple

ROOT = Path(__file__).resolve().parent.parent
CONCEPT_DIR = ROOT / "concept"
DOCS_DIR = ROOT / "docs"
CONTENT_DIR = ROOT / "content"

# Ignore paths that are explicitly indexes/navigation or archive-like
IGNORE_PATTERNS = [
    r"README\.md$",
    r"INDEX\.md$",
    r"SUMMARY\.md$",
    r"reports/",
    r"tmp/",
    r"archive/",
    r"book/",
]


def should_ignore(path: Path) -> bool:
    s = str(path).replace("\\", "/")
    for pat in IGNORE_PATTERNS:
        if re.search(pat, s):
            return True
    return False


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except Exception:
        return ""


def extract_title_and_en(path: Path, text: str) -> Tuple[str, str]:
    """Extract Chinese title (first # heading) and EN title from frontmatter."""
    title = ""
    en = ""
    # Chinese title: first # line
    m = re.search(r"^#\s+(.+)$", text, re.MULTILINE)
    if m:
        title = m.group(1).strip()
    # EN title in frontmatter
    m = re.search(r"\*\*EN\*\*:\s*(.+)", text)
    if m:
        en = m.group(1).strip()
    return title, en


def tokenize(text: str) -> List[str]:
    """Simple tokenization: Chinese chars + alphanumeric words."""
    # Remove markdown links, code blocks, URLs
    text = re.sub(r"!?\[([^\]]+)\]\([^)]+\)", r"\1", text)
    text = re.sub(r"```[\s\S]*?```", " ", text)
    text = re.sub(r"https?://\S+", " ", text)
    # Chinese characters
    chars = re.findall(r"[\u4e00-\u9fff]", text)
    # English/numbers
    words = re.findall(r"[a-zA-Z0-9_]{2,}", text)
    return [w.lower() for w in words] + chars


def heading_tokens(text: str) -> Counter:
    """Tokens from headings only, weighted higher."""
    headings = re.findall(r"^#+\s+(.+)$", text, re.MULTILINE)
    tokens: List[str] = []
    for h in headings:
        tokens.extend(tokenize(h))
    # triple weight for headings
    c = Counter(tokens)
    return Counter({k: v * 3 for k, v in c.items()})


def body_tokens(text: str) -> Counter:
    """Tokens from body text."""
    # Remove frontmatter-ish metadata lines
    lines = text.splitlines()
    body_lines: List[str] = []
    in_front = False
    for line in lines:
        if line.startswith("> ") and not in_front:
            in_front = True
        if in_front and not line.startswith("> "):
            in_front = False
        if not in_front:
            body_lines.append(line)
    return Counter(tokenize("\n".join(body_lines)))


def document_fingerprint(text: str) -> Counter:
    """Combined fingerprint: headings weighted + body."""
    return heading_tokens(text) + body_tokens(text)


def cosine_similarity(a: Counter, b: Counter) -> float:
    if not a or not b:
        return 0.0
    dot = sum(a[k] * b[k] for k in a if k in b)
    norm_a = sum(v * v for v in a.values()) ** 0.5
    norm_b = sum(v * v for v in b.values()) ** 0.5
    if norm_a == 0 or norm_b == 0:
        return 0.0
    return dot / (norm_a * norm_b)


def collect_md_files(directory: Path) -> List[Path]:
    return [p for p in directory.rglob("*.md") if not should_ignore(p)]


def main() -> int:
    parser = argparse.ArgumentParser(description="Canonical boundary patrol")
    parser.add_argument("--strict", action="store_true", help="Exit non-zero if high-risk duplicates found")
    parser.add_argument(
        "--threshold",
        type=float,
        default=0.60,
        help="Similarity threshold for flagging (default 0.60; lower values are very noisy)",
    )
    parser.add_argument("--min-concept-words", type=int, default=50, help="Ignore concept pages with fewer body words")
    parser.add_argument("--top", type=int, default=30, help="Number of top pairs to report")
    parser.add_argument("--json", help="Write full findings to JSON file")
    args = parser.parse_args()

    concept_files = collect_md_files(CONCEPT_DIR)
    docs_files = collect_md_files(DOCS_DIR)
    content_files = collect_md_files(CONTENT_DIR)
    external_files = docs_files + content_files

    # Build concept index with fingerprints
    concept_index: List[Tuple[Path, str, str, Counter]] = []
    skipped_concept = 0
    for p in concept_files:
        text = read_text(p)
        title, en = extract_title_and_en(p, text)
        fp = document_fingerprint(text)
        body_word_count = sum(body_tokens(text).values())
        if body_word_count < args.min_concept_words:
            skipped_concept += 1
            continue
        concept_index.append((p, title, en, fp))

    # Build external index
    external_index: List[Tuple[Path, str, str, Counter]] = []
    for p in external_files:
        text = read_text(p)
        title, en = extract_title_and_en(p, text)
        fp = document_fingerprint(text)
        external_index.append((p, title, en, fp))

    print(
        f"[canonical-boundary] concept={len(concept_index)} (skipped {skipped_concept} short) "
        f"docs={len(docs_files)} content={len(content_files)} threshold={args.threshold}"
    )

    high_risk: List[Tuple[float, Path, str, Path, str]] = []

    for ext_path, ext_title, ext_en, ext_fp in external_index:
        for con_path, con_title, con_en, con_fp in concept_index:
            sim = cosine_similarity(ext_fp, con_fp)
            if sim >= args.threshold:
                high_risk.append((sim, ext_path, ext_title, con_path, con_title))

    high_risk.sort(reverse=True, key=lambda x: x[0])

    if not high_risk:
        print("[canonical-boundary] ✅ No high-risk canonical boundary overlaps found.")
        return 0

    print(f"\n[canonical-boundary] ⚠️ Found {len(high_risk)} pairs with similarity >= {args.threshold}")
    print("-" * 80)
    for i, (sim, ext_path, ext_title, con_path, con_title) in enumerate(high_risk[: args.top], 1):
        rel_ext = ext_path.relative_to(ROOT)
        rel_con = con_path.relative_to(ROOT)
        print(f"{i}. similarity={sim:.3f}")
        print(f"   external: {rel_ext} — {ext_title or '(no title)'}")
        print(f"   concept:  {rel_con} — {con_title or '(no title)'}")

    if len(high_risk) > args.top:
        print(f"\n... and {len(high_risk) - args.top} more pairs")

    if args.json:
        import json

        payload = [
            {
                "similarity": sim,
                "external": str(ext_path.relative_to(ROOT)),
                "external_title": ext_title,
                "concept": str(con_path.relative_to(ROOT)),
                "concept_title": con_title,
            }
            for sim, ext_path, ext_title, con_path, con_title in high_risk
        ]
        with open(args.json, "w", encoding="utf-8") as jf:
            json.dump(payload, jf, ensure_ascii=False, indent=2)
        print(f"\n📝 JSON 报告: {args.json}")

    if args.strict:
        print("\n[canonical-boundary] ❌ strict mode: failing due to high-risk overlaps")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
