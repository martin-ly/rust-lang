#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Taxonomy quality check: detect duplicate EN titles, missing Bloom/Summary,
scattered topics across layers, and invalid redirect stub targets.

Exit codes:
  0 = OK
  1 = issues found (when --strict)

Outputs:
  reports/TAXONOMY_QUALITY_BASELINE_<date>.md
  reports/TAXONOMY_QUALITY_BASELINE_<date>.json
"""
from __future__ import annotations

import argparse
import datetime
import glob
import json
import os
import re
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CONCEPT = os.path.join(ROOT, "concept")

EN_RE = re.compile(r"^>\s*\*\*EN\*\*[:\s]*(.*)$", re.MULTILINE)
SUMMARY_RE = re.compile(r"^>\s*\*\*Summary\*\*[:\s]*(.*)$", re.MULTILINE)
BLOOM_RE = re.compile(r"^>\s*\*\*Bloom 层级\*\*[:\s]*(.*)$", re.MULTILINE)
STUB_TARGET_RE = re.compile(
    r"本文件为(?:学习入口 stub|重定向 stub).*?[`\[]?concept/([^`\]\n]+)\.(?:md|html)",
    re.DOTALL | re.IGNORECASE,
)


def extract_field(text: str, regex: re.Pattern) -> str | None:
    m = regex.search(text)
    return m.group(1).strip() if m else None


def layer_of_path(path: str) -> str | None:
    parts = path.replace("\\", "/").split("/")
    if len(parts) >= 2 and parts[0] == "concept":
        m = re.match(r"(\d{2})_", parts[1])
        if m:
            return f"L{int(m.group(1))}"
    return None


def basename_no_number(path: str) -> str:
    base = os.path.splitext(os.path.basename(path))[0]
    base = re.sub(r"^\d+_", "", base)
    base = re.sub(
        r"_(preview|stabilized|tracking|cheatsheet|quick_start|advanced|basics|"
        r"deep_dive|internals|faq|glossary|index|quiz|examples|collection|part\d+|"
        r"original|final|expanded|supplement)$",
        "",
        base,
    )
    return base


def main():
    parser = argparse.ArgumentParser(description="Taxonomy quality checker")
    parser.add_argument("--strict", action="store_true", help="exit non-zero on issues")
    args = parser.parse_args()

    files = glob.glob(os.path.join(CONCEPT, "**/*.md"), recursive=True)
    issues = defaultdict(list)
    en_map = defaultdict(list)
    missing_bloom = []
    missing_summary = []
    basename_layers = defaultdict(lambda: defaultdict(list))
    invalid_stub_targets = []

    for f in files:
        rel = os.path.relpath(f, ROOT).replace("\\", "/")
        text = open(f, encoding="utf-8", errors="ignore").read()

        en = extract_field(text, EN_RE)
        summary = extract_field(text, SUMMARY_RE)
        bloom = extract_field(text, BLOOM_RE)

        if en:
            en_map[en.lower()].append(rel)
        else:
            issues["missing_en"].append(rel)

        if not summary:
            missing_summary.append(rel)

        if not bloom:
            missing_bloom.append(rel)

        layer = layer_of_path(rel)
        if layer:
            basename_layers[basename_no_number(rel)][layer].append(rel)

        # redirect stub target validity
        if re.search(r"本文件为(?:学习入口 stub|重定向 stub)", text, re.IGNORECASE):
            target_match = STUB_TARGET_RE.search(text)
            if target_match:
                target = os.path.join(ROOT, "concept", target_match.group(1) + ".md")
                if not os.path.exists(target):
                    invalid_stub_targets.append((rel, target_match.group(1) + ".md"))
            else:
                invalid_stub_targets.append((rel, "<target not detected>"))

    # duplicate EN titles (exclude README/Table of Contents)
    duplicate_en = {
        k: v for k, v in en_map.items() if len(v) > 1 and k not in ("readme", "table of contents")
    }
    if duplicate_en:
        issues["duplicate_en"] = duplicate_en

    if missing_bloom:
        issues["missing_bloom"] = missing_bloom
    if missing_summary:
        issues["missing_summary"] = missing_summary

    # scattered topics: same basename in 3+ distinct layers
    scattered = {
        k: dict(v)
        for k, v in basename_layers.items()
        if len(v) >= 3 and k not in ("README", "SUMMARY", "")
    }
    if scattered:
        issues["scattered_topics"] = scattered

    if invalid_stub_targets:
        issues["invalid_stub_targets"] = invalid_stub_targets

    # report
    date_str = datetime.datetime.now().strftime("%Y-%m-%d")
    md_path = os.path.join(ROOT, f"reports/TAXONOMY_QUALITY_BASELINE_{date_str}.md")
    json_path = os.path.join(ROOT, f"reports/TAXONOMY_QUALITY_BASELINE_{date_str}.json")

    lines = [
        "# Taxonomy Quality Baseline",
        "",
        f"**Date**: {date_str}  ",
        f"**Scanned**: {len(files)} concept/ files",
        "",
        "## Summary",
        "",
    ]

    total_issue_files = sum(
        len(v) if isinstance(v, list) else len(v)
        for v in issues.values()
    )
    lines.append(f"- Duplicate EN titles: {len(duplicate_en)} groups")
    lines.append(f"- Missing Bloom: {len(missing_bloom)} files")
    lines.append(f"- Missing Summary: {len(missing_summary)} files")
    lines.append(f"- Scattered topics (≥3 layers): {len(scattered)} groups")
    lines.append(f"- Invalid stub targets: {len(invalid_stub_targets)} files")
    lines.append("")

    if not issues:
        lines.append("✅ All taxonomy checks passed.")
    else:
        lines.append("## Details")
        lines.append("")
        for category, data in issues.items():
            lines.append(f"### {category}")
            lines.append("")
            if category == "duplicate_en":
                for title, paths in data.items():
                    lines.append(f"- `{title}`: {len(paths)} files")
                    for p in paths:
                        lines.append(f"  - `{p}`")
            elif category == "scattered_topics":
                for base, layer_map in data.items():
                    lines.append(f"- `{base}` across {len(layer_map)} layers")
                    for layer, paths in layer_map.items():
                        lines.append(f"  - {layer}: {', '.join(paths)}")
            elif category == "invalid_stub_targets":
                for rel, target in data:
                    lines.append(f"- `{rel}` -> `{target}`")
            else:
                for p in data:
                    lines.append(f"- `{p}`")
            lines.append("")

    with open(md_path, "w", encoding="utf-8") as f:
        f.write("\n".join(lines) + "\n")

    serializable_issues = {}
    for k, v in issues.items():
        if k == "invalid_stub_targets":
            serializable_issues[k] = [{"file": a, "target": b} for a, b in v]
        elif k == "scattered_topics":
            serializable_issues[k] = {base: {layer: paths for layer, paths in lm.items()} for base, lm in v.items()}
        else:
            serializable_issues[k] = v

    with open(json_path, "w", encoding="utf-8") as f:
        json.dump(
            {
                "date": date_str,
                "scanned": len(files),
                "issues": serializable_issues,
            },
            f,
            ensure_ascii=False,
            indent=2,
        )

    print(f"Scanned {len(files)} files.")
    print(f"Duplicate EN groups: {len(duplicate_en)}")
    print(f"Missing Bloom: {len(missing_bloom)}")
    print(f"Missing Summary: {len(missing_summary)}")
    print(f"Scattered topics: {len(scattered)}")
    print(f"Invalid stub targets: {len(invalid_stub_targets)}")
    print(f"Report: {md_path}")

    if args.strict and issues:
        print("\n❌ Taxonomy issues found.")
        raise SystemExit(1)
    print("\n✅ Taxonomy quality OK.")


if __name__ == "__main__":
    main()
