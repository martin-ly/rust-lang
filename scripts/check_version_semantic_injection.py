#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""check_version_semantic_injection.py — 检查 Rust 版本特性是否反向注入 concept/ 权威页。

解析 `concept/07_future/00_version_tracking/rust_1_9[0-7]_stabilized.md` 中的
稳定特性条目（矩阵表第一列或章节标题），提取每条特性，并检查：
  - 版本跟踪页中该特性条目是否包含指向 `concept/` 权威页的链接；或
  - 任一 `concept/` 权威页正文包含回链到该版本跟踪页，并且正文中出现
    该特性的规范化名称（视为 concept/ 主动回注）。

输出覆盖率与未映射列表，支持 `--strict`（覆盖率 < 80% 时 exit 1）和
`--report`（写入 reports/ 基线报告）。
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
VERSION_DIR = ROOT / "concept" / "07_future" / "00_version_tracking"
CONCEPT_DIR = ROOT / "concept"

# 1.90–1.97 stable version tracking pages
VERSION_FILES: list[tuple[str, str]] = [
    ("1.90", "rust_1_90_stabilized.md"),
    ("1.91", "rust_1_91_stabilized.md"),
    ("1.92", "rust_1_92_stabilized.md"),
    ("1.93", "rust_1_93_stabilized.md"),
    ("1.94", "rust_1_94_stabilized.md"),
    ("1.95", "rust_1_95_stabilized.md"),
    ("1.96", "rust_1_96_stabilized.md"),
    ("1.97", "rust_1_97_stabilized.md"),
]

# Regex for markdown links
MD_LINK_RE = re.compile(r"\[([^\]]*)\]\(([^\s)]+)\)")


def normalize_text(text: str) -> str:
    """Strip markdown formatting and punctuation for fuzzy comparison."""
    text = re.sub(r"`+", "", text)
    text = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", text)
    text = re.sub(r"\*+", "", text)
    text = re.sub(r"[（(][^）)]+[）)]", "", text)
    text = re.sub(r"[§0-9.\-/_]", "", text)
    text = re.sub(r"\s+", "", text)
    return text.strip().lower()


def extract_feature_name(cell: str) -> str:
    """Clean a feature name from the first column of a matrix table."""
    cell = cell.strip()
    cell = re.sub(r"^[▲✅❌⭐⚠️]+\s*", "", cell)
    cell = re.sub(r"\s*[（(]§[^）)]+[）)]\s*$", "", cell)
    return cell.strip()


def resolve_link(link_target: str, base_dir: Path) -> Path | None:
    """Resolve a markdown link target relative to base_dir."""
    if link_target.startswith(("http://", "https://", "mailto:", "#")):
        return None
    # Strip fragment
    target = link_target.split("#")[0]
    if not target:
        return None
    try:
        return (base_dir / target).resolve()
    except Exception:
        return None


def is_concept_authority_path(path: Path) -> bool:
    """Check if a resolved path points to a concept/ authority page (not version tracking)."""
    try:
        rel = path.relative_to(CONCEPT_DIR)
    except ValueError:
        return False
    return "00_version_tracking" not in rel.parts


def extract_matrix_features(version: str, filename: str, text: str) -> list[dict]:
    """Extract feature rows from a 4-column feature matrix table."""
    features: list[dict] = []
    in_matrix = False

    for line in text.splitlines():
        stripped = line.strip()
        if "| 特性 " in stripped and "影响面" in stripped:
            in_matrix = True
            continue
        if in_matrix:
            if not stripped.startswith("|"):
                break
            if stripped.replace("|", "").strip().startswith("-"):
                continue
            cells = [c.strip() for c in stripped.strip("|").split("|")]
            if len(cells) < 4:
                continue
            feature = extract_feature_name(cells[0])
            if not feature or feature == "特性" or set(feature) <= {"-", "|", ":"}:
                continue
            features.append({
                "version": version,
                "filename": filename,
                "feature": feature,
                "row": stripped,
            })

    return features


def extract_section_features(version: str, filename: str, text: str) -> list[dict]:
    """For pages without a matrix table (e.g. 1.97), extract numbered section headings."""
    features: list[dict] = []
    heading_re = re.compile(r"^#{1,4}\s+(\d+(?:\.\d+)+)\s+(.+?)$", re.MULTILINE)
    lines = text.splitlines()

    for m in heading_re.finditer(text):
        section = m.group(1)
        title = m.group(2).strip()
        if not title or title.startswith("目录") or title.startswith("练习"):
            continue
        if any(k in title for k in ["权威来源", "国际权威参考", "迁移指南", "兼容性注意", "练习与验证"]):
            continue
        # Include heading and next 2 lines to catch inserted concept links
        line_no = text[:m.start()].count("\n")
        context = "\n".join(lines[line_no:line_no + 3])
        features.append({
            "version": version,
            "filename": filename,
            "feature": f"{title} (§{section})",
            "row": context,
        })

    return features


def extract_features(version: str, filename: str) -> list[dict]:
    path = VERSION_DIR / filename
    if not path.exists():
        return []

    text = path.read_text(encoding="utf-8", errors="replace")
    matrix_features = extract_matrix_features(version, filename, text)
    if matrix_features:
        return matrix_features
    return extract_section_features(version, filename, text)


def find_concept_links_in_row(row: str, version_filename: str) -> list[str]:
    """Find concept/ authority page links in a feature row and return their concept-relative paths."""
    base_dir = VERSION_DIR
    concept_links: list[str] = []
    for m in MD_LINK_RE.finditer(row):
        target = m.group(2)
        resolved = resolve_link(target, base_dir)
        if resolved and is_concept_authority_path(resolved):
            concept_links.append(resolved.relative_to(CONCEPT_DIR).as_posix())
    return concept_links


def find_concept_backlinks(version_filename: str) -> dict[str, dict]:
    """Find concept pages that link back to the given version tracking page."""
    version_link_pattern = re.compile(re.escape(version_filename))
    backlink_map: dict[str, dict] = {}

    for path in CONCEPT_DIR.rglob("*.md"):
        if "00_version_tracking" in path.parts:
            continue
        rel = path.relative_to(CONCEPT_DIR).as_posix()
        text = path.read_text(encoding="utf-8", errors="replace")
        if version_link_pattern.search(text):
            backlink_map[rel] = {
                "path": rel,
                "text": text,
            }

    return backlink_map


def feature_mentioned_in_concept(feature: str, concept_text: str) -> bool:
    """Heuristic: is the feature name mentioned in a concept page?"""
    norm_feature = normalize_text(feature)
    if len(norm_feature) < 6:
        return False
    norm_concept = normalize_text(concept_text)
    return norm_feature in norm_concept or norm_concept in norm_feature


def evaluate() -> dict:
    all_features: list[dict] = []

    for version, filename in VERSION_FILES:
        features = extract_features(version, filename)
        backlinks = find_concept_backlinks(filename)
        for feat in features:
            feat["normalized"] = normalize_text(feat["feature"])
            forward_links = find_concept_links_in_row(feat["row"], filename)
            feat["concept_links"] = list(dict.fromkeys(forward_links))
            forward = bool(forward_links)
            backlink_mentions = list(dict.fromkeys([
                rel for rel, info in backlinks.items()
                if feature_mentioned_in_concept(feat["feature"], info["text"])
            ]))
            feat["backlink_mentions"] = backlink_mentions
            feat["mapped"] = forward or bool(backlink_mentions)
        all_features.extend(features)

    mapped = [f for f in all_features if f["mapped"]]
    unmapped = [f for f in all_features if not f["mapped"]]

    return {
        "total": len(all_features),
        "mapped_count": len(mapped),
        "unmapped_count": len(unmapped),
        "coverage_rate": round(len(mapped) / len(all_features) * 100, 1) if all_features else 0.0,
        "features": all_features,
        "unmapped": unmapped,
    }


def format_report(result: dict, date_str: str) -> str:
    lines = [
        f"# Version Semantic Injection Baseline Report ({date_str})",
        "",
        "> 检查 Rust 1.90–1.97 稳定特性在版本跟踪页与 `concept/` 权威页之间的双向链接覆盖。",
        "",
        "## 汇总",
        "",
        f"- 版本范围：1.90 – 1.97（共 {len(VERSION_FILES)} 个稳定版本）",
        f"- 提取特性数：{result['total']}",
        f"- 已映射：{result['mapped_count']} ({result['coverage_rate']}%)",
        f"- 未映射：{result['unmapped_count']}",
        "",
        "## 未映射特性",
        "",
    ]
    if not result["unmapped"]:
        lines.append("无。所有提取特性均已建立 concept/ 前向链接或存在带特征提及的 concept/ 回链。")
    else:
        for f in result["unmapped"]:
            lines.append(f"- **{f['version']}**: {f['feature']}")
    lines.append("")

    lines.append("## 已映射特性（按版本分组）")
    lines.append("")
    grouped: dict[str, list[dict]] = {}
    for f in result["features"]:
        if f["mapped"]:
            grouped.setdefault(f["version"], []).append(f)
    for version in sorted(grouped):
        lines.append(f"### {version}")
        for f in grouped[version]:
            if f["concept_links"]:
                links = ", ".join(f"`{p}`" for p in f["concept_links"])
                lines.append(f"- {f['feature']} → {links}")
            elif f.get("backlink_mentions"):
                backs = ", ".join(f"`{p}`" for p in f["backlink_mentions"])
                lines.append(f"- {f['feature']} ← {backs}")
        lines.append("")

    lines.append("## 维护说明")
    lines.append("")
    lines.append("- 未映射特性需在版本跟踪页添加指向 `concept/` 权威页的链接，")
    lines.append("  或在对应 concept/ 权威页增加版本兼容性小节并回链版本页。")
    lines.append("- 本脚本逻辑见 `scripts/check_version_semantic_injection.py`。")
    lines.append("")

    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="检查 Rust 1.90–1.97 稳定特性的版本语义注入双向链接覆盖"
    )
    parser.add_argument("--strict", action="store_true", help="覆盖率 < 80%% 时 exit 1")
    parser.add_argument("--json", action="store_true", help="仅输出 JSON 到 stdout")
    parser.add_argument("--report", action="store_true", help="写入 reports/ 基线报告")
    args = parser.parse_args()

    result = evaluate()
    date_str = _dt.datetime.now().strftime("%Y_%m_%d")

    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0

    report = format_report(result, date_str)
    print(report)

    if args.report:
        reports_dir = ROOT / "reports"
        reports_dir.mkdir(exist_ok=True)
        md_path = reports_dir / f"VERSION_SEMANTIC_INJECTION_BASELINE_{date_str}.md"
        json_path = reports_dir / f"VERSION_SEMANTIC_INJECTION_BASELINE_{date_str}.json"
        md_path.write_text(report, encoding="utf-8")
        json_path.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"\n报告已写入：\n  {md_path}\n  {json_path}", file=sys.stderr)

    if args.strict and result["coverage_rate"] < 80.0:
        print(f"\n❌ 覆盖率 {result['coverage_rate']}% < 80%，严格模式失败。", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
