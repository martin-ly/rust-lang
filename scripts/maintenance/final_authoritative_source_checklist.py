#!/usr/bin/env python3
"""
Final authoritative-source coverage checklist for docs/research_notes/.

Groups Markdown files by concept family (概念族) and checks quality gates:
    * P0 official-source coverage = 100%
    * P1 academic-source coverage >= 95%
    * P2 community-source coverage >= 95%
    * P0+P1+P2 full-stack coverage >= 90%
    * Every file has concept-family metadata
    * Every file has an authority-source marker ("> **来源:**" or "> **权威来源**:")

Usage:
    python scripts/maintenance/final_authoritative_source_checklist.py [--target=all|p1|p2]

This is an informational tool: it always exits with code 0.
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Iterable

PROJECT_ROOT = Path(__file__).resolve().parents[2]
RESEARCH_NOTES = PROJECT_ROOT / "docs" / "research_notes"

# Authority-source marker patterns.
AUTHORITY_MARKER_RE = re.compile(r">\s*\*\*(来源|权威来源)\*\*[:：]")

# Reuse the same tier classification logic as the coverage dashboard so that
# the final checklist and the dashboard report identical numbers.
sys.path.insert(0, str(PROJECT_ROOT / "scripts" / "maintenance"))
from authority_coverage_dashboard import (
    extract_concept_family,
    extract_urls,
    iter_md_files,
    pct,
    tier_coverage,
)


class FileInfo:
    """Per-file analysis result."""

    def __init__(self, path: Path, family: str | None, has_marker: bool, levels: set[str]):
        self.path = path
        self.family = family
        self.has_marker = has_marker
        self.levels = levels

    @property
    def has_family(self) -> bool:
        return self.family is not None


def analyze_file(path: Path) -> FileInfo:
    """Extract concept family, authority markers, and source tiers from a file."""
    text = path.read_text(encoding="utf-8", errors="ignore")

    family = extract_concept_family(text)
    has_marker = bool(AUTHORITY_MARKER_RE.search(text))
    coverage = tier_coverage(extract_urls(text))

    return FileInfo(
        path.relative_to(PROJECT_ROOT),
        family,
        has_marker,
        {tier for tier, covered in coverage.items() if covered},
    )


def build_family_map(files: Iterable[FileInfo]) -> dict[str, list[FileInfo]]:
    """Group files by concept family. Files without a family go to a sentinel bucket."""
    families: dict[str, list[FileInfo]] = defaultdict(list)
    for info in files:
        key = info.family if info.family else "(未指定概念族)"
        families[key].append(info)
    return dict(families)


def threshold_ok(part: int, total: int, threshold: float) -> bool:
    """Check whether part/total meets the threshold (inclusive)."""
    if total == 0:
        return True
    return pct(part, total) + 1e-9 >= threshold


def file_list(items: list[FileInfo], limit: int = 20) -> str:
    """Format a limited list of file paths."""
    lines = [f"    - {info.path.as_posix()}" for info in items[:limit]]
    if len(items) > limit:
        lines.append(f"    - ... and {len(items) - limit} more")
    return "\n".join(lines)


def recommend(action: str, items: list[FileInfo]) -> str:
    """Return a recommendation line with supporting file list."""
    if not items:
        return ""
    return f"  推荐操作: {action}\n{file_list(items)}"


def evaluate_family(name: str, items: list[FileInfo], target: str) -> list[str]:
    """Return a list of failure descriptions for a concept family."""
    failures: list[str] = []
    total = len(items)

    missing_family = [info for info in items if not info.has_family]
    missing_marker = [info for info in items if not info.has_marker]
    p0_files = [info for info in items if "P0" in info.levels]
    p1_files = [info for info in items if "P1" in info.levels]
    p2_files = [info for info in items if "P2" in info.levels]
    all3_files = [info for info in items if {"P0", "P1", "P2"} <= info.levels]

    if missing_family:
        failures.append(
            recommend(
                "为下列文件补充 '> **概念族**: <名称>' 元信息",
                missing_family,
            )
        )

    if missing_marker:
        failures.append(
            recommend(
                "为下列文件补充 '> **来源:**' 或 '> **权威来源**: <链接>' 标记",
                missing_marker,
            )
        )

    check_p0 = target == "all"
    check_p1 = target in ("all", "p1")
    check_p2 = target in ("all", "p2")
    check_all3 = target == "all"

    if check_p0 and len(p0_files) != total:
        failures.append(
            f"  P0 官方来源覆盖率 {pct(len(p0_files), total):.1f}% 未达 100% "
            f"({len(p0_files)}/{total})\n"
            + recommend(
                "为下列文件补充 P0 官方来源（doc.rust-lang.org、rust-lang GitHub、官方博客等）",
                [info for info in items if "P0" not in info.levels],
            )
        )

    if check_p1 and not threshold_ok(len(p1_files), total, 95.0):
        failures.append(
            f"  P1 学术来源覆盖率 {pct(len(p1_files), total):.1f}% 未达 ≥95% "
            f"({len(p1_files)}/{total})\n"
            + recommend(
                "为下列文件补充 P1 学术来源（POPL/PLDI 论文、arXiv、ACM/IEEE/Springer 等）",
                [info for info in items if "P1" not in info.levels],
            )
        )

    if check_p2 and not threshold_ok(len(p2_files), total, 95.0):
        failures.append(
            f"  P2 社区来源覆盖率 {pct(len(p2_files), total):.1f}% 未达 ≥95% "
            f"({len(p2_files)}/{total})\n"
            + recommend(
                "为下列文件补充 P2 社区来源（Rust API Guidelines、this-week-in-rust、生态文档等）",
                [info for info in items if "P2" not in info.levels],
            )
        )

    if check_all3 and not threshold_ok(len(all3_files), total, 90.0):
        failures.append(
            f"  P0+P1+P2 全层级覆盖率 {pct(len(all3_files), total):.1f}% 未达 ≥90% "
            f"({len(all3_files)}/{total})\n"
            + recommend(
                "为下列文件同时补充 P0、P1、P2 三个层级的权威来源",
                [info for info in items if {"P0", "P1", "P2"} - info.levels],
            )
        )

    return failures


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Final authoritative-source coverage checklist for docs/research_notes/."
    )
    parser.add_argument(
        "--target",
        choices=["all", "p1", "p2"],
        default="all",
        help="Coverage tier to check: all (default), p1, or p2.",
    )
    args = parser.parse_args(argv)
    target: str = args.target

    files = [analyze_file(p) for p in iter_md_files()]
    families = build_family_map(files)

    header = f"docs/12_research_notes 权威来源对齐最终覆盖率检查清单 (target={target})"
    print("=" * 72)
    print(header)
    print("=" * 72)
    print(f"扫描文件数: {len(files)}")
    print(f"概念族数: {len(families)}")
    print()

    failed_families: list[tuple[str, list[FileInfo], list[str]]] = []
    passed_count = 0

    for name in sorted(families):
        items = families[name]
        failures = evaluate_family(name, items, target)
        if failures:
            failed_families.append((name, items, failures))
        else:
            passed_count += 1

    for name, items, failures in failed_families:
        print(f"\n❌ 概念族: {name} ({len(items)} 个文件)")
        for failure in failures:
            print(failure)

    print("\n" + "=" * 72)
    print("汇总")
    print("=" * 72)
    print(f"  达标概念族: {passed_count}/{len(families)}")
    print(f"  未达标概念族: {len(failed_families)}/{len(families)}")
    print(f"  总文件数: {len(files)}")
    if target == "all":
        print("  检查门禁: P0=100%, P1≥95%, P2≥95%, P0+P1+P2≥90%, 概念族元信息, 权威来源标记")
    elif target == "p1":
        print("  检查门禁: P1≥95%, 概念族元信息, 权威来源标记")
    elif target == "p2":
        print("  检查门禁: P2≥95%, 概念族元信息, 权威来源标记")
    print("=" * 72)

    # Informational tool: always return 0.
    return 0


if __name__ == "__main__":
    sys.exit(main())
