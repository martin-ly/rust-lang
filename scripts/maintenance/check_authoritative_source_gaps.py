#!/usr/bin/env python3
"""
Check docs/12_research_notes authoritative source coverage gaps.

Reads all Markdown files under docs/12_research_notes/, groups them by concept
family (概念族), and reports:
- Number of files per concept family.
- Percentage of files in each family that reference P0/P1/P2 authority URLs.
- Which concept families are missing P0/P1/P2 source coverage.

This script is informational and always exits with code 0.

Usage:
    python scripts/maintenance/check_authoritative_source_gaps.py
"""

from __future__ import annotations

import re
import sys
from collections import defaultdict
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[2]
RESEARCH_NOTES = PROJECT_ROOT / "docs" / "research_notes"

# Authority URL tiers. Domains are matched as substrings.
P0_DOMAINS = [
    r"doc\.rust-lang\.org",
    r"rust-lang\.github\.io",
    r"github\.com/rust-lang",
    r"rustc-dev-guide\.rust-lang\.org",
    r"spec\.ferrocene\.dev",
    r"error_codes/error-index\.html",
]

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

P2_DOMAINS = [
    r"rust-unofficial\.github\.io",
    r"nnethercote\.github\.io",
    r"this-week-in-rust\.org",
    r"blog\.rust-lang\.org",
    r"github\.com/verus-lang",
    r"github\.com/model-checking",
    r"github\.com/creusot-rs",
    r"github\.com/formal-land",
    r"github\.com/AeneasVerif",
    # Community/ecosystem sources used by counterexample boundary files.
    r"microservices\.io",
    r"refactoring\.guru",
    r"pragprog\.com",
    r"docs\.rs/tokio",
    r"docs\.rs",
    r"crates\.io",
    # Database / storage / cloud-native ecosystem.
    r"diesel\.rs",
    r"github\.com/launchbadge",
    r"sea-ql\.org",
    r"github\.com/rusqlite",
    r"github\.com/redis-rs",
    r"github\.com/mongodb",
    r"github\.com/tokio-rs/mini-redis",
    r"github\.com/spacejam/sled",
    r"github\.com/fede1024/rust-rdkafka",
    r"github\.com/amqp-rs/lapin",
    r"github\.com/nats-io/nats\.rs",
    r"kube\.rs",
    r"github\.com/open-telemetry",
    r"github\.com/prometheus",
    r"github\.com/envoyproxy",
    r"kubernetes\.io",
    r"docs\.docker\.com",
    # Web/network/error-handling ecosystem.
    r"github\.com/hyperium",
    r"github\.com/tower-rs",
    r"github\.com/actix",
    r"github\.com/SergioBenitez",
    r"github\.com/tokio-rs/axum",
    r"github\.com/quinn-rs",
    r"github\.com/dtolnay",
    r"github\.com/EmbarkStudios",
    # CI/CD / supply-chain security.
    r"github\.com/rustsec",
    r"sigstore\.dev",
    r"slsa\.dev",
    r"spdx\.dev",
]

CONCEPT_FAMILY_RE = re.compile(r">\s*\*\*概念族\*\*[:：]\s*(.+)")
LINK_RE = re.compile(r"!?\[[^\]]*\]\(([^)]+)\)")


def iter_md_files() -> list[Path]:
    return sorted(RESEARCH_NOTES.rglob("*.md"))


def extract_concept_family(content: str) -> str | None:
    match = CONCEPT_FAMILY_RE.search(content)
    if not match:
        return None
    family = match.group(1).strip()
    # Remove trailing Markdown formatting characters (e.g. punctuation).
    family = re.sub(r"[\|\[\]\(\)\*]+$", "", family).strip()
    return family or None


def extract_urls(content: str) -> set[str]:
    """Return all URLs referenced in Markdown links inside the content."""
    urls: set[str] = set()
    for m in LINK_RE.finditer(content):
        link = m.group(1)
        if link.startswith("http"):
            urls.add(link.split("#")[0].split("?")[0])
    return urls


def tier_coverage(urls: set[str]) -> dict[str, bool]:
    """Return which tiers are covered by the given URL set."""
    text = " ".join(urls)
    return {
        "P0": any(re.search(domain, text) for domain in P0_DOMAINS),
        "P1": any(re.search(domain, text) for domain in P1_DOMAINS),
        "P2": any(re.search(domain, text) for domain in P2_DOMAINS),
    }


def analyze() -> dict[str, dict[str, object]]:
    files = iter_md_files()
    families: dict[str, list[dict[str, object]]] = defaultdict(list)
    unclassified: list[Path] = []

    for f in files:
        content = f.read_text(encoding="utf-8", errors="ignore")
        family = extract_concept_family(content)
        urls = extract_urls(content)
        coverage = tier_coverage(urls)
        record = {
            "path": f.relative_to(PROJECT_ROOT).as_posix(),
            "urls": urls,
            "coverage": coverage,
        }
        if family is None:
            unclassified.append(f.relative_to(PROJECT_ROOT))
        else:
            families[family].append(record)

    report: dict[str, dict[str, object]] = {
        "_meta": {
            "total_files": len(files),
            "unclassified_files": len(unclassified),
            "unclassified_paths": [p.as_posix() for p in unclassified],
        }
    }

    for family in sorted(families):
        records = families[family]
        total = len(records)
        p0_count = sum(1 for r in records if r["coverage"]["P0"])
        p1_count = sum(1 for r in records if r["coverage"]["P1"])
        p2_count = sum(1 for r in records if r["coverage"]["P2"])
        report[family] = {
            "file_count": total,
            "P0_count": p0_count,
            "P1_count": p1_count,
            "P2_count": p2_count,
            "P0_pct": round(p0_count / total * 100, 1) if total else 0.0,
            "P1_pct": round(p1_count / total * 100, 1) if total else 0.0,
            "P2_pct": round(p2_count / total * 100, 1) if total else 0.0,
            "files": records,
        }

    return report


def print_report(report: dict[str, dict[str, object]]) -> None:
    print("=" * 70)
    print("docs/12_research_notes 权威来源缺口报告")
    print("=" * 70)

    meta = report["_meta"]
    print(f"\n总 Markdown 文件数: {meta['total_files']}")
    print(f"未分类（缺少概念族元信息）文件数: {meta['unclassified_files']}")
    if meta["unclassified_files"]:
        for p in meta["unclassified_paths"][:10]:
            print(f"  ⚠️  {p}")
        if meta["unclassified_files"] > 10:
            print(f"  ... 还有 {meta['unclassified_files'] - 10} 个")

    print("\n" + "-" * 70)
    print(f"{'概念族':<40} {'文件数':>8} {'P0%':>8} {'P1%':>8} {'P2%':>8}")
    print("-" * 70)

    gap_families: dict[str, list[str]] = {"P0": [], "P1": [], "P2": []}

    for family, data in sorted(report.items()):
        if family == "_meta":
            continue
        file_count = data["file_count"]
        p0_pct = data["P0_pct"]
        p1_pct = data["P1_pct"]
        p2_pct = data["P2_pct"]
        print(
            f"{family:<40} {file_count:>8} {p0_pct:>7.1f}% {p1_pct:>7.1f}% {p2_pct:>7.1f}%"
        )

        if p0_pct < 100:
            gap_families["P0"].append(family)
        if p1_pct < 50:
            gap_families["P1"].append(family)
        if p2_pct < 30:
            gap_families["P2"].append(family)

    print("-" * 70)

    print("\n" + "=" * 70)
    print("缺口汇总（信息性）")
    print("=" * 70)

    print("\nP0 官方来源覆盖率未达 100% 的概念族：")
    if gap_families["P0"]:
        for family in gap_families["P0"]:
            print(f"  ⚠️  {family}")
    else:
        print("  ✅ 所有概念族 P0 来源覆盖率均达 100%")

    print("\nP1 学术/形式化来源覆盖率低于 50% 的概念族：")
    if gap_families["P1"]:
        for family in gap_families["P1"]:
            print(f"  ⚠️  {family}")
    else:
        print("  ✅ 所有概念族 P1 来源覆盖率均不低于 50%")

    print("\nP2 社区/生态来源覆盖率低于 30% 的概念族：")
    if gap_families["P2"]:
        for family in gap_families["P2"]:
            print(f"  ⚠️  {family}")
    else:
        print("  ✅ 所有概念族 P2 来源覆盖率均不低于 30%")

    print("\n" + "=" * 70)
    print("说明：本报告仅用于信息展示，不直接影响退出码。")
    print("=" * 70)


def main() -> int:
    report = analyze()
    print_report(report)
    return 0


if __name__ == "__main__":
    sys.exit(main())
