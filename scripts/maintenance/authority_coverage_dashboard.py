#!/usr/bin/env python3
"""
Authority source coverage dashboard for docs/research_notes.

Reads all Markdown files under docs/research_notes/, groups them by concept
family (概念族), and produces a Markdown table with the following metrics:

- Number of files per family.
- Percentage of files citing P0 official sources.
- Percentage of files citing P1 academic/formal sources.
- Percentage of files citing P2 community/ecosystem sources.
- Percentage of files citing P0+P1+P2 sources together.
- Number of files lacking any P0/P1/P2 authoritative source marker.

The script is informational and always exits with code 0.

Usage:
    python scripts/maintenance/authority_coverage_dashboard.py
    python scripts/maintenance/authority_coverage_dashboard.py --output=coverage.md
"""

from __future__ import annotations

import argparse
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


def pct(part: int, total: int) -> float:
    return round(part / total * 100, 1) if total else 0.0


def analyze() -> tuple[dict[str, dict[str, object]], dict[str, object]]:
    files = iter_md_files()
    families: dict[str, list[dict[str, object]]] = defaultdict(list)
    unclassified: list[str] = []

    for f in files:
        content = f.read_text(encoding="utf-8", errors="ignore")
        family = extract_concept_family(content)
        urls = extract_urls(content)
        coverage = tier_coverage(urls)
        record: dict[str, object] = {
            "path": f.relative_to(PROJECT_ROOT).as_posix(),
            "coverage": coverage,
            "has_any_authority": any(coverage.values()),
        }
        if family is None:
            unclassified.append(record["path"])
        else:
            families[family].append(record)

    # Build family-level aggregated metrics.
    family_rows: dict[str, dict[str, object]] = {}
    for family in sorted(families):
        records = families[family]
        total = len(records)
        p0_count = sum(1 for r in records if r["coverage"]["P0"])
        p1_count = sum(1 for r in records if r["coverage"]["P1"])
        p2_count = sum(1 for r in records if r["coverage"]["P2"])
        all_three_count = sum(
            1 for r in records if all(r["coverage"].values())
        )
        missing_count = sum(1 for r in records if not r["has_any_authority"])

        family_rows[family] = {
            "file_count": total,
            "P0_count": p0_count,
            "P1_count": p1_count,
            "P2_count": p2_count,
            "all_three_count": all_three_count,
            "missing_count": missing_count,
            "P0_pct": pct(p0_count, total),
            "P1_pct": pct(p1_count, total),
            "P2_pct": pct(p2_count, total),
            "all_three_pct": pct(all_three_count, total),
        }

    # Overall totals across all classified files.
    all_classified = [r for records in families.values() for r in records]
    total_classified = len(all_classified)
    total_p0 = sum(1 for r in all_classified if r["coverage"]["P0"])
    total_p1 = sum(1 for r in all_classified if r["coverage"]["P1"])
    total_p2 = sum(1 for r in all_classified if r["coverage"]["P2"])
    total_all_three = sum(1 for r in all_classified if all(r["coverage"].values()))
    total_missing = sum(1 for r in all_classified if not r["has_any_authority"])

    overall = {
        "total_files": len(files),
        "classified_files": total_classified,
        "unclassified_files": len(unclassified),
        "unclassified_paths": unclassified,
        "P0_count": total_p0,
        "P1_count": total_p1,
        "P2_count": total_p2,
        "all_three_count": total_all_three,
        "missing_count": total_missing,
        "P0_pct": pct(total_p0, total_classified),
        "P1_pct": pct(total_p1, total_classified),
        "P2_pct": pct(total_p2, total_classified),
        "all_three_pct": pct(total_all_three, total_classified),
    }

    return family_rows, overall


def render_markdown(
    family_rows: dict[str, dict[str, object]], overall: dict[str, object]
) -> str:
    lines: list[str] = []
    lines.append("# docs/research_notes 权威来源覆盖率仪表板\n")
    lines.append(
        f"- **总 Markdown 文件数**：{overall['total_files']}"
    )
    lines.append(
        f"- **已分类文件数**：{overall['classified_files']}"
    )
    lines.append(
        f"- **未分类文件数**：{overall['unclassified_files']}"
    )
    lines.append("")
    lines.append("## 总体指标\n")
    lines.append("| 指标 | 计数 | 比例 |")
    lines.append("|------|-----:|-----:|")
    lines.append(
        f"| 含 P0 官方来源 | {overall['P0_count']} | {overall['P0_pct']}% |"
    )
    lines.append(
        f"| 含 P1 学术来源 | {overall['P1_count']} | {overall['P1_pct']}% |"
    )
    lines.append(
        f"| 含 P2 社区来源 | {overall['P2_count']} | {overall['P2_pct']}% |"
    )
    lines.append(
        f"| 同时含 P0+P1+P2 | {overall['all_three_count']} | {overall['all_three_pct']}% |"
    )
    lines.append(
        f"| 缺少权威来源标记 | {overall['missing_count']} | - |"
    )
    lines.append("")
    lines.append("## 按概念族分组\n")
    lines.append(
        "| 概念族 | 文件总数 | P0 官方% | P1 学术% | P2 社区% | P0+P1+P2% | 缺少权威来源 |"
    )
    lines.append(
        "|--------|---------:|---------:|---------:|---------:|----------:|-------------:|"
    )

    for family, row in sorted(family_rows.items()):
        lines.append(
            f"| {family} | {row['file_count']} | {row['P0_pct']}% | "
            f"{row['P1_pct']}% | {row['P2_pct']}% | {row['all_three_pct']}% | "
            f"{row['missing_count']} |"
        )

    if not family_rows:
        lines.append("| *暂无分类数据* | - | - | - | - | - | - |")

    if overall["unclassified_files"]:
        lines.append("")
        lines.append("## 未分类文件（缺少概念族元信息）\n")
        for p in overall["unclassified_paths"]:
            lines.append(f"- `{p}`")

    lines.append("")
    lines.append(
        "说明：本仪表板为信息性工具，P0/P1/P2 域名定义参考 "
        "`scripts/maintenance/check_authoritative_source_gaps.py`。"
    )
    return "\n".join(lines)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="权威来源覆盖率仪表板（docs/research_notes）。"
    )
    parser.add_argument(
        "--output",
        type=str,
        default=None,
        help="可选：将 Markdown 报告输出到指定文件路径。",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    family_rows, overall = analyze()
    report = render_markdown(family_rows, overall)

    if args.output:
        output_path = Path(args.output)
        output_path.write_text(report, encoding="utf-8")
        print(f"报告已写入：{output_path.resolve()}")
    else:
        print(report)

    return 0


if __name__ == "__main__":
    sys.exit(main())
