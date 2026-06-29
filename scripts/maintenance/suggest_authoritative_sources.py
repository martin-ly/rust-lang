#!/usr/bin/env python3
"""
Suggest authoritative source completions for docs/research_notes.

Reads all Markdown files under docs/research_notes/, groups them by concept
family (概念族), determines which P0/P1/P2 authority tiers are missing in each
file, and recommends authoritative source links based on concept-family
keywords.

The script is informational and always exits with code 0.

Usage:
    python scripts/maintenance/suggest_authoritative_sources.py
    python scripts/maintenance/suggest_authoritative_sources.py --output=suggestions.md
"""

from __future__ import annotations

import argparse
import re
import sys
from collections import defaultdict
from dataclasses import dataclass
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


@dataclass(frozen=True)
class SourceSuggestion:
    """A single authoritative source suggestion."""

    tier: str
    name: str
    url: str
    note: str = ""


# Map concept-family keywords (matched as substrings) to tiered suggestions.
# Keep the order from the task description.
KEYWORD_SUGGESTIONS: list[tuple[list[str], list[SourceSuggestion]]] = [
    (
        ["所有权", "借用", "生命周期"],
        [
            SourceSuggestion("P1", "RustBelt", "https://plv.mpi-sws.org/rustbelt/popl18/"),
            SourceSuggestion("P1", "Stacked Borrows", "https://plv.mpi-sws.org/rustbos/"),
            SourceSuggestion("P1", "Tree Borrows", "https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html"),
            SourceSuggestion("P0", "TRPL Ch4", "https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html"),
            SourceSuggestion("P0", "Rust Reference", "https://doc.rust-lang.org/reference/"),
        ],
    ),
    (
        ["类型系统", "型变", "泛型", "Trait"],
        [
            SourceSuggestion("P1", "RustSEM", "https://link.springer.com/article/10.1007/s10703-024-00460-3"),
            SourceSuggestion("P1", "Oxide", "https://arxiv.org/abs/1903.00982"),
            SourceSuggestion("P0", "TRPL Ch10", "https://doc.rust-lang.org/book/ch10-00-generics.html"),
            SourceSuggestion("P0", "Rust Reference Types", "https://doc.rust-lang.org/reference/types.html"),
        ],
    ),
    (
        ["并发", "异步", "Send/Sync", "Future", "Pin"],
        [
            SourceSuggestion("P1", "RustBelt", "https://plv.mpi-sws.org/rustbelt/popl18/"),
            SourceSuggestion("P2", "Tokio Docs", "https://docs.rs/tokio/latest/tokio/"),
            SourceSuggestion("P0", "Async Book", "https://rust-lang.github.io/async-book/"),
            SourceSuggestion("P0", "TRPL Ch16", "https://doc.rust-lang.org/book/ch16-00-concurrency.html"),
        ],
    ),
    (
        ["unsafe", "FFI", "内存", "UB", "Unsafe"],
        [
            SourceSuggestion("P0", "Unsafe Code Guidelines", "https://rust-lang.github.io/unsafe-code-guidelines/"),
            SourceSuggestion("P0", "Rustonomicon", "https://doc.rust-lang.org/nomicon/"),
            SourceSuggestion("P1", "RustSEM", "https://link.springer.com/article/10.1007/s10703-024-00460-3"),
        ],
    ),
    (
        ["模块", "module", "use 路径", "crate-type"],
        [
            SourceSuggestion("P0", "RFC 2126", "https://rust-lang.github.io/rfcs/2126-path-clarity.html"),
            SourceSuggestion("P0", "Rust Reference Modules", "https://doc.rust-lang.org/reference/items/modules.html"),
        ],
    ),
    (
        ["设计模式", "惯用法", "反模式"],
        [
            SourceSuggestion("P2", "Rust Design Patterns", "https://rust-unofficial.github.io/patterns/"),
            SourceSuggestion("P2", "Refactoring Guru", "https://refactoring.guru/"),
        ],
    ),
    (
        ["Crate 架构", "workspace", "public/private API", "SemVer", "API 稳定性"],
        [
            SourceSuggestion("P2", "Rust API Guidelines", "https://rust-lang.github.io/api-guidelines/"),
            SourceSuggestion("P2", "Rust Design Patterns", "https://rust-unofficial.github.io/patterns/"),
        ],
    ),
    (
        ["数据库", "存储", "云原生", "diesel", "sqlx", "kube-rs"],
        [
            SourceSuggestion("P2", "diesel.rs", "https://diesel.rs/"),
            SourceSuggestion("P2", "sqlx", "https://github.com/launchbadge/sqlx"),
            SourceSuggestion("P2", "kube-rs", "https://kube.rs/"),
            SourceSuggestion("P2", "Kubernetes docs", "https://kubernetes.io/docs/"),
        ],
    ),
    (
        ["CI/CD", "供应链", "cargo-audit", "Sigstore", "SLSA"],
        [
            SourceSuggestion("P2", "cargo-audit / RustSec", "https://github.com/rustsec/rustsec"),
            SourceSuggestion("P2", "Sigstore", "https://www.sigstore.dev/"),
            SourceSuggestion("P2", "SLSA", "https://slsa.dev/"),
        ],
    ),
    (
        ["性能", "测试", "benchmark", "Criterion", "Miri"],
        [
            SourceSuggestion("P2", "Rust Performance Book", "https://nnethercote.github.io/perf-book/"),
            SourceSuggestion("P2", "Criterion.rs", "https://github.com/bheisler/criterion.rs"),
            SourceSuggestion("P2", "Miri", "https://github.com/rust-lang/miri"),
        ],
    ),
    (
        ["学习", "面试", "教程", "Rustlings"],
        [
            SourceSuggestion("P0", "The Rust Programming Language", "https://doc.rust-lang.org/book/"),
            SourceSuggestion("P0", "Rust By Example", "https://doc.rust-lang.org/rust-by-example/"),
            SourceSuggestion("P2", "Rustlings", "https://github.com/rust-lang/rustlings"),
        ],
    ),
]

GENERIC_SUGGESTIONS: list[SourceSuggestion] = [
    SourceSuggestion("P0", "Rust Reference", "https://doc.rust-lang.org/reference/"),
    SourceSuggestion("P0", "The Rust Programming Language", "https://doc.rust-lang.org/book/"),
    SourceSuggestion("P1", "RustBelt", "https://plv.mpi-sws.org/rustbelt/popl18/"),
    SourceSuggestion("P2", "Rust Design Patterns", "https://rust-unofficial.github.io/patterns/"),
]


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


def match_suggestions(family: str) -> tuple[list[str], list[SourceSuggestion]]:
    """Return matched keywords and aggregated tiered suggestions for a family."""
    matched_keywords: list[str] = []
    suggestions: list[SourceSuggestion] = []
    seen: set[tuple[str, str]] = set()

    for keywords, sources in KEYWORD_SUGGESTIONS:
        for kw in keywords:
            if kw in family:
                matched_keywords.append(kw)
                for src in sources:
                    key = (src.tier, src.name)
                    if key not in seen:
                        seen.add(key)
                        suggestions.append(src)
                break  # Only add once per keyword group.

    if not suggestions:
        suggestions = GENERIC_SUGGESTIONS

    return matched_keywords, suggestions


def suggestions_for_missing_tiers(
    missing: list[str], suggestions: list[SourceSuggestion]
) -> list[SourceSuggestion]:
    """
    Return suggestions whose tier is in the missing tier list.

    If a missing tier has no keyword-matched suggestion, fall back to the
    generic suggestion for that tier so the recommendation remains actionable.
    """
    result: list[SourceSuggestion] = []
    seen: set[tuple[str, str]] = set()
    for tier in missing:
        tier_suggestions = [s for s in suggestions if s.tier == tier]
        if not tier_suggestions:
            tier_suggestions = [s for s in GENERIC_SUGGESTIONS if s.tier == tier]
        for s in tier_suggestions:
            key = (s.tier, s.name)
            if key not in seen:
                seen.add(key)
                result.append(s)
    return result


def format_source(source: SourceSuggestion) -> str:
    note = f" — {source.note}" if source.note else ""
    return f"[{source.name}]({source.url}){note}"


def analyze() -> tuple[dict[str, dict[str, object]], dict[str, object]]:
    files = iter_md_files()
    families: dict[str, list[dict[str, object]]] = defaultdict(list)
    unclassified: list[str] = []

    for f in files:
        content = f.read_text(encoding="utf-8", errors="ignore")
        family = extract_concept_family(content)
        urls = extract_urls(content)
        coverage = tier_coverage(urls)
        missing = [tier for tier, has in coverage.items() if not has]
        record: dict[str, object] = {
            "path": f.relative_to(PROJECT_ROOT).as_posix(),
            "coverage": coverage,
            "missing": missing,
            "has_gaps": bool(missing),
        }
        if family is None:
            unclassified.append(record["path"])
        else:
            families[family].append(record)

    family_reports: dict[str, dict[str, object]] = {}
    for family in sorted(families):
        records = families[family]
        matched_keywords, suggestions = match_suggestions(family)
        gap_records = [r for r in records if r["has_gaps"]]
        family_reports[family] = {
            "file_count": len(records),
            "gap_count": len(gap_records),
            "matched_keywords": matched_keywords,
            "suggestions": suggestions,
            "files": gap_records,
        }

    all_classified = [r for records in families.values() for r in records]
    total_gaps = sum(1 for r in all_classified if r["has_gaps"])
    tier_gap_counts = {
        "P0": sum(1 for r in all_classified if not r["coverage"]["P0"]),
        "P1": sum(1 for r in all_classified if not r["coverage"]["P1"]),
        "P2": sum(1 for r in all_classified if not r["coverage"]["P2"]),
    }

    overall = {
        "total_files": len(files),
        "classified_files": len(all_classified),
        "unclassified_files": len(unclassified),
        "unclassified_paths": unclassified,
        "total_gap_files": total_gaps,
        "tier_gap_counts": tier_gap_counts,
    }

    return family_reports, overall


def render_markdown(
    family_reports: dict[str, dict[str, object]], overall: dict[str, object]
) -> str:
    lines: list[str] = []
    lines.append("# docs/research_notes 权威来源自动补全建议\n")
    lines.append("## 总体摘要\n")
    lines.append(f"- **总 Markdown 文件数**：{overall['total_files']}")
    lines.append(f"- **已分类文件数**：{overall['classified_files']}")
    lines.append(f"- **未分类文件数**：{overall['unclassified_files']}")
    lines.append(f"- **存在权威来源缺口的文件数**：{overall['total_gap_files']}")
    lines.append("")
    lines.append("| 层级 | 缺少该层级的文件数 |")
    lines.append("|------|-------------------:|")
    for tier in ("P0", "P1", "P2"):
        count = overall["tier_gap_counts"][tier]
        lines.append(f"| {tier} | {count} |")
    lines.append("")
    lines.append(
        "说明：本报告为信息性工具，基于 `scripts/maintenance/authority_coverage_dashboard.py` "
        "的 P0/P1/P2 域名定义与概念族元信息生成，退出码始终为 0。"
    )
    lines.append("")

    gap_families = {
        family: data
        for family, data in family_reports.items()
        if data["gap_count"]
    }

    lines.append("## 按概念族分组\n")
    if not gap_families:
        lines.append("✅ 所有文件均覆盖 P0/P1/P2 三个层级的权威来源，暂无补全建议。")
        lines.append("")

    for family in sorted(gap_families):
        data = gap_families[family]
        lines.append(f"### {family}\n")

        matched = data["matched_keywords"]
        if matched:
            lines.append(f"**检测关键词**：{', '.join(matched)}")
        else:
            lines.append("**检测关键词**：*未命中专用关键词，使用通用推荐*")
        lines.append("")

        suggestions: list[SourceSuggestion] = data["suggestions"]
        by_tier: dict[str, list[SourceSuggestion]] = defaultdict(list)
        for src in suggestions:
            by_tier[src.tier].append(src)

        lines.append("**推荐权威来源**：")
        for tier in ("P0", "P1", "P2"):
            if by_tier[tier]:
                src_list = "；".join(format_source(s) for s in by_tier[tier])
                lines.append(f"- **{tier}**：{src_list}")
        lines.append("")

        lines.append(f"**缺口文件数**：{data['gap_count']} / {data['file_count']}")
        lines.append("")
        lines.append("| 文件 | 缺少层级 | 建议补充来源 |")
        lines.append("|------|----------|--------------|")

        files: list[dict[str, object]] = data["files"]
        for record in sorted(files, key=lambda r: r["path"]):
            missing: list[str] = record["missing"]
            missing_str = ", ".join(missing)
            relevant = suggestions_for_missing_tiers(missing, suggestions)
            src_str = "；".join(format_source(s) for s in relevant)
            lines.append(f"| `{record['path']}` | {missing_str} | {src_str} |")
        lines.append("")

    if overall["unclassified_files"]:
        lines.append("## 未分类文件（缺少概念族元信息）\n")
        for p in overall["unclassified_paths"]:
            lines.append(f"- `{p}`")
        lines.append("")

    return "\n".join(lines)


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="docs/research_notes 权威来源自动补全建议工具。"
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
    family_reports, overall = analyze()
    report = render_markdown(family_reports, overall)

    if args.output:
        output_path = Path(args.output)
        output_path.write_text(report, encoding="utf-8")
        print(f"报告已写入：{output_path.resolve()}")
    else:
        print(report)

    return 0


if __name__ == "__main__":
    sys.exit(main())
