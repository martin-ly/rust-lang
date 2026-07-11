#!/usr/bin/env python3
"""
P2 community source coverage sprint for docs/research_notes.

Appends a "社区权威参考" section to Markdown files that:
- Belong to concept families with P2 coverage gaps (coverage < 100%, including
  families below the 30% threshold reported by check_authoritative_source_gaps.py).
- Are not root hub documents (README.md / INDEX.md).
- Do not already contain any P2 authority URL.
- Do not already have a "## 社区权威参考" section.

The script is idempotent: re-running it skips files already processed.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parents[2]
RESEARCH_NOTES = PROJECT_ROOT / "docs" / "research_notes"
SCRIPT_DIR = PROJECT_ROOT / "scripts" / "maintenance"

# Reuse the analysis logic and P2 domain definitions from the gap checker so
# the sprint stays consistent with the official coverage report.
sys.path.insert(0, str(SCRIPT_DIR))
import check_authoritative_source_gaps as gaps  # noqa: E402

ROOT_HUB_FILES = {"README.md", "INDEX.md"}
SECTION_HEADER = "## 社区权威参考"

P2_CANDIDATES = {
    "patterns": "- [Rust Design Patterns](https://rust-unofficial.github.io/patterns/)",
    "api_guidelines": "- [Rust API Guidelines](https://rust-lang.github.io/api-guidelines/)",
    "twir": "- [This Week in Rust](https://this-week-in-rust.org/)",
    "inside_rust": "- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)",
    "perf": "- [Rust Performance Book](https://nnethercote.github.io/perf-book/)",
    "zh_book": "- [Rust Book 中文](https://kaisery.github.io/trpl-zh-cn/)",
    "zh_community": "- [Rust 中文社区](https://rustcc.cn/)",
}


def is_root_hub(path: Path) -> bool:
    """Return True for canonical root hub documents that should not be modified."""
    return path.parent == RESEARCH_NOTES and path.name in ROOT_HUB_FILES


def select_links(family: str) -> list[str]:
    """Pick 2-4 generic P2 community links based on the concept family topic."""
    f = family.lower()
    links: list[str] = []

    # Design / architecture / patterns families.
    if any(k in f for k in (
        "设计模式", "crate 架构", "api", "软件设计", "组合工程",
        "边界系统", "边界矩阵", "惯用法", "架构", "pattern",
    )):
        links.extend([
            P2_CANDIDATES["patterns"],
            P2_CANDIDATES["api_guidelines"],
            P2_CANDIDATES["twir"],
        ])

    # Performance families.
    if any(k in f for k in ("性能", "perf", "optimization")):
        links.append(P2_CANDIDATES["perf"])

    # Core language / unsafe / concurrency / async / type system / formal methods
    # / RFC / toolchain / authoritative alignment families.
    if any(k in f for k in (
        "unsafe", "ffi", "内存安全", "并发", "send/sync", "异步",
        "future", "pin", "所有权", "借用", "类型系统", "trait",
        "形式化", "证明", "语义", "宏", "rfc", "版本", "工具链",
        "cargo", "edition", "reference", "library", "rustonomicon",
        "unsafe code", "rustc", "ferrocene", "安全", "验证",
    )):
        links.extend([
            P2_CANDIDATES["inside_rust"],
            P2_CANDIDATES["twir"],
        ])

    # i18n / Chinese community / learning / navigation / knowledge graph.
    if any(k in f for k in (
        "国际化", "i18n", "中文", "知识图谱", "索引", "导航",
        "学习资源", "教程", "元/导航",
    )):
        if "国际化" in f or "i18n" in f or "中文" in f:
            links.append(P2_CANDIDATES["zh_book"])
        else:
            links.append(P2_CANDIDATES["zh_community"])
        links.append(P2_CANDIDATES["twir"])

    # Fallback default for any remaining gap families.
    if not links:
        links = [
            P2_CANDIDATES["twir"],
            P2_CANDIDATES["inside_rust"],
            P2_CANDIDATES["zh_community"],
        ]

    # Deduplicate while preserving order, then keep 2-4 items.
    seen: set[str] = set()
    unique: list[str] = []
    for link in links:
        if link not in seen:
            seen.add(link)
            unique.append(link)

    if len(unique) < 2:
        unique = [
            P2_CANDIDATES["twir"],
            P2_CANDIDATES["inside_rust"],
        ]

    return unique[:4]


def has_p2_url(content: str) -> bool:
    """Return True if the content already references a known P2 authority URL."""
    urls = gaps.extract_urls(content)
    return gaps.tier_coverage(urls)["P2"]


def has_community_section(content: str) -> bool:
    """Return True if the file already contains the target section header."""
    return SECTION_HEADER in content


def build_section(family: str) -> str:
    """Build the Markdown snippet to append."""
    lines = ["", SECTION_HEADER, ""]
    lines.extend(select_links(family))
    lines.append("")
    return "\n".join(lines)


def append_section(path: Path, family: str, dry_run: bool = False) -> bool:
    """Append the community authority section to a single file.

    Returns True if the file would be / was modified.
    """
    content = path.read_text(encoding="utf-8", errors="ignore")

    if is_root_hub(path):
        return False
    if has_community_section(content):
        return False
    if has_p2_url(content):
        return False

    if dry_run:
        return True

    section = build_section(family)
    stripped = content.rstrip()

    # If the file already ends with a horizontal rule, append after it so the
    # rule acts as a separator rather than becoming an orphan trailing marker.
    if stripped.endswith("---"):
        new_content = stripped + "\n" + section
    else:
        new_content = stripped + section

    path.write_text(new_content, encoding="utf-8")
    return True


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="P2 社区来源覆盖率冲刺脚本（docs/research_notes）。"
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="仅统计会修改的文件，不实际写入。",
    )
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    report = gaps.analyze()
    report.pop("_meta", None)

    modified = 0
    skipped_hub = 0
    skipped_has_p2 = 0
    skipped_has_section = 0
    family_modified: dict[str, int] = {}

    for family, data in sorted(report.items()):
        # Target families with any P2 gap (coverage < 100%).
        if data["P2_pct"] >= 100:
            continue

        for record in data["files"]:
            rel = record["path"]
            path = PROJECT_ROOT / rel

            if is_root_hub(path):
                skipped_hub += 1
                continue

            content = path.read_text(encoding="utf-8", errors="ignore")
            if has_community_section(content):
                skipped_has_section += 1
                continue
            if has_p2_url(content):
                skipped_has_p2 += 1
                continue

            if append_section(path, family, dry_run=args.dry_run):
                modified += 1
                family_modified[family] = family_modified.get(family, 0) + 1

    mode_label = "（干运行）" if args.dry_run else ""
    print(f"会修改 / 已修改文件数{mode_label}: {modified}")
    print(f"跳过根目录枢纽文档: {skipped_hub}")
    print(f"跳过已含 P2 URL: {skipped_has_p2}")
    print(f"跳过已有社区权威参考小节: {skipped_has_section}")

    if family_modified:
        print("\n按概念族修改统计:")
        for family, count in sorted(family_modified.items()):
            print(f"  {family}: {count}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
