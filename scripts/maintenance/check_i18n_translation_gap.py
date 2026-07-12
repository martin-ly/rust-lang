#!/usr/bin/env python3
"""
check_i18n_translation_gap.py

检测 Rust 官方文档翻译版本与英文原版之间的版本差异，输出差距报告。

用法:
    python scripts/maintenance/check_i18n_translation_gap.py
"""

from __future__ import annotations

import json
import sys
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any

PROJECT_ROOT = Path(__file__).resolve().parents[2]


@dataclass(frozen=True)
class TranslationSource:
    name: str
    upstream_owner_repo: str
    translation_owner_repo: str
    project_doc: str


SOURCES: list[TranslationSource] = [
    TranslationSource(
        name="TRPL 中文",
        upstream_owner_repo="rust-lang/book",
        translation_owner_repo="rust-lang-cn/book",
        project_doc="docs/12_research_notes/01_alignment_matrices/32_rust_book_alignment.md",
    ),
    TranslationSource(
        name="TRPL 日本語",
        upstream_owner_repo="rust-lang/book",
        translation_owner_repo="rust-jp/book",
        project_doc="docs/12_research_notes/01_alignment_matrices/32_rust_book_alignment.md",
    ),
    TranslationSource(
        name="Rust Reference 中文",
        upstream_owner_repo="rust-lang/reference",
        translation_owner_repo="rust-lang-cn/reference",
        project_doc="docs/12_research_notes/01_alignment_matrices/34_rust_reference_alignment.md",
    ),
]


def _github_api(url: str) -> Any:
    req = urllib.request.Request(
        url,
        headers={"Accept": "application/vnd.github+json", "User-Agent": "rust-lang-i18n-gap-checker"},
    )
    with urllib.request.urlopen(req, timeout=30) as resp:  # noqa: S310
        return json.loads(resp.read().decode("utf-8"))


def latest_release_tag(owner_repo: str) -> str | None:
    try:
        data = _github_api(f"https://api.github.com/repos/{owner_repo}/releases/latest")
        return str(data.get("tag_name", "")) or None
    except Exception as exc:  # noqa: BLE001
        print(f"⚠️  Failed to fetch release for {owner_repo}: {exc}", file=sys.stderr)
        return None


def latest_commit_sha(owner_repo: str, default_branch: str = "main") -> str | None:
    try:
        data = _github_api(f"https://api.github.com/repos/{owner_repo}/commits/{default_branch}")
        return str(data.get("sha", ""))[:7] or None
    except Exception as exc:  # noqa: BLE001
        print(f"⚠️  Failed to fetch commit for {owner_repo}: {exc}", file=sys.stderr)
        return None


def check_source(source: TranslationSource) -> dict[str, Any]:
    upstream_tag = latest_release_tag(source.upstream_owner_repo)
    upstream_commit = latest_commit_sha(source.upstream_owner_repo)
    translation_commit = latest_commit_sha(source.translation_owner_repo)
    return {
        "source": source,
        "upstream_tag": upstream_tag,
        "upstream_commit": upstream_commit,
        "translation_commit": translation_commit,
    }


def print_report(results: list[dict[str, Any]]) -> None:
    print("=" * 70)
    print("International Translation Gap Report")
    print("=" * 70)
    for r in results:
        s: TranslationSource = r["source"]
        print(f"\n{s.name}")
        print(f"  Project doc      : {s.project_doc}")
        print(f"  Upstream         : {s.upstream_owner_repo}")
        print(f"    latest release : {r['upstream_tag'] or 'N/A'}")
        print(f"    latest commit  : {r['upstream_commit'] or 'N/A'}")
        print(f"  Translation      : {s.translation_owner_repo}")
        print(f"    latest commit  : {r['translation_commit'] or 'N/A'}")
        if r["upstream_commit"] and r["translation_commit"]:
            print(f"  Status           : 🔄 need manual comparison of commits")
        else:
            print(f"  Status           : ⚠️  could not fetch data")
    print("\n" + "=" * 70)
    print("Tip: Run `git log --oneline <upstream>..<translation>` locally for details.")
    print("=" * 70)


def main() -> int:
    results = [check_source(s) for s in SOURCES]
    print_report(results)
    return 0


if __name__ == "__main__":
    sys.exit(main())
