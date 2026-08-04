#!/usr/bin/env python3
"""Automated response skeleton for Rust 1.98.0 stable release.

This script detects whether Rust 1.98.0 has been released and, if so, performs
a structured release-response workflow:

1. Create ``concept/07_future/00_version_tracking/rust_1_98_0.md`` from a
   template populated with the release date and upstream links.
2. Update ``concept/07_future/00_version_tracking/01_rust_version_tracking.md``
   to link to the new 1.98.0 page.
3. Update ``concept/SUMMARY.md`` with the 1.98.0 entry.
4. Touch affected Cargo / toolchain concept pages with 1.98 compatibility notes.
5. Run ``scripts/check_version_semantic_injection.py --strict`` to verify
   1.98.0 features are bidirectionally linked to ``concept/`` authority pages.

Modes:

* ``--check-only`` — only detect release status and print pending/available.
* ``--dry-run`` — print all planned file changes without writing them.
* ``--apply`` (default) — execute the workflow when 1.98.0 is available.

Exit codes:

* ``0`` — release detected and workflow completed, or pending and --check-only.
* ``1`` — unexpected error.
* ``2`` — 1.98.0 not yet released (when run without ``--check-only``).

Examples:

    python scripts/rust_1_98_0_release_response.py --check-only
    python scripts/rust_1_98_0_release_response.py --dry-run
    python scripts/rust_1_98_0_release_response.py --apply
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import re
import subprocess
import sys
import urllib.request
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
VERSION_DIR = ROOT / "concept" / "07_future" / "00_version_tracking"
CONCEPT_DIR = ROOT / "concept"
SUMMARY_PATH = CONCEPT_DIR / "SUMMARY.md"
VERSION_TRACKING_PATH = VERSION_DIR / "01_rust_version_tracking.md"
RELEASE_PAGE_PATH = VERSION_DIR / "rust_1_98_0.md"
CHECK_SCRIPT = ROOT / "scripts" / "check_version_semantic_injection.py"

EXPECTED_RELEASE_DATE = "2026-08-20"
RELEASE_NOTES_BETA = "https://releases.rs/docs/1.98.0/"
RELEASE_NOTES_STABLE = "https://releases.rs/docs/1.98.0/"
RUST_BLOG_RSS = "https://blog.rust-lang.org/feed.xml"
GITHUB_RELEASES = "https://api.github.com/repos/rust-lang/rust/releases/tags/1.98.0"


def _http_get_json(url: str, timeout: int = 15) -> dict[str, Any] | None:
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "rust-lang-kb-release-bot/1.0"})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            if resp.status != 200:
                return None
            data = resp.read().decode("utf-8")
            return json.loads(data)
    except Exception:
        return None


def _http_get_text(url: str, timeout: int = 15) -> str | None:
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "rust-lang-kb-release-bot/1.0"})
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            if resp.status != 200:
                return None
            return resp.read().decode("utf-8", errors="replace")
    except Exception:
        return None


def check_github_release() -> dict[str, Any] | None:
    """Check if rust-lang/rust tag 1.98.0 exists."""
    return _http_get_json(GITHUB_RELEASES)


def check_releases_rs() -> bool:
    """Check if releases.rs 1.98.0 page returns 200 and looks like stable."""
    text = _http_get_text(RELEASE_NOTES_STABLE)
    if not text:
        return False
    # Stable pages usually contain "Rust 1.98.0" without "beta" markers.
    return "Rust 1.98.0" in text and "beta" not in text.lower()


def check_rust_blog() -> bool:
    """Check Rust Blog RSS for 1.98.0 announcement."""
    text = _http_get_text(RUST_BLOG_RSS)
    if not text:
        return False
    return "1.98.0" in text


def detect_release() -> dict[str, Any]:
    """Aggregate release detection from multiple sources."""
    github = check_github_release()
    releases_rs = check_releases_rs()
    blog = check_rust_blog()
    available = bool(github) or releases_rs or blog
    reasons: list[str] = []
    if github:
        reasons.append("GitHub tag 1.98.0 exists")
    if releases_rs:
        reasons.append("releases.rs 1.98.0 stable page available")
    if blog:
        reasons.append("Rust Blog 1.98.0 announcement found")
    return {
        "available": available,
        "reasons": reasons,
        "github": bool(github),
        "releases_rs": releases_rs,
        "rust_blog": blog,
        "expected_date": EXPECTED_RELEASE_DATE,
        "checked_at": _dt.datetime.now(_dt.timezone.utc).isoformat(),
    }


def build_release_page(release_date: str | None) -> str:
    """Generate the Rust 1.98.0 stable release page skeleton."""
    date_str = release_date or EXPECTED_RELEASE_DATE
    return f"""# Rust 1.98.0 稳定特性

> **EN**: Rust 1.98.0 Stabilized Features
> **Summary**: Rust 1.98.0 于 {date_str} 进入 stable 通道。本文档按官方发布笔记汇总已稳定的语言、标准库、Cargo、Rustdoc 与目标平台变更。
>
> **受众**: [专家]
> **Bloom 层级**: L2-L3
> **内容分级**: [综述级]
> **权威来源**: 本文件为 `concept/` 权威页。
> **Rust 版本**: **1.98.0 stable**
> **最后更新**: {_dt.datetime.now().strftime("%Y-%m-%d")}
> **状态**: ✅ 已对齐 Rust 1.98.0 stable
>
> **权威来源**:
>
> · [Announcing Rust 1.98.0 — Rust Blog](https://blog.rust-lang.org/) ·
> [Rust 1.98.0 Release Notes]({RELEASE_NOTES_STABLE}) ·
> [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) ·
> [TRPL](https://doc.rust-lang.org/book/title-page.html) ·
> [Brown University — Interactive Rust Book](https://rust-book.cs.brown.edu/)
>
> **前置概念**: [Rust 版本跟踪](01_rust_version_tracking.md) · [Rust 1.97 稳定特性](rust_1_97_stabilized.md) · [Rust 1.97.1 稳定补丁](rust_1_97_1.md)
> **后置概念**: [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md) · [Rust 1.99+ 前沿特性预览](rust_1_99_preview.md)

---

## 1. 已稳定特性概览

> 本节在 1.98.0 stable 发布当天由 `scripts/rust_1_98_0_release_response.py` 自动生成骨架；
> 发布团队需按官方 release notes 逐项填充特性表格、代码示例、迁移注意与相关 `concept/` 权威页链接。

| 类别 | 代表变更 |
|:---|:---|
| **语言** | （待填充：按 release notes 列出） |
| **标准库** | （待填充） |
| **平台** | （待填充） |
| **Cargo** | （待填充） |
| **Rustdoc** | （待填充） |
| **兼容性** | （待填充） |

## 2. 语言与编译器

（待填充：逐条特性、代码示例、相关 `concept/` 页、迁移注意）

## 3. 目标平台

（待填充）

## 4. 标准库 API

（待填充）

## 5. Cargo

（待填充）

## 6. Rustdoc

（待填充）

## 7. 兼容性注意事项

| 变更 | 影响 | 建议 |
|:---|:---|:---|
| （待填充） | | |

## 8. 迁移指南

```bash
rustup update stable
rustc --version  # >= 1.98.0
cargo --version  # >= 1.98.0
```

## 9. 权威来源与示例

> **完整特性说明、代码示例与迁移建议**请参见项目权威页：
>
> - [`concept/07_future/00_version_tracking/rust_1_98_preview.md`](rust_1_98_preview.md)（未稳定候选与 1.99+ 前瞻）

## 10. 项目构建说明

本项目 `rust-toolchain.toml` 保持 `channel = "stable"`，由 rustup 自动解析当前 latest stable。

## 国际权威参考 / International Authority References

- **P1 学术/形式化**: [Oxide: The Essence of Rust (arXiv:1903.00982)](https://arxiv.org/abs/1903.00982)
- **P2 生态/社区**: [docs.rs/tokio](https://docs.rs/tokio) · [docs.rs/futures](https://docs.rs/futures)

## 相关概念

- [Rust 版本跟踪](01_rust_version_tracking.md)
- [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md)
- [Rust 1.99+ 前沿特性预览](rust_1_99_preview.md)

## 🧭 思维导图（Mindmap）

```mermaid
mindmap
  root((Rust 1.98.0 稳定特性))
    1. 已稳定特性概览
    2. 语言与编译器
    3. 目标平台
    4. 标准库 API
    5. Cargo
    6. Rustdoc
    7. 兼容性注意事项
```

## ⚠️ 反例与陷阱

（待填充：1.98.0 最可能造成编译失败的兼容性变更及最小复现）
"""


def update_version_tracking_page(dry_run: bool) -> list[str]:
    """Insert a link to rust_1_98_0.md in the version tracking page."""
    changes: list[str] = []
    if not VERSION_TRACKING_PATH.exists():
        return changes
    text = VERSION_TRACKING_PATH.read_text(encoding="utf-8")
    marker = "> Rust 1.97.1 已于 2026-07-16 进入 stable"
    link_line = (
        "> Rust 1.98.0 stable 已发布，详见 [`rust_1_98_0.md`](rust_1_98_0.md)；"
        "1.98.0 beta 已冻结，预计 2026-08-20 进入 stable。\n"
    )
    if "rust_1_98_0.md" in text:
        return changes
    if marker in text:
        new_text = text.replace(marker, marker + "\n" + link_line)
        changes.append(f"updated {VERSION_TRACKING_PATH}")
        if not dry_run:
            VERSION_TRACKING_PATH.write_text(new_text, encoding="utf-8")
    return changes


def update_summary(dry_run: bool) -> list[str]:
    """Add rust_1_98_0.md entry to concept/SUMMARY.md if missing."""
    changes: list[str] = []
    if not SUMMARY_PATH.exists():
        return changes
    text = SUMMARY_PATH.read_text(encoding="utf-8")
    entry = "  - [Rust 1.98.0 稳定特性](07_future/00_version_tracking/rust_1_98_0.md)"
    if "rust_1_98_0.md" in text:
        return changes
    # Insert after rust_1_97_stabilized.md line.
    anchor = "  - [Rust 1.97 稳定特性](07_future/00_version_tracking/rust_1_97_stabilized.md)"
    if anchor in text:
        new_text = text.replace(anchor, anchor + "\n" + entry)
        changes.append(f"updated {SUMMARY_PATH}")
        if not dry_run:
            SUMMARY_PATH.write_text(new_text, encoding="utf-8")
    return changes


def touch_cargo_pages(dry_run: bool) -> list[str]:
    """Record intent to update Cargo-related concept pages for 1.98.0."""
    changes: list[str] = []
    cargo_pages = [
        CONCEPT_DIR / "06_ecosystem" / "01_cargo" / "17_resolver_v3_public_demo.md",
    ]
    for page in cargo_pages:
        if page.exists():
            changes.append(f"review {page} for 1.98.0 compatibility notes")
    return changes


def run_semantic_injection_check() -> dict[str, Any]:
    """Run the version semantic injection checker."""
    result = {
        "command": str(CHECK_SCRIPT),
        "returncode": -1,
        "stdout": "",
        "stderr": "",
    }
    if not CHECK_SCRIPT.exists():
        result["stderr"] = "check_version_semantic_injection.py not found"
        return result
    try:
        proc = subprocess.run(
            [sys.executable, str(CHECK_SCRIPT), "--strict"],
            capture_output=True,
            text=True,
            cwd=ROOT,
            timeout=300,
        )
        result["returncode"] = proc.returncode
        result["stdout"] = proc.stdout
        result["stderr"] = proc.stderr
    except Exception as exc:
        result["stderr"] = str(exc)
    return result


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Automated response skeleton for Rust 1.98.0 stable release.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument(
        "--check-only",
        action="store_true",
        help="Only detect release status; do not write files",
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Print planned changes without writing files",
    )
    parser.add_argument(
        "--apply",
        action="store_true",
        help="Create/update files if 1.98.0 is released (default if no flag given)",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="Run workflow even if release is not detected (for template testing)",
    )
    args = parser.parse_args(argv)

    if not args.check_only and not args.dry_run and not args.apply:
        args.apply = True

    status = detect_release()
    print(json.dumps(status, ensure_ascii=False, indent=2))

    if args.check_only:
        return 0

    if not status["available"] and not args.force:
        print(f"\nRust 1.98.0 is not yet released (expected around {EXPECTED_RELEASE_DATE}).", file=sys.stderr)
        print("Use --force to test the workflow anyway, or --dry-run to preview changes.", file=sys.stderr)
        return 2

    dry_run = args.dry_run
    changes: list[str] = []

    # 1. Create release page.
    if not RELEASE_PAGE_PATH.exists() or args.force:
        release_date = EXPECTED_RELEASE_DATE if status["available"] else None
        page_text = build_release_page(release_date)
        changes.append(f"create {RELEASE_PAGE_PATH}")
        if not dry_run:
            RELEASE_PAGE_PATH.write_text(page_text, encoding="utf-8")
    else:
        changes.append(f"{RELEASE_PAGE_PATH} already exists")

    # 2. Update version tracking page.
    changes.extend(update_version_tracking_page(dry_run))

    # 3. Update SUMMARY.
    changes.extend(update_summary(dry_run))

    # 4. Review Cargo pages.
    changes.extend(touch_cargo_pages(dry_run))

    # 5. Semantic injection check.
    check_result = run_semantic_injection_check()
    changes.append(
        f"semantic injection check: exit {check_result['returncode']}"
    )

    report = {
        "release_status": status,
        "changes": changes,
        "dry_run": dry_run,
        "semantic_check": check_result,
    }

    print("\nWorkflow report:")
    print(json.dumps(report, ensure_ascii=False, indent=2))

    if dry_run:
        print("\nDry run completed; no files were written.", file=sys.stderr)
        return 0

    return 0 if check_result["returncode"] == 0 else 1


if __name__ == "__main__":
    raise SystemExit(main())
