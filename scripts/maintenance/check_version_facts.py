#!/usr/bin/env python3
"""
版本事实性检查脚本 (Version Fact Checker)

扫描项目中的常见版本号/状态/术语事实性错误，
与 Rust 官方 release notes 和 edition guide 对齐。

运行方式:
    python scripts/maintenance/check_version_facts.py

返回码:
    0 - 未发现疑似错误
    1 - 发现疑似错误

注意：
- archive/ 与 reports/ 中的历史报告通常不扫描（允许保留历史记录）。
- 本脚本是启发式检查，最终判断仍需人工确认。
"""

import os
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

# 扫描目录（排除 archive、target、.git、node_modules 等）
SCAN_DIRS = [
    "book",
    "concept",
    "content",
    "crates",
    "docs",
    "examples",
    "exercises",
    "guides",
    "knowledge",
]

SKIP_DIRS = {
    ".git",
    "target",
    "node_modules",
    "__pycache__",
    "archive",
}

# 事实性规则：(模式, 描述, 是否区分大小写)
RULES = [
    # async closures 已于 1.85.0 stable
    (
        r"(?i)async\s+closure.*(?:nightly-only|unstable|TBD|1\.96|1\.97)",
        "async closures 已在 Rust 1.85.0 stable，不应再描述为 nightly/unstable/TBD/1.96/1.97",
        False,
    ),
    (
        r"(?i)AsyncFn\s+traits?.*1\.94",
        "AsyncFn traits 与 async closures 同在 Rust 1.85.0 stable，不是 1.94",
        False,
    ),
    (
        r"1\.96\s+FCP",
        "async closures 的 FCP/稳定版本号错误（应为 1.85.0）",
        False,
    ),
    # gen blocks 仍 nightly，gen 只是保留关键字
    (
        r"(?i)gen\s+关键字.*(?:正式启用|stable|1\.95.*启用)",
        "gen 只是 Edition 2024 保留关键字；gen {} / yield 仍 nightly，不能说'正式启用'",
        False,
    ),
    # Edition 2024 在 1.85.0 stable
    (
        r"(?i)Edition\s+2024.*1\.82.*稳定",
        "Edition 2024 在 Rust 1.85.0 才真正 stable，1.82 只是部分前置特性",
        False,
    ),
    # &const 不是官方术语
    (
        r"&const\s",
        "不存在 '&const' 官方术语，应使用 '&raw const' / '&raw mut'（1.82 stable）",
        False,
    ),
]

# 文件扩展名白名单
EXTS = {".md", ".rs", ".toml"}


def should_skip_dir(path: Path) -> bool:
    parts = set(path.parts)
    return not parts.isdisjoint(SKIP_DIRS)


def scan() -> list[tuple[str, int, str, str]]:
    findings: list[tuple[str, int, str, str]] = []

    for scan_dir in SCAN_DIRS:
        base = ROOT / scan_dir
        if not base.exists():
            continue
        for path in base.rglob("*"):
            if path.is_dir():
                continue
            if should_skip_dir(path):
                continue
            if path.suffix not in EXTS:
                continue

            try:
                text = path.read_text(encoding="utf-8")
            except UnicodeDecodeError:
                continue

            for lineno, line in enumerate(text.splitlines(), start=1):
                for pattern, desc, _ in RULES:
                    if re.search(pattern, line):
                        findings.append(
                            (str(path.relative_to(ROOT)), lineno, line.strip(), desc)
                        )

    return findings


def main() -> int:
    findings = scan()

    if not findings:
        print("✅ 未发现常见版本/术语事实性错误。")
        return 0

    print(f"⚠️  发现 {len(findings)} 处疑似事实性错误/过时表述：\n")
    for filepath, lineno, line, desc in findings:
        print(f"  {filepath}:{lineno}")
        print(f"    行内容: {line[:120]}")
        print(f"    问题: {desc}\n")

    print("提示：archive/ 与 reports/ 中的历史报告通常允许保留原样。")
    return 1


if __name__ == "__main__":
    sys.exit(main())
