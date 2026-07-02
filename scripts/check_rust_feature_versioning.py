#!/usr/bin/env python3
"""扫描 crates/*/src/rust_*_features.rs 的版本归属一致性。

用法:
    python3 scripts/check_rust_feature_versioning.py

返回非零退出码表示发现潜在版本归属问题。
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

CRATES_DIR = Path("crates")
FEATURE_FILE_RE = re.compile(r"rust_(\d+)_features\.rs$")
EXCLUDED_DIRS = {"archive", "deprecated", "target"}
# 非标准版本号文件：rust_2024_features.rs / rust_2025_features.rs 是 Edition/年度特性合集，
# 不是单一 Rust 1.XX 版本文件，跳过版本一致性检查。
EDITION_YEAR_FILES = {"rust_2024_features.rs", "rust_2025_features.rs"}
# 1.XX / 1.XXX 版本号；末尾不能紧跟数字
VERSION_RE = re.compile(r"1\.(\d{2,3})(?!\d)")
# 已知非版本号误报（如黄金比例 1.618、某些数学常数 1.833）
KNOWN_FALSE_POSITIVE_MINORS = {618, 833}
# 允许相邻版本提及（如说明历史/未来）
ADJACENT_VERSION_THRESHOLD = 2


def extract_file_version(name: str) -> int | None:
    """把 rust_186_features.rs 这样的文件名解析为 Rust 1.86。

    项目约定：文件名中的数字是 "1" + minor 版本拼接而成。
    例如 rust_186_features.rs -> 1.86；rust_1192_features.rs -> 1.192。
    """
    m = FEATURE_FILE_RE.search(name)
    if not m:
        return None
    num = m.group(1)
    # 去掉前导 1，剩余部分即 minor 版本号
    minor = num[1:] if num.startswith("1") else num
    return int(minor) if minor.isdigit() else None


def is_third_party_version(line: str) -> bool:
    """判断该行是否提到第三方库的版本号（如 Tokio 1.52），而非 Rust 版本。"""
    lower = line.lower()
    return "tokio" in lower or "serde" in lower or "axum" in lower or "hyper" in lower


def is_inside_string(line: str, pos: int) -> bool:
    """粗略判断 pos 是否位于双引号字符串字面量内部（考虑 \" 转义）。"""
    in_string = False
    escaped = False
    for i, ch in enumerate(line):
        if i >= pos:
            break
        if escaped:
            escaped = False
            continue
        if ch == "\\":
            escaped = True
            continue
        if ch == '"':
            in_string = not in_string
    return in_string


def check_file(path: Path, file_version: int) -> list[str]:
    issues: list[str] = []
    try:
        text = path.read_text(encoding="utf-8")
    except Exception as e:
        return [f"Cannot read {path}: {e}"]

    lines = text.splitlines()
    for i, line in enumerate(lines, start=1):
        if is_third_party_version(line):
            continue
        for m in VERSION_RE.finditer(line):
            mentioned = int(m.group(1))
            # 跳过 "1.XX+" 形式的历史版本引用（如 "array::map (1.63+)"）
            if m.end() < len(line) and line[m.end()] == "+":
                continue
            # 允许相邻版本提及
            if abs(mentioned - file_version) > ADJACENT_VERSION_THRESHOLD:
                if mentioned in KNOWN_FALSE_POSITIVE_MINORS:
                    continue
                issues.append(
                    f"{path}:{i}: mentions 1.{mentioned} but file is {path.name}"
                )

    # 检查 nightly feature gate 是否出现在 stable 特性文件中
    # 跳过注释和字符串字面量中的 feature gate 提及
    if "features.rs" in path.name and "_preview" not in path.name:
        feature_gate_re = re.compile(r"#!\s*\[\s*feature\s*\(")
        for i, line in enumerate(lines, start=1):
            stripped = line.strip()
            if stripped.startswith("//") or stripped.startswith("*") or stripped.startswith("///"):
                continue
            # 去掉行内注释
            code_part = line.split("//", 1)[0]
            for m in feature_gate_re.finditer(code_part):
                if not is_inside_string(code_part, m.start()):
                    issues.append(f"{path}:{i}: found #![feature(...)] in a stable feature file")

    return issues


def main() -> int:
    all_issues: list[str] = []
    for path in sorted(CRATES_DIR.rglob("rust_*_features.rs")):
        if any(part in EXCLUDED_DIRS for part in path.relative_to(CRATES_DIR).parts):
            continue
        if path.name in EDITION_YEAR_FILES:
            continue
        version = extract_file_version(path.name)
        if version is None:
            continue
        all_issues.extend(check_file(path, version))

    if all_issues:
        print(f"❌ Found {len(all_issues)} potential versioning issues:")
        for issue in all_issues[:50]:
            print(f"  - {issue}")
        if len(all_issues) > 50:
            print(f"  ... and {len(all_issues) - 50} more")
        return 1
    print("✅ No obvious Rust feature versioning issues found.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
