#!/usr/bin/env python3
"""
check_archive_integrity.py

定期运行，检查 archive/ 的健康状态：
1. 空目录检测
2. 索引同步（文件是否在 THEMATIC_INDEX.md 中有对应入口）
3. 内部相对链接无断裂
4. stub 文件合规（≤25 行、≤2000 字节、含权威来源标记）
5. 命名规范（snake_case / number_prefix_snake_case）
6. 独立专题集合入口存在

用法：
    python scripts/check_archive_integrity.py
    python scripts/check_archive_integrity.py --strict

退出码：
    0 - 检查通过
    1 - 发现问题（--strict 时）或仅 warning（默认）
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
ARCHIVE = PROJECT_ROOT / "archive"
THEMATIC_INDEX = ARCHIVE / "THEMATIC_INDEX.md"
RELATIONSHIP_MAP = ARCHIVE / "RELATIONSHIP_MAP.md"
README = ARCHIVE / "README.md"


def get_git_files() -> list[Path]:
    """获取 git 跟踪的 archive/ 下文件。"""
    result = subprocess.run(
        ["git", "ls-files", "archive/"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return [PROJECT_ROOT / p for p in result.stdout.splitlines() if p]


def find_empty_dirs() -> list[Path]:
    """查找 archive/ 下空目录。"""
    empty = []
    for d in sorted(ARCHIVE.rglob("*"), key=lambda x: -len(x.parts)):
        if d.is_dir() and not any(d.iterdir()):
            empty.append(d)
    return empty


def check_stub_purity(stub_paths: list[Path]) -> list[str]:
    issues = []
    markers = ["权威来源", "历史内容", "已归档", "重定向", "superseded", "stub/archive redirect", "已移除", "正文已移除", "重定向 stub"]
    for p in stub_paths:
        try:
            content = p.read_text(encoding="utf-8", errors="ignore")
        except Exception as e:
            issues.append(f"{p}: cannot read ({e})")
            continue
        lines = content.splitlines()
        if len(lines) > 25:
            issues.append(f"{p}: stub exceeds 25 lines ({len(lines)})")
        if len(content.encode("utf-8")) > 2000:
            issues.append(f"{p}: stub exceeds 2000 bytes ({len(content.encode('utf-8'))})")
        lower = content.lower()
        if not any(m.lower() in lower for m in markers):
            issues.append(f"{p}: stub missing canonical/markers")
    return issues


def check_naming(dirs: list[Path]) -> list[str]:
    issues = []
    pattern = re.compile(r"^[a-z0-9_]+$")
    for d in dirs:
        if not d.is_dir():
            continue
        for part in d.relative_to(ARCHIVE).parts:
            if part.startswith("."):
                continue
            # 豁免历史目录名（中文、日期、连字符等已存在）
            if not pattern.match(part):
                issues.append(f"{d}: non-snake_case directory name '{part}'")
    return issues


def check_internal_links(md_files: list[Path]) -> list[str]:
    link_re = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")
    issues = []
    for f in md_files:
        try:
            content = f.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue
        for _, raw in link_re.findall(content):
            if raw.startswith("http") or raw.startswith("#") or raw.startswith("mailto:"):
                continue
            link = raw.split("#")[0]
            if not link:
                continue
            target = (f.parent / link).resolve()
            try:
                target.relative_to(ARCHIVE)
            except ValueError:
                continue
            if not target.exists():
                issues.append(f"{f}: broken internal link to `{link}`")
    return issues


def check_index_sync(md_files: list[Path]) -> list[str]:
    """粗略检查文件是否在 THEMATIC_INDEX.md 或 RELATIONSHIP_MAP.md 中有路径引用。"""
    if not THEMATIC_INDEX.exists() or not RELATIONSHIP_MAP.exists():
        return ["THEMATIC_INDEX.md or RELATIONSHIP_MAP.md missing"]
    index_text = THEMATIC_INDEX.read_text(encoding="utf-8", errors="ignore")
    rel_text = RELATIONSHIP_MAP.read_text(encoding="utf-8", errors="ignore")
    combined = index_text + rel_text

    issues = []
    for f in md_files:
        if f.name in ("THEMATIC_INDEX.md", "RELATIONSHIP_MAP.md", "README.md"):
            continue
        rel = f.relative_to(ARCHIVE).as_posix()
        # 检查路径是否被引用（去掉 .md 后缀也检查）
        if rel not in combined and rel[:-3] not in combined:
            issues.append(f"{f}: not referenced in THEMATIC_INDEX.md or RELATIONSHIP_MAP.md")
    return issues


def check_special_collections() -> list[str]:
    issues = []
    expected = [
        ARCHIVE / "09_special_collections" / "rust_ownership_decidability",
        ARCHIVE / "09_special_collections" / "backup_from_docs",
        ARCHIVE / "05_formal_methods" / "01_ownership_decidability_collection" / "README.md",
        ARCHIVE / "08_quality_audits" / "07_backup_from_docs_entry" / "README.md",
        ARCHIVE / "06_ecosystem" / "08_crate_case_studies" / "README.md",
    ]
    for p in expected:
        if not p.exists():
            issues.append(f"missing expected special collection entry: {p}")
    return issues


def main() -> int:
    parser = argparse.ArgumentParser(description="Check archive/ integrity.")
    parser.add_argument("--strict", action="store_true", help="Treat warnings as errors.")
    args = parser.parse_args()

    print("=== Archive Integrity Check ===\n")

    all_files = get_git_files()
    md_files = [p for p in all_files if p.suffix == ".md"]
    dirs = [d for d in ARCHIVE.rglob("*") if d.is_dir()]
    stub_files = [p for p in md_files if "README.md" in p.name or p.parent.name.endswith("_collection") or "entry" in p.parent.name or "case_studies" in p.parent.name]

    issues = []
    warnings = []

    # 1. 空目录
    empty = find_empty_dirs()
    if empty:
        warnings.extend(f"empty dir: {d}" for d in empty)
        print(f"[EMPTY] {len(empty)} empty dir(s)")
    else:
        print("[EMPTY] OK")

    # 2. stub 合规
    stub_issues = check_stub_purity(stub_files)
    if stub_issues:
        issues.extend(stub_issues)
        print(f"[STUB] {len(stub_issues)} issue(s)")
    else:
        print("[STUB] OK")

    # 3. 命名规范
    naming_issues = check_naming(dirs)
    if naming_issues:
        warnings.extend(naming_issues)
        print(f"[NAMING] {len(naming_issues)} warning(s)")
    else:
        print("[NAMING] OK")

    # 4. 内部链接
    link_issues = check_internal_links(md_files)
    if link_issues:
        issues.extend(link_issues)
        print(f"[LINKS] {len(link_issues)} issue(s)")
    else:
        print("[LINKS] OK")

    # 5. 索引同步
    sync_issues = check_index_sync(md_files)
    if sync_issues:
        warnings.extend(sync_issues)
        print(f"[INDEX] {len(sync_issues)} warning(s)")
    else:
        print("[INDEX] OK")

    # 6. 独立专题集合入口
    special_issues = check_special_collections()
    if special_issues:
        issues.extend(special_issues)
        print(f"[SPECIAL] {len(special_issues)} issue(s)")
    else:
        print("[SPECIAL] OK")

    total_errors = len(issues)
    total_warnings = len(warnings)

    print(f"\n=== Summary ===")
    print(f"Errors: {total_errors}")
    print(f"Warnings: {total_warnings}")

    if issues or warnings:
        print("\n--- Issues ---")
        for issue in issues[:50]:
            print(f"  [ERROR] {issue}")
        print("\n--- Warnings ---")
        for warning in warnings[:50]:
            print(f"  [WARN] {warning}")
        if len(issues) > 50 or len(warnings) > 50:
            print(f"  ... and more")

    if total_errors > 0 or (args.strict and total_warnings > 0):
        return 1

    print("\n=== All checks passed ===")
    return 0


if __name__ == "__main__":
    sys.exit(main())
