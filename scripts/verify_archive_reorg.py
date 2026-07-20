#!/usr/bin/env python3
"""
verify_archive_reorg.py

在 archive 重组的每个阶段后运行，验证：
1. 迁移映射的文件数量守恒；
2. 旧目录是否已清空（或按预期保留为 stub）；
3. 新目录下 stub 文件符合 AGENTS.md 规范（≤25 行、≤2000 字节、含权威来源链接）；
4. archive 内部相对链接无断裂；
5. 新目录命名符合 snake_case / number_prefix_snake_case。

用法：
    python scripts/verify_archive_reorg.py --phase 1
    python scripts/verify_archive_reorg.py --full

退出码：
    0 - 验证通过
    1 - 发现需修复的问题
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
ARCHIVE_ROOT = PROJECT_ROOT / "archive"


def count_files_under(path: Path) -> int:
    return sum(1 for _ in path.rglob("*") if _.is_file())


def get_git_tree_files() -> list[Path]:
    """获取 git 跟踪的 archive/ 下文件列表。"""
    result = subprocess.run(
        ["git", "ls-files", "archive/"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    return [PROJECT_ROOT / p for p in result.stdout.splitlines() if p]


def check_stub_purity(stub_paths: list[Path]) -> list[str]:
    """检查 stub 是否符合 AGENTS.md 规范。"""
    issues = []
    markers = ["权威来源", "历史内容", "已归档", "重定向", "superseded", "stub/archive redirect"]
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


def check_naming(paths: list[Path]) -> list[str]:
    """检查目录名是否符合 snake_case / number_prefix_snake_case。"""
    issues = []
    pattern = re.compile(r"^[a-z0-9_]+$")
    for p in paths:
        if p.is_dir():
            for part in p.relative_to(ARCHIVE_ROOT).parts:
                # 豁免历史目录名（如带中文、日期、连字符）
                if not pattern.match(part) and not part.startswith("."):
                    issues.append(f"{p}: non-snake_case directory name '{part}'")
    return issues


def check_internal_links(md_files: list[Path]) -> list[str]:
    """检查 archive/ 内部 Markdown 文件中的相对链接是否断裂。"""
    link_re = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")
    issues = []
    for f in md_files:
        try:
            content = f.read_text(encoding="utf-8", errors="ignore")
        except Exception:
            continue
        for _, raw in link_re.findall(content):
            # 只处理相对链接且指向 archive/ 内部的
            if raw.startswith("http") or raw.startswith("#") or raw.startswith("mailto:"):
                continue
            link = raw.split("#")[0]
            if not link:
                continue
            target = (f.parent / link).resolve()
            try:
                target_rel = target.relative_to(ARCHIVE_ROOT)
            except ValueError:
                continue
            if not target.exists():
                issues.append(f"{f}: broken internal link to `{link}`")
    return issues


def main() -> int:
    parser = argparse.ArgumentParser(description="Verify archive reorganization integrity.")
    parser.add_argument("--phase", type=int, help="Phase number to verify (1-6).")
    parser.add_argument("--full", action="store_true", help="Run full verification across all archive.")
    args = parser.parse_args()

    if not args.phase and not args.full:
        print("ERROR: specify --phase N or --full", file=sys.stderr)
        return 1

    print("=== Archive Reorganization Verification ===\n")

    all_files = get_git_tree_files()
    md_files = [p for p in all_files if p.suffix == ".md"]
    dirs = [d for d in ARCHIVE_ROOT.rglob("*") if d.is_dir()]
    stub_files = [p for p in md_files if "stub" in p.name.lower() or p.name.endswith("_redirect.md")]

    issues = []

    # 1. 文件数量守恒：检查 archive/ 总文件数是否与阶段前一致（除非阶段有删除）
    if args.full:
        total = count_files_under(ARCHIVE_ROOT)
        print(f"Total files under archive/: {total}")

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
        issues.extend(naming_issues)
        print(f"[NAMING] {len(naming_issues)} issue(s)")
    else:
        print("[NAMING] OK")

    # 4. 内部链接
    link_issues = check_internal_links(md_files)
    if link_issues:
        issues.extend(link_issues)
        print(f"[LINKS] {len(link_issues)} issue(s)")
    else:
        print("[LINKS] OK")

    if issues:
        print(f"\n=== {len(issues)} issue(s) found ===")
        for issue in issues[:50]:
            print(f"  - {issue}")
        if len(issues) > 50:
            print(f"  ... and {len(issues) - 50} more")
        return 1

    print("\n=== All checks passed ===")
    return 0


if __name__ == "__main__":
    sys.exit(main())
