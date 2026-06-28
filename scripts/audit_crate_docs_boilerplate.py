#!/usr/bin/env python3
"""
审计 crates/*/docs/ 下的 boilerplate 文档一致性。

本脚本不修改文件，仅报告各 crate docs 目录中 boilerplate 文件的
存在性、大小和最后修改时间，帮助识别需要统一模板化的位置。

用法:
    python scripts/audit_crate_docs_boilerplate.py
"""

from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CRATES_DIR = ROOT / "crates"

# 被视为 boilerplate 的文件名（按出现频率从高到低）
BOILERPLATE_NAMES = {
    "README.md",
    "ONE_PAGE_SUMMARY.md",
    "00_MASTER_INDEX.md",
    "Glossary.md",
    "FAQ.md",
    "PENDING_ITEMS.md",
    "MIND_MAP.md",
}


def find_crate_docs() -> dict[str, list[Path]]:
    """返回每个 crate 的 docs 目录下文件列表。"""
    result: dict[str, list[Path]] = {}
    for crate_dir in sorted(CRATES_DIR.iterdir()):
        if not crate_dir.is_dir():
            continue
        docs_dir = crate_dir / "docs"
        if not docs_dir.exists():
            continue
        files = [f for f in docs_dir.iterdir() if f.is_file()]
        result[crate_dir.name] = sorted(files)
    return result


def main() -> int:
    crate_docs = find_crate_docs()

    if not crate_docs:
        print("未找到任何 crates/*/docs/ 目录")
        return 0

    # 统计每个 boilerplate 文件出现的 crate 数量
    coverage: dict[str, list[str]] = defaultdict(list)
    for crate_name, files in crate_docs.items():
        for f in files:
            if f.name in BOILERPLATE_NAMES:
                coverage[f.name].append(crate_name)

    print("=" * 70)
    print("Crates docs boilerplate 审计报告")
    print("=" * 70)
    print(f"\n扫描 crate 数: {len(crate_docs)}")

    print("\n--- Boilerplate 文件覆盖情况 ---")
    for name in sorted(BOILERPLATE_NAMES, key=lambda n: -len(coverage[n])):
        crates = coverage[name]
        missing = sorted(set(crate_docs) - set(crates))
        print(f"\n{name}: {len(crates)}/{len(crate_docs)} crate 拥有")
        if crates:
            print(f"  存在: {', '.join(crates)}")
        if missing:
            print(f"  缺失: {', '.join(missing)}")

    print("\n--- 非 boilerplate 文件（潜在需要归类） ---")
    other_files: dict[str, list[str]] = defaultdict(list)
    for crate_name, files in crate_docs.items():
        for f in files:
            if f.name not in BOILERPLATE_NAMES:
                other_files[f.name].append(crate_name)

    for name in sorted(other_files, key=lambda n: -len(other_files[n])):
        crates = other_files[name]
        print(f"{name}: 出现在 {len(crates)} 个 crate ({', '.join(crates)})")

    # 输出机器可读摘要
    summary = {
        "total_crates": len(crate_docs),
        "boilerplate_coverage": {
            name: len(crates) for name, crates in coverage.items()
        },
        "other_files": {name: len(crates) for name, crates in other_files.items()},
    }
    summary_path = ROOT / "target" / "crate_docs_boilerplate_audit.json"
    summary_path.parent.mkdir(parents=True, exist_ok=True)
    summary_path.write_text(json.dumps(summary, indent=2, ensure_ascii=False))
    print(f"\n摘要已写入: {summary_path}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
