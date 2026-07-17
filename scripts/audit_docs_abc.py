#!/usr/bin/env python3
"""
docs/ A/B/C 价值审计脚本（优化版）
- A: 核心参考（必须保留）
- B: 需更新（含 TODO/占位符/旧版本引用）
- C: 过时/重复/低价值（建议归档或删除）
"""

import os
import re
import subprocess
from pathlib import Path
from datetime import datetime

DOCS_DIR = Path("docs")
REPORTS_DIR = Path("reports")
ROOT = Path.cwd()

PATTERN_TODO = re.compile(r"TODO|FIXME|待补充|占位|未完善|draft|WIP", re.IGNORECASE)
PATTERN_OLD_VERSION = re.compile(r"Rust 1\.(\d{2})\.?\d*\b|\brust-version\s*=\s*\"1\.(\d{2})\b")
PATTERN_DEPRECATED = re.compile(r"deprecated|已废弃|已归档|过时|不再维护", re.IGNORECASE)
MSRV_MINOR = 96


def get_git_last_commit(path: Path) -> datetime:
    try:
        result = subprocess.run(
            ["git", "log", "-1", "--format=%ct", str(path)],
            capture_output=True, text=True, check=True
        )
        return datetime.fromtimestamp(int(result.stdout.strip()))
    except Exception:
        return datetime.now()


def build_link_index() -> dict:
    """一次性构建所有 Markdown 内容索引"""
    index = {}
    for root, _, files in os.walk(ROOT):
        for f in files:
            if f.endswith(".md"):
                fpath = Path(root) / f
                try:
                    index[str(fpath)] = fpath.read_text(encoding="utf-8", errors="ignore")
                except Exception:
                    pass
    return index


def count_internal_links(md_path: Path, index: dict) -> int:
    target = str(md_path.resolve().relative_to(ROOT.resolve())).replace("\\", "/")
    count = 0
    for content in index.values():
        if target in content:
            count += 1
    return count


def classify_file(md_path: Path, index: dict) -> tuple:
    rel = str(md_path.relative_to(DOCS_DIR)).replace("\\", "/")
    content = md_path.read_text(encoding="utf-8", errors="ignore")
    
    if PATTERN_DEPRECATED.search(content):
        return "C", "包含 deprecated/已归档/过时标记"
    
    last_commit = get_git_last_commit(md_path)
    days_since_commit = (datetime.now() - last_commit).days
    links = count_internal_links(md_path, index)
    
    if days_since_commit > 365 and links == 0:
        return "C", f"超过 {days_since_commit} 天未更新且无内部链接"
    
    if PATTERN_TODO.search(content):
        return "B", "包含 TODO/FIXME/待补充等标记"
    
    version_matches = PATTERN_OLD_VERSION.findall(content)
    if version_matches:
        versions = [int(v[0] or v[1]) for v in version_matches]
        if max(versions) < MSRV_MINOR - 2:
            return "B", f"包含旧版本引用（最高 1.{max(versions)}）"
    
    if links > 0:
        return "A", f"核心参考（{links} 个内部链接）"
    
    if days_since_commit < 180:
        return "A", "近期维护文件"
    
    return "B", "孤立文档，建议 review"


def main():
    files = sorted(DOCS_DIR.rglob("*.md"))
    index = build_link_index()
    
    results = {"A": [], "B": [], "C": []}
    
    for md_path in files:
        category, reason = classify_file(md_path, index)
        rel = str(md_path.relative_to(DOCS_DIR)).replace("\\", "/")
        results[category].append((rel, reason))
    
    report_path = REPORTS_DIR / "DOCS_ABC_AUDIT_2026_06_03.md"
    with open(report_path, "w", encoding="utf-8") as f:
        f.write("# docs/ A/B/C 价值审计报告\n\n")
        f.write(f"> **生成时间**: {datetime.now().isoformat()}\n")
        f.write(f"> **MSRV 基准**: 1.{MSRV_MINOR}.0\n")
        f.write(f"> **总文件数**: {len(files)}\n\n")
        
        for cat in ["A", "B", "C"]:
            f.write(f"## {cat} 类文件 ({len(results[cat])} 个)\n\n")
            f.write(f"{ {'A': '核心参考 — 必须保留', 'B': '需更新 — 建议修复', 'C': '低价值 — 建议归档/删除'}[cat] }\n\n")
            for rel, reason in results[cat]:
                f.write(f"- `{rel}` — {reason}\n")
            f.write("\n")
    
    print(f"审计完成: {len(files)} 文件")
    print(f"  A 类（核心）: {len(results['A'])}")
    print(f"  B 类（需更新）: {len(results['B'])}")
    print(f"  C 类（建议归档）: {len(results['C'])}")
    print(f"报告保存至: {report_path}")


if __name__ == "__main__":
    main()
