#!/usr/bin/env python3
"""
归档迁移脚本：ROD (rust-ownership-decidability) 目录批量治理脚本

策略：
- 扫描 docs/rust-ownership-decidability/ 中的所有 .md 文件
- 计算每个文件与 concept/ 目录文件的标题/内容相似度
- 相似度 >= 0.7 的文件：添加 [主轨引用: concept/...] 标记
- 相似度 >= 0.9 的文件：建议归档（移动至 archive/ 并标记 [ARCHIVED]）

用法: python scripts/roded_governance.py [--dry-run]
"""

import os
import re
import argparse
from pathlib import Path
from difflib import SequenceMatcher

ROD_DIR = Path("docs/rust-ownership-decidability")
CONCEPT_DIR = Path("concept")
ARCHIVE_DIR = Path("archive/deprecated/roded_duplicates")

def extract_title(filepath: Path) -> str:
    """提取 Markdown 文件的第一级标题。"""
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if line.startswith("# "):
                    return line[2:].strip()
    except Exception:
        pass
    return ""

def extract_first_paragraph(filepath: Path) -> str:
    """提取文件前 500 个非空字符作为摘要。"""
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            text = f.read(2000)
            # 移除代码块和 Markdown 标记
            text = re.sub(r"```[\s\S]*?```", "", text)
            text = re.sub(r"[#*|>\-\[\]`]", "", text)
            text = re.sub(r"\s+", " ", text).strip()
            return text[:500]
    except Exception:
        return ""

def similarity(a: str, b: str) -> float:
    """计算两段文本的相似度。"""
    if not a or not b:
        return 0.0
    return SequenceMatcher(None, a.lower(), b.lower()).ratio()

def find_best_match(rod_file: Path, concept_files: list[Path]) -> tuple[Path, float]:
    """找到与 ROD 文件最匹配的 concept 文件。"""
    rod_title = extract_title(rod_file)
    rod_summary = extract_first_paragraph(rod_file)

    best_match = None
    best_score = 0.0

    for cf in concept_files:
        cf_title = extract_title(cf)
        cf_summary = extract_first_paragraph(cf)

        title_sim = similarity(rod_title, cf_title)
        summary_sim = similarity(rod_summary, cf_summary)
        # 加权：标题匹配权重更高
        score = title_sim * 0.6 + summary_sim * 0.4

        if score > best_score:
            best_score = score
            best_match = cf

    return best_match, best_score

def add_reference_marker(rod_file: Path, concept_file: Path, dry_run: bool = True):
    """在 ROD 文件头部添加主轨引用标记。"""
    marker = f"\n> **[主轨引用: concept/{concept_file.relative_to(CONCEPT_DIR)}]**\n> 本文件内容与主轨教学文档高度重叠，建议优先阅读主轨文档获取最新、最准确的信息。\n\n"

    try:
        with open(rod_file, "r", encoding="utf-8") as f:
            content = f.read()
    except Exception as e:
        print(f"   ⚠️ 无法读取 {rod_file}: {e}")
        return

    if "[主轨引用:" in content:
        print(f"   ⏭️ 已存在引用标记，跳过")
        return

    # 在第一个标题后插入标记
    lines = content.split("\n")
    insert_idx = 0
    for i, line in enumerate(lines):
        if line.startswith("# "):
            insert_idx = i + 1
            break

    new_lines = lines[:insert_idx] + [marker.strip()] + lines[insert_idx:]
    new_content = "\n".join(new_lines)

    if dry_run:
        print(f"   📝 [DRY-RUN] 将添加引用标记 -> concept/{concept_file.relative_to(CONCEPT_DIR)}")
    else:
        with open(rod_file, "w", encoding="utf-8") as f:
            f.write(new_content)
        print(f"   ✅ 已添加引用标记 -> concept/{concept_file.relative_to(CONCEPT_DIR)}")

def archive_file(rod_file: Path, dry_run: bool = True):
    """归档文件至 archive/deprecated/roded_duplicates/"""
    rel_path = rod_file.relative_to(ROD_DIR)
    dest = ARCHIVE_DIR / rel_path

    if dry_run:
        print(f"   📦 [DRY-RUN] 将归档至 {dest}")
        return

    dest.parent.mkdir(parents=True, exist_ok=True)
    try:
        with open(rod_file, "r", encoding="utf-8") as f:
            content = f.read()
        # 添加 ARCHIVED 标记
        if "[ARCHIVED]" not in content:
            content = f"> **[ARCHIVED]** 此文件因与主轨内容完全重复，已归档至 `archive/deprecated/`。\n> 请查阅 `concept/` 目录获取最新内容。\n\n" + content
        with open(dest, "w", encoding="utf-8") as f:
            f.write(content)
        # 删除原文件
        rod_file.unlink()
        print(f"   ✅ 已归档: {dest}")
    except Exception as e:
        print(f"   ⚠️ 归档失败: {e}")

def main():
    parser = argparse.ArgumentParser(description="ROD 目录批量治理")
    parser.add_argument("--dry-run", action="store_true", default=True, help="仅预览，不实际修改")
    parser.add_argument("--apply", action="store_true", help="实际执行修改")
    args = parser.parse_args()

    dry_run = not args.apply

    print(f"🔍 扫描 {ROD_DIR} ...")
    rod_files = list(ROD_DIR.rglob("*.md"))
    print(f"   发现 {len(rod_files)} 个 Markdown 文件")

    print(f"🔍 扫描 {CONCEPT_DIR} ...")
    concept_files = list(CONCEPT_DIR.rglob("*.md"))
    print(f"   发现 {len(concept_files)} 个 Markdown 文件")

    print("\n📊 开始相似度分析...")
    marked = 0
    archived = 0
    skipped = 0

    for rod_file in rod_files:
        best_match, score = find_best_match(rod_file, concept_files)
        if not best_match:
            continue

        rel = rod_file.relative_to(ROD_DIR)
        print(f"\n📄 {rel}")
        print(f"   标题: {extract_title(rod_file)[:60]}")
        print(f"   最佳匹配: concept/{best_match.relative_to(CONCEPT_DIR)} (相似度: {score:.2f})")

        if score >= 0.9:
            archive_file(rod_file, dry_run)
            archived += 1
        elif score >= 0.7:
            add_reference_marker(rod_file, best_match, dry_run)
            marked += 1
        else:
            skipped += 1

    print(f"\n{'='*50}")
    print(f"📈 治理摘要 {'(DRY-RUN)' if dry_run else '(APPLIED)'}")
    print(f"   建议归档 (>=0.9): {archived}")
    print(f"   建议添加引用 (>=0.7): {marked}")
    print(f"   跳过 (<0.7): {skipped}")
    print(f"   总计: {len(rod_files)}")

    if dry_run and (marked > 0 or archived > 0):
        print(f"\n💡 使用 --apply 参数执行实际修改")

if __name__ == "__main__":
    main()
