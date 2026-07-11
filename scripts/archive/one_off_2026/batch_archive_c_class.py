#!/usr/bin/env python3
"""
为 C 类目录（docs/research_notes/ 和 docs/rust-ownership-decidability/）
批量添加 [归档级] 标记。
"""

from pathlib import Path

ARCHIVE_HEADER = """> **内容分级**: [归档级]
> **说明**: 本文档为历史研究材料，部分内容可能已被后续版本覆盖或整合至主轨文档。
> **主轨参考**: [concept/](../../../concept/) · [knowledge/](../../../knowledge/)
>
"""


def process_file(filepath: Path, dry_run: bool = True) -> bool:
    content = filepath.read_text(encoding="utf-8")
    
    # 跳过非 markdown 文件
    if not filepath.name.endswith(".md"):
        return False
    
    # 如果已有内容分级标记，更新为 [归档级]
    if "**内容分级**" in content:
        # 检查是否已经是归档级
        if "[归档级]" in content:
            return False
        # 替换为归档级
        import re
        new_content = re.sub(
            r'>?\s*\*\*内容分级\*\*:[^\n]*',
            '> **内容分级**: [归档级]',
            content
        )
        if not dry_run:
            filepath.write_text(new_content, encoding="utf-8")
        return True
    
    # 如果没有内容分级标记，在标题后插入
    lines = content.splitlines()
    if not lines or not lines[0].strip().startswith("#"):
        return False
    
    # 找到标题后的插入位置
    insert_idx = 1
    for i, line in enumerate(lines[1:], start=1):
        if line.strip() == "":
            insert_idx = i + 1
            break
        if not line.strip().startswith(">"):
            insert_idx = i
            break
    
    new_lines = lines[:insert_idx] + ["> **内容分级**: [归档级]", ">"] + lines[insert_idx:]
    new_content = "\n".join(new_lines)
    
    if not dry_run:
        filepath.write_text(new_content, encoding="utf-8")
    
    return True


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--run", action="store_true")
    parser.add_argument("--dir", required=True)
    parser.add_argument("--limit", type=int, default=0)
    args = parser.parse_args()
    
    target_dir = Path(args.dir)
    modified = 0
    skipped = 0
    
    files = list(target_dir.rglob("*.md"))
    if args.limit > 0:
        files = files[:args.limit]
    
    for md_file in files:
        if "archive" in str(md_file).lower():
            skipped += 1
            continue
        if process_file(md_file, dry_run=not args.run):
            modified += 1
        else:
            skipped += 1
    
    print(f"{'[DRY-RUN] ' if not args.run else ''}完成: 修改 {modified} 个文件, 跳过 {skipped} 个文件")


if __name__ == "__main__":
    main()
