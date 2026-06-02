#!/usr/bin/env python3
"""
knowledge/ 命名规范批量重命名脚本

用法:
    python scripts/knowledge_rename.py --dry-run   # 预演，仅打印映射表
    python scripts/knowledge_rename.py --execute   # 实际执行重命名
    python scripts/knowledge_rename.py --batch 00_start  # 仅执行指定批次
"""

import argparse
import os
import re
import subprocess
from pathlib import Path

BASE_DIR = Path("knowledge")
EXCLUDED = {"README.md", "INDEX.md"}


def discover_files():
    """发现所有需要重命名的文件，按目录分组"""
    groups = {}
    for root, dirs, files in os.walk(BASE_DIR):
        # 排除 .kimi 等隐藏目录
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        rel_root = Path(root).relative_to(BASE_DIR)
        md_files = [f for f in files if f.endswith('.md') and f not in EXCLUDED]
        # 过滤已合规的文件
        non_compliant = [f for f in md_files if not re.match(r'^\d{2}_[a-z0-9_]+\.md$', f)]
        if non_compliant:
            groups[str(rel_root)] = sorted(non_compliant)
    return groups


def generate_mappings(groups):
    """生成重命名映射：每个目录内按字母顺序编号"""
    mappings = []
    for rel_dir, files in sorted(groups.items()):
        for idx, old_name in enumerate(files, start=1):
            prefix = f"{idx:02d}"
            # 新文件名：全小写，空格/连字符转为下划线
            stem = Path(old_name).stem
            new_stem = stem.lower().replace('-', '_').replace(' ', '_').replace('.', '_')
            # 如果已经有前缀了（理论上不应该），去掉
            new_stem = re.sub(r'^\d{2}_', '', new_stem)
            new_name = f"{prefix}_{new_stem}.md"
            old_path = BASE_DIR / rel_dir / old_name
            new_path = BASE_DIR / rel_dir / new_name
            mappings.append((str(old_path), str(new_path), old_name, new_name, rel_dir))
    return mappings


def update_links(mappings):
    """更新 knowledge/ 内所有 .md 文件中的链接"""
    # 构建旧名 -> 新名的映射（用于相对路径替换）
    name_map = {}
    for old_path, new_path, old_name, new_name, rel_dir in mappings:
        # 精确匹配：目录/旧文件名.md
        old_pattern = re.escape(f"{rel_dir}/{old_name}")
        name_map[old_pattern] = f"{rel_dir}/{new_name}"
        # 也匹配 ./旧文件名.md（同一目录内相对链接）
        name_map[re.escape(f"./{old_name}")] = f"./{new_name}"
        name_map[re.escape(f"({old_name})")] = f"({new_name})"
        name_map[re.escape(f"({rel_dir}/{old_name})")] = f"({rel_dir}/{new_name})"

    for root, dirs, files in os.walk(BASE_DIR):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        for f in files:
            if not f.endswith('.md'):
                continue
            filepath = Path(root) / f
            content = filepath.read_text(encoding='utf-8')
            new_content = content
            changed = False
            for old_pat, new_pat in name_map.items():
                if old_pat in new_content:
                    new_content = new_content.replace(old_pat, new_pat)
                    changed = True
            if changed:
                if args.execute or args.batch or args.skip_rename:
                    filepath.write_text(new_content, encoding='utf-8')
                    print(f"  [UPDATED] {filepath}")
                else:
                    print(f"  [WOULD UPDATE] {filepath}")


def execute_rename(mappings):
    """执行 git mv 重命名"""
    for old_path, new_path, old_name, new_name, rel_dir in mappings:
        if not Path(old_path).exists():
            if Path(new_path).exists():
                print(f"  [SKIP] already renamed: {old_path} -> {new_path}")
            else:
                print(f"  [ERROR] source missing: {old_path}")
            continue
        if Path(new_path).exists():
            print(f"  [SKIP] target exists: {new_path}")
            continue
        subprocess.run(["git", "mv", old_path, new_path], check=True)
        print(f"  [RENAMED] {old_path} -> {new_path}")


def main():
    global args
    parser = argparse.ArgumentParser()
    parser.add_argument("--dry-run", action="store_true", help="仅打印映射表")
    parser.add_argument("--execute", action="store_true", help="实际执行")
    parser.add_argument("--batch", type=str, help="仅执行指定目录批次，如 00_start")
    parser.add_argument("--skip-rename", action="store_true", help="跳过 git mv，只更新链接")
    args = parser.parse_args()

    if not args.dry_run and not args.execute and not args.batch and not args.skip_rename:
        parser.print_help()
        return

    groups = discover_files()

    # 如果指定了 batch，只保留该目录
    if args.batch:
        if args.batch in groups:
            groups = {args.batch: groups[args.batch]}
        else:
            print(f"Batch '{args.batch}' not found or already compliant.")
            return

    mappings = generate_mappings(groups)

    print(f"=" * 60)
    print(f"knowledge/ 重命名映射表")
    print(f"=" * 60)
    print(f"总文件数: {len(mappings)}")
    print(f"涉及目录: {len(groups)}")
    print()

    for old_path, new_path, old_name, new_name, rel_dir in mappings:
        print(f"  [{rel_dir:30s}] {old_name:50s} -> {new_name}")

    if args.dry_run:
        print("\n[DRY RUN] 链接更新预览:")
        update_links(mappings)
        return

    if args.execute or args.batch or args.skip_rename:
        print("\n开始执行...")
        if not args.skip_rename:
            print("\n[1/2] 执行 git mv 重命名...")
            execute_rename(mappings)
        print("\n[2/2] 更新内部交叉链接...")
        update_links(mappings)
        print("\n完成!")


if __name__ == "__main__":
    main()
