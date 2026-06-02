#!/usr/bin/env python3
"""
修复 knowledge/ 中因重命名产生的死链接 v2

正确处理相对路径（./ ../ 等）
"""

import os
import re
from pathlib import Path

BASE_DIR = Path("knowledge")


def get_new_name_map():
    """构建目录 -> {旧stem: 新文件名} 的映射"""
    mapping = {}
    for root, dirs, files in os.walk(BASE_DIR):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        rel_dir = str(Path(root).relative_to(BASE_DIR)).replace('\\', '/')
        mapping[rel_dir] = {}
        for f in files:
            if not f.endswith('.md'):
                continue
            m = re.match(r'^(\d{2})_([a-z0-9_]+)\.md$', f)
            if m:
                stem = m.group(2)
                mapping[rel_dir][stem] = f
    return mapping


def resolve_link(link_path, current_dir):
    """将相对链接解析为相对于 knowledge/ 的目标目录和文件名"""
    path = Path(link_path)
    name = path.name

    if link_path.startswith('/'):
        # 绝对路径（不应该出现）
        target_dir = str(path.parent).replace('\\', '/').lstrip('/')
    elif link_path.startswith('../'):
        # 向上解析
        target_dir = Path(current_dir) / path.parent
        target_dir = str(target_dir).replace('\\', '/')
    elif link_path.startswith('./'):
        target_dir = current_dir
    else:
        # 无前缀，可能是同一目录或带目录
        if '/' in link_path or '\\' in link_path:
            target_dir = str(path.parent).replace('\\', '/')
        else:
            target_dir = current_dir

    return target_dir, name


def get_stem(name):
    """提取可用于匹配的 stem"""
    stem = Path(name).stem.lower().replace('-', '_').replace(' ', '_').replace('.', '_')
    stem = re.sub(r'^\d{2}_', '', stem)
    return stem


def fix_all_links():
    new_name_map = get_new_name_map()
    total_fixed = 0
    total_files = 0

    for root, dirs, files in os.walk(BASE_DIR):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        rel_root = str(Path(root).relative_to(BASE_DIR)).replace('\\', '/')

        for f in files:
            if not f.endswith('.md'):
                continue

            filepath = Path(root) / f
            content = filepath.read_text(encoding='utf-8')
            new_content = content
            changed = False

            for match in re.finditer(r'\[([^\]]*)\]\(([^)]+)\)', content):
                link_text = match.group(1)
                link_path = match.group(2)

                if not link_path.endswith('.md'):
                    continue

                target_dir, target_name = resolve_link(link_path, rel_root)
                target_path = BASE_DIR / target_dir / target_name

                if target_path.exists():
                    continue

                # 尝试匹配新文件名
                stem = get_stem(target_name)
                dir_map = new_name_map.get(target_dir, {})
                new_name = dir_map.get(stem)

                if new_name:
                    # 构建新链接
                    if '/' in link_path or '\\' in link_path:
                        new_link = str(Path(link_path).parent / new_name).replace('\\', '/')
                    else:
                        new_link = new_name

                    old_full = f'[{link_text}]({link_path})'
                    new_full = f'[{link_text}]({new_link})'
                    new_content = new_content.replace(old_full, new_full)
                    changed = True
                    total_fixed += 1
                    print(f"  [{filepath}] {link_path} -> {new_link}")

            if changed:
                filepath.write_text(new_content, encoding='utf-8')
                total_files += 1
                print(f"[FIXED] {filepath}")

    print(f"\n总计: 修复 {total_fixed} 个链接, 更新 {total_files} 个文件")


if __name__ == "__main__":
    fix_all_links()
