#!/usr/bin/env python3
"""
修复 knowledge/ 中因重命名产生的死链接

策略：
1. 遍历所有 .md 文件中的链接
2. 如果链接目标不存在，尝试在同一目录找到 NN_ 前缀的匹配文件
3. 替换链接
"""

import os
import re
from pathlib import Path

BASE_DIR = Path("knowledge")


def get_new_name_map():
    """构建旧文件名 stem -> 新文件名 的映射"""
    mapping = {}
    for root, dirs, files in os.walk(BASE_DIR):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        rel_dir = str(Path(root).relative_to(BASE_DIR)).replace('\\', '/')
        for f in files:
            if not f.endswith('.md'):
                continue
            m = re.match(r'^(\d{2})_([a-z0-9_]+)\.md$', f)
            if m:
                # 新文件名已合规
                stem = m.group(2)
                mapping.setdefault(rel_dir, {})[stem] = f
    return mapping


def find_matching_new_file(old_link, new_name_map):
    """根据旧链接找到对应的新文件名"""
    old_path = Path(old_link)
    old_name = old_path.name
    old_stem = Path(old_name).stem.lower().replace('-', '_').replace(' ', '_').replace('.', '_')
    old_stem = re.sub(r'^\d{2}_', '', old_stem)

    # 确定目标目录
    if '/' in old_link or '\\' in old_link:
        link_dir = str(old_path.parent).replace('\\', '/')
    else:
        # 相对链接，需要在调用者上下文中解析
        return None, None

    if link_dir in new_name_map:
        dir_map = new_name_map[link_dir]
        if old_stem in dir_map:
            return link_dir, dir_map[old_stem]

    return None, None


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

            # 匹配所有 Markdown 链接: [text](path)
            for match in re.finditer(r'\[([^\]]*)\]\(([^)]+)\)', content):
                link_text = match.group(1)
                link_path = match.group(2)

                # 只处理 .md 链接
                if not link_path.endswith('.md'):
                    continue

                # 检查链接目标是否存在
                if '/' in link_path or '\\' in link_path:
                    target_dir = str(Path(link_path).parent).replace('\\', '/')
                    target_name = Path(link_path).name
                else:
                    # 同一目录内相对链接
                    target_dir = rel_root
                    target_name = link_path

                target_path = BASE_DIR / target_dir / target_name
                if target_path.exists():
                    continue  # 链接有效，跳过

                # 尝试找到新文件名
                link_dir, new_name = find_matching_new_file(link_path, new_name_map)
                if new_name:
                    # 构建新链接路径
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
