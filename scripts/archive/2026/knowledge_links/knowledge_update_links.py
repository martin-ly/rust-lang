#!/usr/bin/env python3
"""
单独更新 knowledge/ 内所有 Markdown 链接的脚本
用于在重命名完成后统一更新链接
"""

import os
import re
from pathlib import Path

BASE_DIR = Path("knowledge")
EXCLUDED = {"README.md", "INDEX.md"}


def get_all_mappings():
    """获取所有旧名->新名的映射"""
    name_map = {}
    for root, dirs, files in os.walk(BASE_DIR):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        rel_dir = str(Path(root).relative_to(BASE_DIR)).replace('\\', '/')
        for f in files:
            if not f.endswith('.md') or f in EXCLUDED:
                continue
            # 如果文件名已合规，跳过
            if re.match(r'^\d{2}_[a-z0-9_]+\.md$', f):
                continue
            # 生成新文件名
            stem = Path(f).stem
            new_stem = stem.lower().replace('-', '_').replace(' ', '_').replace('.', '_')
            new_stem = re.sub(r'^\d{2}_', '', new_stem)
            # 需要知道它在目录中的序号，这里简单处理：不生成序号，只做名称替换
            # 实际上这个脚本应该在重命名后运行，只更新那些已经重命名了的文件的链接
            pass
    return name_map


def update_all_links():
    """扫描所有旧文件名模式并更新为新文件名"""
    # 先收集所有已重命名文件的映射（新文件名合规的文件）
    rename_map = {}
    for root, dirs, files in os.walk(BASE_DIR):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        rel_dir = str(Path(root).relative_to(BASE_DIR)).replace('\\', '/')
        for f in files:
            if not f.endswith('.md') or f in EXCLUDED:
                continue
            # 检查是否是新命名格式
            m = re.match(r'^(\d{2})_([a-z0-9_]+)\.md$', f)
            if m:
                prefix, stem = m.groups()
                # 尝试推断旧文件名（去掉前缀，恢复原始大小写不可能，但我们可以匹配常见的变体）
                # 更好的方式：收集所有可能的不合规文件名，通过扫描来匹配
                pass

    # 更直接的方式：收集所有仍然存在于文本中的旧文件名引用
    # 遍历所有文件，找到形如 (xxx.md) 或 (dir/xxx.md) 的链接
    # 如果 xxx.md 在当前目录中不存在但有一个 NN_xxx.md 存在，则替换
    for root, dirs, files in os.walk(BASE_DIR):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        rel_dir = str(Path(root).relative_to(BASE_DIR)).replace('\\', '/')
        md_files = [f for f in files if f.endswith('.md')]

        for filepath in [Path(root) / f for f in md_files]:
            content = filepath.read_text(encoding='utf-8')
            new_content = content
            changed = False

            # 匹配所有 markdown 链接中的 .md 路径
            # 模式: ](path/to/file.md) 或 ](file.md) 或 ](./file.md)
            for match in re.finditer(r'\(([^)]*\.md)\)', content):
                old_link = match.group(1)
                old_name = Path(old_link).name

                # 如果 old_name 已经合规，跳过
                if re.match(r'^\d{2}_[a-z0-9_]+\.md$', old_name):
                    continue

                # 尝试找到对应的新文件名
                # 在同一目录或链接指向的目录中查找
                link_dir = rel_dir if '/' not in old_link else str(Path(old_link).parent).replace('\\', '/')
                target_dir = BASE_DIR / link_dir

                # 在新命名的文件中查找匹配
                found_new = None
                if target_dir.exists():
                    for candidate in target_dir.glob('*.md'):
                        cname = candidate.name
                        cm = re.match(r'^\d{2}_([a-z0-9_]+)\.md$', cname)
                        if cm:
                            # 比较 stem（去掉数字前缀后的小写形式）
                            cstem = cm.group(1)
                            old_stem = Path(old_name).stem.lower().replace('-', '_').replace(' ', '_').replace('.', '_')
                            old_stem = re.sub(r'^\d{2}_', '', old_stem)
                            if cstem == old_stem:
                                found_new = cname
                                break

                if found_new:
                    new_link = str(Path(old_link).parent / found_new).replace('\\', '/')
                    if old_link.startswith('./') and not new_link.startswith('./'):
                        new_link = './' + new_link
                    new_content = new_content.replace(f'({old_link})', f'({new_link})')
                    changed = True
                    print(f"  [{filepath}] ({old_link}) -> ({new_link})")

            if changed:
                filepath.write_text(new_content, encoding='utf-8')
                print(f"[UPDATED] {filepath}")


if __name__ == "__main__":
    print("开始更新 knowledge/ 内所有 Markdown 链接...")
    update_all_links()
    print("完成!")
