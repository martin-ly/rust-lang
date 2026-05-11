#!/usr/bin/env python3
"""
最终版链接修复脚本
"""
import json
import re
from pathlib import Path
from collections import defaultdict

BASE_DIR = Path('e:/_src/rust-lang')
DOCS_DIR = BASE_DIR / 'docs'

# 读取 JSON 文件
with open('scripts/real_broken_links.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

real_broken = data.get('real_broken', [])

# 分类统计
stats = defaultdict(int)
files_modified = set()

print("=" * 80)
print("链接问题修复报告")
print("=" * 80)

# 分类并输出统计
for item in real_broken:
    target = item.get('link_target', '')
    
    if '/xxx/' in target or 'xxx' in target:
        stats['xxx_placeholder'] += 1
    elif target.startswith('<'):
        stats['external_url_format'] += 1
    elif 'path/to/' in target or target in ['link', 'url', 'path']:
        stats['template_examples'] += 1
    elif 'software_design_theory' in target:
        stats['software_design_theory'] += 1
    elif 'rust-formal-engineering-system' in target:
        stats['rust_formal_engineering'] += 1
    elif 'archive/deprecated' in target:
        stats['archive_deprecated'] += 1
    elif 'crates/' in target:
        stats['crates_broken'] += 1
    elif 'research_notes/research_notes' in target:
        stats['double_path'] += 1
    else:
        stats['other'] += 1

print("\n问题分类统计:")
for cat, count in sorted(stats.items(), key=lambda x: -x[1]):
    print(f"  {cat}: {count}")

print(f"\n总计: {len(real_broken)} 个问题")

# 创建修复报告
report_lines = []
report_lines.append("# 链接修复报告\n")
report_lines.append(f"生成日期: 2026-03-19\n\n")
report_lines.append("## 问题统计\n\n")
report_lines.append("| 类别 | 数量 |\n")
report_lines.append("|------|------|\n")
for cat, count in sorted(stats.items(), key=lambda x: -x[1]):
    report_lines.append(f"| {cat} | {count} |\n")
report_lines.append(f"| **总计** | **{len(real_broken)}** |\n\n")

# 按类别列出问题
report_lines.append("## 问题详情\n\n")

categories = {
    'xxx_placeholder': 'xxx 占位符链接',
    'external_url_format': '外部URL格式问题',
    'template_examples': '模板示例链接',
    'software_design_theory': 'software_design_theory 目录不存在',
    'rust_formal_engineering': 'rust-formal-engineering-system 目录不存在',
    'archive_deprecated': 'archive/deprecated 目录不存在',
    'crates_broken': 'crates 子目录不存在',
    'double_path': '路径重复',
    'other': '其他问题'
}

# 按类别分组
by_category = defaultdict(list)
for item in real_broken:
    target = item.get('link_target', '')
    
    if '/xxx/' in target or 'xxx' in target:
        cat = 'xxx_placeholder'
    elif target.startswith('<'):
        cat = 'external_url_format'
    elif 'path/to/' in target or target in ['link', 'url', 'path']:
        cat = 'template_examples'
    elif 'software_design_theory' in target:
        cat = 'software_design_theory'
    elif 'rust-formal-engineering-system' in target:
        cat = 'rust_formal_engineering'
    elif 'archive/deprecated' in target:
        cat = 'archive_deprecated'
    elif 'crates/' in target:
        cat = 'crates_broken'
    elif 'research_notes/research_notes' in target:
        cat = 'double_path'
    else:
        cat = 'other'
    
    by_category[cat].append(item)

# 为每个类别生成详情
for cat_key, cat_name in categories.items():
    items = by_category.get(cat_key, [])
    if not items:
        continue
    
    report_lines.append(f"### {cat_name} ({len(items)}个)\n\n")
    
    # 按文件分组
    by_file = defaultdict(list)
    for item in items:
        by_file[item.get('file', 'unknown')].append(item)
    
    for file_path, file_items in sorted(by_file.items()):
        report_lines.append(f"#### {file_path}\n\n")
        for item in file_items:
            link_text = item.get('link_text', '')
            target = item.get('link_target', '')
            suggestion = item.get('suggestion', '').replace('\n', ' ')
            report_lines.append(f"- **{link_text}** -> `{target}`\n")
            if suggestion:
                report_lines.append(f"  - 建议: {suggestion[:100]}...\n")
        report_lines.append("\n")

# 保存报告
report_path = 'scripts/LINK_FIX_REPORT.md'
with open(report_path, 'w', encoding='utf-8') as f:
    f.writelines(report_lines)

print(f"\n详细报告已保存: {report_path}")

# 创建修复脚本内容
fix_script = '''#!/usr/bin/env python3
"""
自动修复脚本 - 由 fix_links_final.py 生成
"""
from pathlib import Path
import re

DOCS_DIR = Path('e:/_src/rust-lang/docs')

def fix_file(file_path, replacements):
    """在文件中执行替换"""
    try:
        content = file_path.read_text(encoding='utf-8')
        original = content
        for old, new in replacements:
            content = content.replace(old, new)
        if content != original:
            file_path.write_text(content, encoding='utf-8')
            return True
    except Exception as e:
        print(f"Error fixing {file_path}: {e}")
    return False

# 修复定义
print("开始修复...")

'''

# 为每个类别添加修复逻辑
print("\n建议的修复操作:")

# 1. xxx_placeholder - 需要手动创建目录或修改链接
if by_category.get('xxx_placeholder'):
    print("\n[xxx_placeholder]")
    print("  建议: 创建 crates/xxx/ 目录或修改链接为实际crate名称")

# 2. external_url_format - 需要修复格式
if by_category.get('external_url_format'):
    print("\n[external_url_format]")
    print("  建议: 修复 <https://...> text 格式为 [text](https://...)")

# 3. template_examples - 需要修改为实际链接
if by_category.get('template_examples'):
    print("\n[template_examples]")
    print("  建议: 替换 path/to/doc.md 等占位符为实际路径")

# 4. software_design_theory - 需要创建目录
if by_category.get('software_design_theory'):
    print("\n[software_design_theory]")
    print("  建议: 创建 docs/research_notes/software_design_theory/ 及其子目录")
    print("  或: 修改链接指向正确的位置")

# 5. rust_formal_engineering - 需要创建目录
if by_category.get('rust_formal_engineering'):
    print("\n[rust_formal_engineering]")
    print("  建议: 创建 docs/rust-formal-engineering-system/ 及其子目录")
    print("  或: 修改链接指向正确的位置")

# 6. archive_deprecated - 需要创建目录
if by_category.get('archive_deprecated'):
    print("\n[archive_deprecated]")
    print("  建议: 创建 docs/archive/deprecated/ 目录")

# 7. crates_broken - 需要创建目录
if by_category.get('crates_broken'):
    print("\n[crates_broken]")
    print("  建议: 在对应 crates 下创建 examples/tests/benches/docs 目录")

print("\n" + "=" * 80)
