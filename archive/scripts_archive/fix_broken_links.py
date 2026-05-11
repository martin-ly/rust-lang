#!/usr/bin/env python3
"""
分析和修复 broken links 的脚本
"""
import json
import re
from collections import defaultdict
from pathlib import Path

# 读取 JSON 文件
with open('scripts/real_broken_links.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

false_positives = data.get('false_positives', [])
real_broken = data.get('real_broken', [])

print("=" * 80)
print("链接问题分析报告")
print("=" * 80)
print(f"\n误报数量 (false_positives): {len(false_positives)}")
print(f"真正损坏链接数量 (real_broken): {len(real_broken)}")

# 分类统计
categories = {
    'xxx_placeholder': [],  # xxx 占位符链接
    'nonexistent_dirs': [],  # 不存在的目录
    'external_url_format': [],  # 外部URL格式问题
    'template_examples': [],  # 模板文件中的示例链接
    'double_research_notes': [],  # research_notes/research_notes 重复路径
    'crates_not_exist': [],  # crates 下不存在的目录
    'software_design_theory': [],  # software_design_theory 相关
    'rust_formal_engineering': [],  # rust-formal-engineering-system 相关
    'archive_deprecated': [],  # archive/deprecated 相关
    'other_relative': [],  # 其他相对路径问题
}

for item in real_broken:
    target = item.get('link_target', '')
    file_path = item.get('file', '')
    resolved = item.get('resolved_path', '')
    
    # 1. xxx 占位符链接
    if '/xxx/' in target or 'xxx' in target.lower():
        categories['xxx_placeholder'].append(item)
    # 2. 外部URL格式问题 (以 < 开头)
    elif target.startswith('<'):
        categories['external_url_format'].append(item)
    # 3. 模板示例链接
    elif 'path/to/' in target or target in ['link', 'url', 'path']:
        categories['template_examples'].append(item)
    # 4. research_notes 重复路径
    elif 'research_notes/research_notes' in resolved:
        categories['double_research_notes'].append(item)
    # 5. software_design_theory
    elif 'software_design_theory' in target:
        categories['software_design_theory'].append(item)
    # 6. rust-formal-engineering-system
    elif 'rust-formal-engineering-system' in target:
        categories['rust_formal_engineering'].append(item)
    # 7. archive/deprecated
    elif 'archive/deprecated' in target:
        categories['archive_deprecated'].append(item)
    # 8. crates 下不存在的目录
    elif 'crates/' in target and ('examples/' in target or 'src/' in target or 'tests/' in target or 'benches/' in target or 'docs/' in target):
        categories['crates_not_exist'].append(item)
    # 9. 其他
    else:
        categories['other_relative'].append(item)

print("\n" + "=" * 80)
print("问题分类统计")
print("=" * 80)

for cat_name, items in categories.items():
    print(f"\n{cat_name}: {len(items)} 个")
    if len(items) > 0 and len(items) <= 5:
        for item in items[:3]:
            print(f"  - {item.get('file', '')}: {item.get('link_target', '')}")
    elif len(items) > 5:
        print(f"  示例:")
        for item in items[:3]:
            print(f"    - {item.get('file', '')}: {item.get('link_target', '')}")

# 按文件统计
files_with_issues = defaultdict(list)
for item in real_broken:
    file_path = item.get('file', '')
    files_with_issues[file_path].append(item)

print("\n" + "=" * 80)
print(f"涉及文件数量: {len(files_with_issues)}")
print("=" * 80)

# 找出问题最多的文件
sorted_files = sorted(files_with_issues.items(), key=lambda x: len(x[1]), reverse=True)
print("\n问题最多的前 20 个文件:")
for file_path, issues in sorted_files[:20]:
    print(f"  {file_path}: {len(issues)} 个问题")

# 生成修复报告
print("\n" + "=" * 80)
print("修复方案建议")
print("=" * 80)

print("""
1. **xxx 占位符链接** (xxx_placeholder)
   - 这些是指向 crates/xxx/ 的占位符链接
   - 建议：将 xxx 替换为实际的 crate 名称，或添加说明文字表明这是示例

2. **外部URL格式问题** (external_url_format)
   - Markdown 链接中 URL 被 < > 包裹且格式不正确
   - 建议：修复为 [text](url) 格式，移除 < >

3. **模板示例链接** (template_examples)
   - 路径包含 path/to/ 或是 link/url/path 等占位符
   - 建议：替换为实际文档路径或添加 TODO 标记

4. **research_notes 重复路径** (double_research_notes)
   - 链接路径包含 research_notes/research_notes/
   - 建议：移除重复部分

5. **software_design_theory 目录不存在** (software_design_theory)
   - 链接指向不存在的 software_design_theory 子目录
   - 建议：创建目录或修改链接路径

6. **rust-formal-engineering-system 目录不存在** (rust_formal_engineering)
   - 链接指向不存在的 rust-formal-engineering-system 子目录
   - 建议：创建目录或修改链接路径

7. **archive/deprecated 目录不存在** (archive_deprecated)
   - 链接指向不存在的 archive/deprecated 目录
   - 建议：检查是否需要创建目录或修改链接

8. **crates 目录不存在** (crates_not_exist)
   - 链接指向 crates 下的 examples/tests/benches/docs 等子目录
   - 建议：检查 crates 实际结构或创建对应目录

9. **其他相对路径问题** (other_relative)
   - 需要逐一检查并修复
""")

# 保存详细报告
report_path = 'scripts/link_analysis_report.txt'
with open(report_path, 'w', encoding='utf-8') as f:
    f.write("=" * 80 + "\n")
    f.write("链接问题详细分析报告\n")
    f.write("=" * 80 + "\n\n")
    
    f.write(f"误报数量: {len(false_positives)}\n")
    f.write(f"真正损坏链接数量: {len(real_broken)}\n\n")
    
    for cat_name, items in categories.items():
        if items:
            f.write(f"\n{'=' * 80}\n")
            f.write(f"分类: {cat_name} ({len(items)} 个问题)\n")
            f.write('=' * 80 + "\n")
            for item in items:
                f.write(f"\n文件: {item.get('file', '')}\n")
                f.write(f"  链接文本: {item.get('link_text', '')}\n")
                f.write(f"  链接目标: {item.get('link_target', '')}\n")
                f.write(f"  解析路径: {item.get('resolved_path', '')}\n")
                f.write(f"  建议: {item.get('suggestion', '')}\n")

print(f"\n\n详细报告已保存到: {report_path}")
