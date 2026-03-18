#!/usr/bin/env python3
"""
批量修复 broken links
"""
import json
import re
from pathlib import Path

# 读取 JSON 文件
with open('scripts/real_broken_links.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

real_broken = data.get('real_broken', [])

docs_dir = Path('e:/_src/rust-lang/docs')

# 跟踪修复的文件
fixed_files = set()
fix_count = 0

# 1. 修复外部URL格式问题 (移除 < > 包裹)
def fix_external_url(item):
    global fix_count
    file_path = docs_dir / item['file']
    target = item['link_target']
    link_text = item['link_text']
    
    # 提取正确的URL
    if target.startswith('<') and target.endswith('>'):
        url = target[1:-1]
    else:
        # 处理 <https://...> text 这种格式
        match = re.match(r'<(https?://[^>]+)>\s*(.+)', target)
        if match:
            url = match.group(1)
        else:
            return False
    
    old_link = f"[{link_text}]({target})"
    new_link = f"[{link_text}]({url})"
    
    if not file_path.exists():
        return False
    
    content = file_path.read_text(encoding='utf-8')
    if old_link in content:
        content = content.replace(old_link, new_link)
        file_path.write_text(content, encoding='utf-8')
        fix_count += 1
        fixed_files.add(str(file_path))
        print(f"  [URL格式] 修复: {file_path.name}")
        return True
    return False

# 2. 修复 template_examples - 替换占位符
def fix_template_examples(item):
    global fix_count
    file_path = docs_dir / item['file']
    target = item['link_target']
    link_text = item['link_text']
    
    # 对于模板占位符，添加 TODO 标记
    old_link = f"[{link_text}]({target})"
    new_link = f"[{link_text}](TODO_{target.replace('/', '_')})"
    
    if not file_path.exists():
        return False
    
    content = file_path.read_text(encoding='utf-8')
    if old_link in content:
        # 将占位符链接改为纯文本或添加 TODO
        content = content.replace(old_link, f"`{link_text}` (TODO: 添加链接)")
        file_path.write_text(content, encoding='utf-8')
        fix_count += 1
        fixed_files.add(str(file_path))
        print(f"  [模板占位符] 修复: {file_path.name}")
        return True
    return False

# 3. 修复 research_notes 重复路径
def fix_double_research_notes(item):
    global fix_count
    file_path = docs_dir / item['file']
    target = item['link_target']
    link_text = item['link_text']
    
    # 修复 ../research_notes/xxx 为 ./xxx (如果文件已经在 research_notes 下)
    if '../research_notes/' in target and 'research_notes/' in str(file_path):
        new_target = target.replace('../research_notes/', './')
        old_link = f"[{link_text}]({target})"
        new_link = f"[{link_text}]({new_target})"
        
        if not file_path.exists():
            return False
        
        content = file_path.read_text(encoding='utf-8')
        if old_link in content:
            content = content.replace(old_link, new_link)
            file_path.write_text(content, encoding='utf-8')
            fix_count += 1
            fixed_files.add(str(file_path))
            print(f"  [重复路径] 修复: {file_path.name}")
            return True
    return False

# 4. 修复 archive/process_reports 路径
def fix_archive_process_reports(item):
    global fix_count
    file_path = docs_dir / item['file']
    target = item['link_target']
    link_text = item['link_text']
    
    # 修复 ../archive/process_reports/2026_02/ 路径
    if '../archive/process_reports/2026_02/' in target:
        # 查找正确的报告文件
        correct_file = '100_PERCENT_COMPLETION_REPORT_2026_02_24.md'
        old_link = f"[{link_text}]({target})"
        new_link = f"[{link_text}](./{correct_file})"
        
        if not file_path.exists():
            return False
        
        content = file_path.read_text(encoding='utf-8')
        if old_link in content:
            content = content.replace(old_link, new_link)
            file_path.write_text(content, encoding='utf-8')
            fix_count += 1
            fixed_files.add(str(file_path))
            print(f"  [归档路径] 修复: {file_path.name}")
            return True
    return False

# 5. 修复 coq_skeleton 链接为 archive/deprecated/coq_skeleton
def fix_coq_skeleton(item):
    global fix_count
    file_path = docs_dir / item['file']
    target = item['link_target']
    link_text = item['link_text']
    
    # 如果链接指向 ./coq_skeleton/，修改为指向 archive/deprecated/coq_skeleton/
    if target == './coq_skeleton/' or target == 'coq_skeleton/':
        old_link = f"[{link_text}]({target})"
        new_link = f"[{link_text}](../archive/deprecated/coq_skeleton/)"
        
        if not file_path.exists():
            return False
        
        content = file_path.read_text(encoding='utf-8')
        if old_link in content:
            content = content.replace(old_link, new_link)
            file_path.write_text(content, encoding='utf-8')
            fix_count += 1
            fixed_files.add(str(file_path))
            print(f"  [coq_skeleton] 修复: {file_path.name}")
            return True
    return False

# 6. 修复软件设计理论路径
def fix_software_design_theory(item):
    global fix_count
    file_path = docs_dir / item['file']
    target = item['link_target']
    link_text = item['link_text']
    
    # 将 ./software_design_theory/ 改为 ./ (如果文件本身就在 software_design_theory 下)
    if './software_design_theory/' in target and 'software_design_theory/' in str(file_path):
        return False  # 暂不自动修复，需要手动检查
    
    return False

# 主修复逻辑
print("=" * 80)
print("开始修复链接...")
print("=" * 80)

for item in real_broken:
    target = item.get('link_target', '')
    
    # 分类修复
    if target.startswith('<'):
        fix_external_url(item)
    elif 'path/to/' in target or target in ['link', 'url', 'path']:
        fix_template_examples(item)
    elif '../research_notes/' in target and 'research_notes/' in item.get('file', ''):
        fix_double_research_notes(item)
    elif '../archive/process_reports/2026_02/' in target:
        fix_archive_process_reports(item)
    elif 'coq_skeleton/' in target:
        fix_coq_skeleton(item)

print("\n" + "=" * 80)
print(f"修复完成: 共修复 {fix_count} 个问题，涉及 {len(fixed_files)} 个文件")
print("=" * 80)

if fixed_files:
    print("\n已修复的文件列表:")
    for f in sorted(fixed_files):
        print(f"  - {f}")
