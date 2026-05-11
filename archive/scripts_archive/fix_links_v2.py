#!/usr/bin/env python3
"""
智能修复 broken links - 版本2
首先验证链接是否真的损坏，然后进行修复
"""
import json
import re
from pathlib import Path
from collections import defaultdict

# 路径配置
BASE_DIR = Path('e:/_src/rust-lang')
DOCS_DIR = BASE_DIR / 'docs'

# 读取 JSON 文件
with open('scripts/real_broken_links.json', 'r', encoding='utf-8') as f:
    data = json.load(f)

real_broken = data.get('real_broken', [])

# 修复统计
fixed_count = 0
fixed_files = set()
skip_count = 0

# 缓存文件内容
file_cache = {}

def get_file_content(file_path):
    """获取文件内容，带缓存"""
    abs_path = str(file_path.absolute())
    if abs_path not in file_cache:
        try:
            file_cache[abs_path] = file_path.read_text(encoding='utf-8')
        except Exception as e:
            print(f"  错误: 无法读取文件 {file_path}: {e}")
            return None
    return file_cache[abs_path]

def save_file_content(file_path, content):
    """保存文件内容"""
    file_path.write_text(content, encoding='utf-8')
    abs_path = str(file_path.absolute())
    file_cache[abs_path] = content

# 1. 修复外部URL格式问题
# 问题: <https://...> text 这种格式在 Markdown 中是错误的
# 应该改为: [text](https://...)
def fix_external_url_issues():
    global fixed_count, skip_count
    
    pattern = re.compile(r'\[<([^>]+)>\s+([^\]]+)\]\(\)')
    
    for item in real_broken:
        target = item.get('link_target', '')
        link_text = item.get('link_text', '')
        file_rel = item.get('file', '')
        
        # 检测 <https://...> 格式的URL后面跟着空格和文本
        if target.startswith('<') and '>' in target and not target.endswith('>'):
            file_path = DOCS_DIR / file_rel
            if not file_path.exists():
                continue
            
            content = get_file_content(file_path)
            if content is None:
                continue
            
            # 查找并修复这种格式
            # 格式可能是: [text](<url> something)
            old_pattern = f"[{link_text}]({re.escape(target)})"
            
            if old_pattern in content:
                # 提取URL和实际文本
                match = re.match(r'<(https?://[^>]+)>\s*(.+)', target)
                if match:
                    url = match.group(1)
                    new_target = url
                    new_pattern = f"[{link_text}]({new_target})"
                    content = content.replace(old_pattern, new_pattern)
                    save_file_content(file_path, content)
                    fixed_count += 1
                    fixed_files.add(str(file_path))
                    print(f"  [修复外部URL] {file_rel}: {link_text}")

# 2. 修复占位符链接
def fix_placeholder_links():
    global fixed_count
    
    for item in real_broken:
        target = item.get('link_target', '')
        link_text = item.get('link_text', '')
        file_rel = item.get('file', '')
        
        # 检测 xxx 占位符
        if '/xxx/' in target or target in ['link', 'url', 'path', 'path/to/doc.md']:
            file_path = DOCS_DIR / file_rel
            if not file_path.exists():
                continue
            
            content = get_file_content(file_path)
            if content is None:
                continue
            
            old_link = f"[{link_text}]({target})"
            
            if old_link in content:
                # 将占位符改为纯文本 + TODO 标记
                new_text = f"`{link_text}` ⚠️ (链接待补充)"
                content = content.replace(old_link, new_text)
                save_file_content(file_path, content)
                fixed_count += 1
                fixed_files.add(str(file_path))
                print(f"  [修复占位符] {file_rel}: {link_text}")

# 3. 修复重复路径问题
# 例如: research_notes/research_notes/xxx -> research_notes/xxx
def fix_duplicate_paths():
    global fixed_count
    
    for item in real_broken:
        target = item.get('link_target', '')
        link_text = item.get('link_text', '')
        file_rel = item.get('file', '')
        
        # 检测重复路径
        if 'research_notes/research_notes/' in target or '../research_notes/' in target:
            file_path = DOCS_DIR / file_rel
            if not file_path.exists():
                continue
            
            content = get_file_content(file_path)
            if content is None:
                continue
            
            # 如果文件本身就在 research_notes 目录下
            if 'research_notes/' in file_rel:
                old_link = f"[{link_text}]({target})"
                
                if old_link in content:
                    # 修复重复路径
                    new_target = target.replace('../research_notes/', './')
                    new_target = new_target.replace('research_notes/research_notes/', 'research_notes/')
                    new_link = f"[{link_text}]({new_target})"
                    content = content.replace(old_link, new_link)
                    save_file_content(file_path, content)
                    fixed_count += 1
                    fixed_files.add(str(file_path))
                    print(f"  [修复重复路径] {file_rel}: {link_text}")

# 4. 修复 archive/process_reports 路径
def fix_archive_paths():
    global fixed_count
    
    for item in real_broken:
        target = item.get('link_target', '')
        link_text = item.get('link_text', '')
        file_rel = item.get('file', '')
        
        if '../archive/process_reports/2026_02/' in target:
            file_path = DOCS_DIR / file_rel
            if not file_path.exists():
                continue
            
            content = get_file_content(file_path)
            if content is None:
                continue
            
            old_link = f"[{link_text}]({target})"
            
            if old_link in content:
                # 修复为正确的相对路径
                new_target = '../../../100_PERCENT_COMPLETION_REPORT_2026_02_24.md'
                new_link = f"[{link_text}]({new_target})"
                content = content.replace(old_link, new_link)
                save_file_content(file_path, content)
                fixed_count += 1
                fixed_files.add(str(file_path))
                print(f"  [修复归档路径] {file_rel}: {link_text}")

# 主函数
print("=" * 80)
print("链接修复工具 v2")
print("=" * 80)

print("\n步骤 1: 修复外部URL格式问题...")
fix_external_url_issues()

print("\n步骤 2: 修复占位符链接...")
fix_placeholder_links()

print("\n步骤 3: 修复重复路径问题...")
fix_duplicate_paths()

print("\n步骤 4: 修复归档路径问题...")
fix_archive_paths()

print("\n" + "=" * 80)
print(f"修复完成!")
print(f"  - 修复问题数: {fixed_count}")
print(f"  - 涉及文件数: {len(fixed_files)}")
print("=" * 80)

if fixed_files:
    print("\n已修复的文件列表:")
    for f in sorted(fixed_files):
        print(f"  - {Path(f).name}")
