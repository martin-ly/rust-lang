#!/usr/bin/env python3
"""
批量修复 concept/ 下被错误填入目录结构的 **Summary** 字段。
基于 **EN** 和 **定位** 元数据生成简洁的英文摘要。
"""

import glob
import re
import os

BAD_PATTERNS = ['目录', '变更日志', '- [', '](#']

def extract_field(content, field_name):
    """提取 front matter 中的字段值，支持多行直到下一个 > 开头或空行"""
    # 匹配 **字段名**: 后面的内容
    pattern = rf'\*\*{re.escape(field_name)}\*\*:\s*(.*?)(?=\n>|\n#|\n\n|\Z)'
    m = re.search(pattern, content, re.DOTALL)
    if m:
        return ' '.join(m.group(1).strip().split())
    return None

def is_bad_summary(summary):
    if not summary:
        return True
    s = summary.strip()
    if len(s) < 10:
        return True
    for p in BAD_PATTERNS:
        if p in s:
            return True
    return False

def generate_summary(en_title, zh_position, filename):
    """基于可用元数据生成最小化英文摘要"""
    topic = en_title or os.path.basename(filename).replace('.md', '')
    topic = topic.split('（')[0].strip()
    
    desc_parts = []
    if zh_position:
        # 提取关键词生成简单描述
        if '形式化' in zh_position or 'Formal' in zh_position:
            desc_parts.append("formal methods foundations")
        if '示例' in zh_position or '代码' in zh_position:
            desc_parts.append("practical examples")
        if '对比' in zh_position or '比较' in zh_position:
            desc_parts.append("cross-language comparison")
        if '心智模型' in zh_position or '模型' in zh_position:
            desc_parts.append("mental model building")
        if '分析' in zh_position or '机制' in zh_position:
            desc_parts.append("mechanism analysis")
    
    if desc_parts:
        desc = "Core Rust concept covering " + ", ".join(desc_parts) + "."
    else:
        desc = "Core Rust concept with theoretical foundations and practical applications."
    
    return f"> **Summary**: {topic}. {desc}"

def fix_file(path):
    with open(path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 找到 Summary 行
    summary_match = re.search(r'(\*\*Summary\*\*:\s*)(.+?)(?=\n>|\n#|\Z)', content, re.DOTALL)
    if not summary_match:
        return False, "no summary field"
    
    summary_val = summary_match.group(2)
    if not is_bad_summary(summary_val):
        return False, "summary ok"
    
    en_title = extract_field(content, 'EN')
    zh_position = extract_field(content, '定位')
    
    new_summary = generate_summary(en_title, zh_position, path)
    
    # 替换 Summary 行（只替换该字段值，保留前面的 **Summary**: ）
    old_block = summary_match.group(0)
    new_block = f"**Summary**: {new_summary.split(':', 1)[1].strip()}"
    
    # 由于 Summary 可能在单行或多行，我们用更精确的方式替换
    prefix = summary_match.group(1)  # "**Summary**: "
    new_content = content.replace(old_block, prefix + new_summary.split(':', 1)[1].strip(), 1)
    
    if new_content == content:
        return False, "replace failed"
    
    with open(path, 'w', encoding='utf-8') as f:
        f.write(new_content)
    return True, new_summary

def main():
    files = glob.glob('concept/**/*.md', recursive=True)
    files = [f for f in files if 'archive' not in f]
    
    fixed = 0
    skipped = 0
    errors = []
    
    for path in files:
        try:
            changed, msg = fix_file(path)
            if changed:
                fixed += 1
                if fixed <= 3:
                    print(f"[FIXED] {path}")
                    print(f"        → {msg}")
            else:
                skipped += 1
        except Exception as e:
            errors.append((path, str(e)))
    
    print(f"\n=== Results ===")
    print(f"Fixed:   {fixed}")
    print(f"Skipped: {skipped}")
    print(f"Errors:  {len(errors)}")
    for p, e in errors[:5]:
        print(f"  ERROR {p}: {e}")

if __name__ == '__main__':
    main()
