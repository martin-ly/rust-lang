#!/usr/bin/env python3
"""
验证 JSON 中报告的链接问题是否真实存在
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

print("=" * 80)
print("验证链接问题")
print("=" * 80)

verified_issues = []
not_found = []

for item in real_broken[:50]:  # 只验证前50个以加快速度
    target = item.get('link_target', '')
    link_text = item.get('link_text', '')
    file_rel = item.get('file', '')
    
    file_path = DOCS_DIR / file_rel
    
    if not file_path.exists():
        print(f"文件不存在: {file_rel}")
        continue
    
    try:
        content = file_path.read_text(encoding='utf-8')
    except Exception as e:
        print(f"读取错误 {file_rel}: {e}")
        continue
    
    # 构造链接模式
    link_pattern = f"[{link_text}]({target})"
    
    if link_pattern in content:
        verified_issues.append(item)
        print(f"✓ 找到: {file_rel} -> {target[:50]}...")
    else:
        not_found.append(item)
        print(f"✗ 未找到: {file_rel} -> {link_text} -> {target[:50]}...")

print("\n" + "=" * 80)
print(f"验证结果:")
print(f"  - 确认存在的问题: {len(verified_issues)}")
print(f"  - 未找到的链接: {len(not_found)}")
print("=" * 80)

# 显示几个未找到的例子
if not_found:
    print("\n未找到的链接示例:")
    for item in not_found[:5]:
        print(f"  文件: {item.get('file', '')}")
        print(f"  文本: {item.get('link_text', '')}")
        print(f"  目标: {item.get('link_target', '')}")
        print()
