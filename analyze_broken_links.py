#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""分析断链类型并分类"""

import json
import re

def main():
    with open('docs/link_check_report.json', 'r', encoding='utf-8') as f:
        data = json.load(f)

    # 分类断链
    false_positives = []  # 代码语法误报
    real_broken = []      # 真正的断链

    # 代码语法模式
    code_patterns = [
        r'^a, b T$', r'^item T$', r'^x T$', r'^numbers \[\]T$',
        r'^v$', r'\bt T\b', r'\[\]T$',
        r'^constraint', r'^comparable', r'^Cloneable', r'^Number', r'^Drawable'
    ]
    
    broken_by_file = data.get('broken_by_file', {})
    
    for file_path, links in broken_by_file.items():
        for link in links:
            target = link.get('link_target', '')
            text = link.get('link_text', '')
            
            # 检测代码语法误报
            is_false_positive = False
            
            # 检查是否泛型代码被误识别
            if any(x in text for x in ['T any', 'T comparable', 'T Drawable', 'T Cloneable', 'T Number', 'T constraints']):
                is_false_positive = True
            elif re.search(r'^[a-z, ]+ T$', target):  # 如 "a, b T"
                is_false_positive = True
            elif target in ['item T', 'x T', 'v', 'numbers []T']:
                is_false_positive = True
            elif text.startswith('\\'):  # LaTeX 语法
                is_false_positive = True
            elif '{}' in target:  # 模板语法
                is_false_positive = True
            
            if is_false_positive:
                false_positives.append({**link, 'file': file_path})
            else:
                real_broken.append({**link, 'file': file_path})

    print(f'总断链数: {data.get("broken_links", 0)}')
    print(f'代码语法误报: {len(false_positives)}')
    print(f'真正的断链: {len(real_broken)}')
    print()
    print('=== 前30个真正断链 ===')
    for link in real_broken[:30]:
        print(f"File: {link['file']}")
        print(f"  Text: [{link['link_text']}]")
        print(f"  Target: ({link['link_target']})")
        print()

    # 按文件分组统计
    print('=== 真正断链按文件分布 (前20) ===')
    from collections import Counter
    file_counts = Counter(link['file'] for link in real_broken)
    for file, count in file_counts.most_common(20):
        print(f'{count:3d}: {file}')

    # 保存分类结果
    with open('docs/real_broken_links.json', 'w', encoding='utf-8') as f:
        json.dump({
            'false_positives': false_positives,
            'real_broken': real_broken
        }, f, ensure_ascii=False, indent=2)
    print(f'\n详细结果已保存到 docs/real_broken_links.json')

if __name__ == '__main__':
    main()
