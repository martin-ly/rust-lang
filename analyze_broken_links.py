#!/usr/bin/env python3
"""分析断链报告"""

import json
from collections import Counter

def main():
    with open('docs/link_check_report.json', 'r', encoding='utf-8') as f:
        data = json.load(f)
    
    broken_by_file = data.get('broken_by_file', {})
    
    print(f"总断链数: {data.get('total_broken', 0)}")
    print(f"涉及文件数: {len(broken_by_file)}")
    print()
    
    # 按断链数量排序
    sorted_files = sorted(broken_by_file.items(), key=lambda x: len(x[1]), reverse=True)
    
    print("断链最多的文件 (Top 20):")
    for filepath, links in sorted_files[:20]:
        print(f"  {filepath}: {len(links)} 个断链")
    
    print()
    print("断链类型分析:")
    
    # 分析断链类型
    target_patterns = Counter()
    for filepath, links in broken_by_file.items():
        for link in links:
            target = link.get('target', '')
            # 分类断链
            if target.endswith('/'):
                target_patterns['目录链接'] += 1
            elif 'research_notes' in target and not target.startswith('docs/'):
                target_patterns['research_notes 路径错误'] += 1
            elif target.startswith('../'):
                target_patterns['相对路径错误'] += 1
            elif '.md' not in target:
                target_patterns['非 md 链接'] += 1
            else:
                target_patterns['其他'] += 1
    
    for pattern, count in target_patterns.most_common():
        print(f"  {pattern}: {count}")

if __name__ == '__main__':
    main()
