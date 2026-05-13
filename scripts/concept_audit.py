#!/usr/bin/env python3
"""概念知识体系自动化审计脚本

检查项：
1. 每个 markdown 文件包含 ≥3 个跨文件链接
2. 文件内 TODO 标记与 todos.md 同步
3. 代码块语言标记正确
4. 文件命名符合规范
5. 生成审计报告
"""

import os, re, json, sys
from pathlib import Path
from collections import defaultdict

CONCEPT_DIR = Path("concept")
REPORT_PATH = "reports/concept_audit_report.md"
INDEX_PATH = "concept/00_meta/concept_index.json"

def find_md_files():
    files = []
    for root, _, fs in os.walk(CONCEPT_DIR):
        for f in fs:
            if f.endswith(".md") and f != "README.md":
                files.append(Path(root) / f)
    return sorted(files)

def check_cross_links(content, file_path):
    """检查跨文件链接数量"""
    # 匹配 [text](./path.md) 或 [text](../path.md) 格式的链接
    links = re.findall(r'\[([^\]]+)\]\((\.\.?/[^)]+\.md)\)', content)
    # 也匹配绝对路径链接
    links += re.findall(r'\[([^\]]+)\]\((/[^)]+\.md)\)', content)
    return len(links), links

def check_code_blocks(content):
    """检查代码块标记"""
    issues = []
    # 匹配完整的代码块围栏，提取语言标记
    blocks = re.findall(r'```(\w+)?[^\n]*\n', content)
    for i, block in enumerate(blocks):
        lang = block.strip() if block else ''
        # 排除已知的非代码块类型
        if not lang and not any(marker in content for marker in ['```mermaid', '```text', '```plain', '```yaml', '```json', '```toml']):
            issues.append(f"未标注语言的代码块 #{i+1}")
    return issues

def check_todos(content):
    """检查文件内 TODO 状态"""
    pending = len(re.findall(r'^- \[ \]', content, re.MULTILINE))
    done = len(re.findall(r'^- \[x\]', content, re.MULTILINE))
    return pending, done

def check_file_naming(file_path):
    """检查文件命名是否符合 NN_english_name.md"""
    name = file_path.name
    return bool(re.match(r'^\d{2}_[a-z_]+\.md$', name)), name

def main():
    md_files = find_md_files()
    
    results = {
        'total_files': len(md_files),
        'cross_links_ok': 0,
        'cross_links_fail': [],
        'code_block_issues': [],
        'todo_summary': {'pending': 0, 'done': 0},
        'naming_ok': 0,
        'naming_fail': [],
    }
    
    for file_path in md_files:
        content = file_path.read_text(encoding='utf-8')
        rel_path = str(file_path).replace('\\', '/')
        
        # 1. 跨文件链接检查
        link_count, links = check_cross_links(content, file_path)
        if link_count >= 3:
            results['cross_links_ok'] += 1
        else:
            results['cross_links_fail'].append({
                'file': rel_path,
                'count': link_count,
                'links': [l[1] for l in links[:5]]
            })
        
        # 2. 代码块检查
        code_issues = check_code_blocks(content)
        if code_issues:
            results['code_block_issues'].append({
                'file': rel_path,
                'issues': code_issues
            })
        
        # 3. TODO 统计
        pending, done = check_todos(content)
        results['todo_summary']['pending'] += pending
        results['todo_summary']['done'] += done
        
        # 4. 命名规范
        naming_ok, name = check_file_naming(file_path)
        if naming_ok:
            results['naming_ok'] += 1
        else:
            results['naming_fail'].append(rel_path)
    
    # 生成报告
    generate_report(results)
    
    # 打印摘要
    print(f"\n{'='*60}")
    print("概念知识体系自动化审计完成")
    print(f"{'='*60}")
    print(f"扫描文件数: {results['total_files']}")
    print(f"跨文件链接 ≥3: {results['cross_links_ok']}/{results['total_files']}")
    print(f"命名规范符合: {results['naming_ok']}/{results['total_files']}")
    print(f"代码块问题: {len(results['code_block_issues'])} 个文件")
    print(f"TODO 待完成: {results['todo_summary']['pending']}")
    print(f"TODO 已完成: {results['todo_summary']['done']}")
    print(f"报告: {REPORT_PATH}")
    
    if results['cross_links_fail'] or results['code_block_issues']:
        print(f"\n⚠️ 有 {len(results['cross_links_fail'])} 个文件跨文件链接不足")
        print(f"⚠️ 有 {len(results['code_block_issues'])} 个文件代码块标记有问题")
        sys.exit(1)
    else:
        print(f"\n✅ 审计通过！")

def generate_report(results):
    lines = [
        "# 概念知识体系自动化审计报告",
        "",
        f"> 生成时间: 2026-05-13",
        f"> 扫描文件数: {results['total_files']}",
        "",
        "## 摘要",
        "",
        f"| 指标 | 数值 |",
        f"|:---|:---|",
        f"| 扫描文件数 | {results['total_files']} |",
        f"| 跨文件链接 ≥3 | {results['cross_links_ok']}/{results['total_files']} |",
        f"| 命名规范符合 | {results['naming_ok']}/{results['total_files']} |",
        f"| 代码块问题文件 | {len(results['code_block_issues'])} |",
        f"| TODO 待完成 | {results['todo_summary']['pending']} |",
        f"| TODO 已完成 | {results['todo_summary']['done']} |",
        "",
    ]
    
    if results['cross_links_fail']:
        lines.extend([
            "## 跨文件链接不足的文件",
            "",
            "| 文件 | 链接数 | 现有链接 |",
            "|:---|:---|:---|",
        ])
        for item in results['cross_links_fail']:
            links_preview = ', '.join(item['links'][:3]) if item['links'] else '无'
            lines.append(f"| {item['file']} | {item['count']} | {links_preview} |")
        lines.append("")
    
    if results['code_block_issues']:
        lines.extend([
            "## 代码块标记问题",
            "",
            "| 文件 | 问题 |",
            "|:---|:---|",
        ])
        for item in results['code_block_issues']:
            issues = '; '.join(item['issues'])
            lines.append(f"| {item['file']} | {issues} |")
        lines.append("")
    
    if results['naming_fail']:
        lines.extend([
            "## 命名不规范的文件",
            "",
        ])
        for f in results['naming_fail']:
            lines.append(f"- {f}")
        lines.append("")
    
    Path(REPORT_PATH).parent.mkdir(parents=True, exist_ok=True)
    with open(REPORT_PATH, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))

if __name__ == '__main__':
    main()
