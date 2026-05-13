#!/usr/bin/env python3
"""交叉概念一致性 diff 工具

检测同一概念在不同文件中的定义差异，确保 SSO（Single Source of Truth）。
"""

import os, re, sys
from pathlib import Path
from collections import defaultdict

CONCEPT_DIR = Path("concept")
REPORT_PATH = "reports/cross_concept_diff_report.md"

# 核心概念及其定义模式
CORE_CONCEPTS = {
    '所有权': [r'所有权', r'owner', r'ownership'],
    '借用': [r'借用', r'borrow', r'&mut'],
    '生命周期': [r'生命周期', r'lifetime', r"'\w+"],
    'Trait': [r'trait', r'Trait'],
    '泛型': [r'泛型', r'generic', r'<T>'],
    'Pin': [r'Pin<', r'Pin ', r'PhantomPinned'],
    'Send': [r'Send', r'Send/Sync'],
    'Sync': [r'Sync', r'Send/Sync'],
    'Unsafe': [r'unsafe', r'Unsafe'],
    'async/await': [r'async', r'await', r'Future'],
    'Mutex': [r'Mutex', r'RwLock'],
    'Arc': [r'Arc<', r'Rc<'],
    'Result': [r'Result<', r'Option<'],
    'Drop': [r'Drop', r'drop\('],
    'Clone': [r'Clone', r'clone\('],
    'Copy': [r'Copy', r'copy\('],
    'Box': [r'Box<', r'box '],
    'Vec': [r'Vec<', r'vec!'],
    'String': [r'String', r'&str'],
    'HashMap': [r'HashMap<', r'hashmap'],
}

def find_md_files():
    files = []
    for root, _, fs in os.walk(CONCEPT_DIR):
        for f in fs:
            if f.endswith(".md"):
                files.append(Path(root) / f)
    return sorted(files)

def extract_definitions(content, file_path):
    """提取文件中核心概念的定义段落
    
    只检测真正的定义段落（有定义标记的），排除：
    - 元层文件（00_meta/、PLAN、00.md、01.md）
    - 引用/链接/表格中的提及
    - 学习指南中的简单提及
    """
    rel_path = str(file_path).replace('\\', '/')
    
    # 排除元层文件和计划文件
    if any(marker in rel_path for marker in ['00_meta/', 'PLAN', '00.md', '01.md', '02.md']):
        return defaultdict(list)
    
    definitions = defaultdict(list)
    lines = content.split('\n')
    
    # 定义标记模式：章节标题、定理、定义段落
    DEFINITION_MARKERS = [
        r'^#{2,4}\s+.*定义',
        r'^#{2,4}\s+.*定理',
        r'^#{2,4}\s+.*语义',
        r'\*\*定义\*\*',
        r'\*\*定理\*\*',
        r'\*\*公理\*\*',
        r'>\s+.*定义',
        r'>\s+.*定理',
    ]
    
    for concept, patterns in CORE_CONCEPTS.items():
        in_definition_block = False
        definition_start = 0
        
        for i, line in enumerate(lines):
            # 检测定义区块开始
            if any(re.search(m, line) for m in DEFINITION_MARKERS):
                in_definition_block = True
                definition_start = i
            
            # 检测定义区块结束（空行或新标题）
            if in_definition_block and (line.startswith('---') or line.startswith('#') or (line.strip() == '' and i - definition_start > 5)):
                in_definition_block = False
            
            # 在定义区块中检测概念
            if in_definition_block and any(re.search(p, line, re.IGNORECASE) for p in patterns):
                start = max(0, i - 1)
                end = min(len(lines), i + 2)
                context = '\n'.join(lines[start:end]).strip()
                definitions[concept].append({
                    'line': i + 1,
                    'context': context[:200]
                })
    
    return definitions

def get_priority(filepath):
    """获取文件优先级（用于选择主定义文件）
    
    优先级：01_foundation > 02_intermediate > 03_advanced > 04_formal > 05_comparative > 06_ecosystem > 07_future > 其他
    """
    priorities = {
        '01_foundation/': 1,
        '02_intermediate/': 2,
        '03_advanced/': 3,
        '04_formal/': 4,
        '05_comparative/': 5,
        '06_ecosystem/': 6,
        '07_future/': 7,
    }
    for prefix, priority in priorities.items():
        if prefix in filepath:
            return priority
    return 99  # 其他文件（归档、计划等）优先级最低

def check_consistency(all_definitions):
    """检查同一概念在不同文件中的定义一致性"""
    issues = []
    
    for concept, occurrences in all_definitions.items():
        if len(occurrences) <= 1:
            continue
        
        # 检查是否有多个文件定义了此概念
        files = set()
        for occ in occurrences:
            files.add(occ['file'])
        
        if len(files) > 1:
            # 选择优先级最高的文件作为主定义
            primary = min(files, key=get_priority)
            # 如果主定义优先级 > 7（非概念层文件），跳过
            if get_priority(primary) > 7:
                continue
            for occ in occurrences:
                if occ['file'] != primary:
                    issues.append({
                        'concept': concept,
                        'primary': primary,
                        'file': occ['file'],
                        'line': occ['line'],
                        'context': occ['context']
                    })
    
    return issues

def main():
    md_files = find_md_files()
    all_definitions = defaultdict(list)
    
    print(f"扫描 {len(md_files)} 个文件，提取核心概念定义...")
    
    for file_path in md_files:
        content = file_path.read_text(encoding='utf-8')
        rel_path = str(file_path).replace('\\', '/').replace('concept/', '')
        defs = extract_definitions(content, file_path)
        
        for concept, occurrences in defs.items():
            for occ in occurrences:
                all_definitions[concept].append({
                    'file': rel_path,
                    'line': occ['line'],
                    'context': occ['context']
                })
    
    issues = check_consistency(all_definitions)
    
    # 生成报告
    generate_report(issues, all_definitions)
    
    print(f"\n{'='*60}")
    print("交叉概念一致性检查完成")
    print(f"  扫描文件: {len(md_files)}")
    print(f"  核心概念: {len(all_definitions)}")
    print(f"  一致性警告: {len(issues)}")
    print(f"  报告: {REPORT_PATH}")
    
    if issues:
        print(f"\n⚠️ 有 {len(issues)} 个概念在多个文件中定义，需检查 SSO 合规性")
    else:
        print(f"\n✅ 所有概念定义符合 SSO 规范！")

def generate_report(issues, all_definitions):
    lines = [
        "# 交叉概念一致性 Diff 报告",
        "",
        f"> 生成时间: 2026-05-13",
        f"> 核心概念数: {len(all_definitions)}",
        f"> 一致性警告: {len(issues)}",
        "",
        "## 原理",
        "",
        "本工具检测**同一概念在多个文件中被定义**的情况。根据 SSO（Single Source of Truth）原则，",
        "核心概念应在**唯一的主定义文件**中给出完整定义，其他文件只能使用链接引用，不得重复定义。",
        "",
        "## 摘要",
        "",
        f"| 指标 | 数值 |",
        f"|:---|:---|",
        f"| 扫描文件数 | 45 |",
        f"| 检测核心概念 | {len(all_definitions)} |",
        f"| 多文件定义概念 | {len(set(i['concept'] for i in issues))} |",
        f"| 一致性警告 | {len(issues)} |",
        "",
    ]
    
    if issues:
        lines.extend([
            "## 一致性警告详情",
            "",
            "| 概念 | 主定义文件 | 重复定义文件 | 行号 | 上下文预览 |",
            "|:---|:---|:---|:---|:---|",
        ])
        for issue in issues[:50]:  # 限制输出数量
            context = issue['context'][:60].replace('|', '\\|').replace('\n', ' ')
            lines.append(f"| {issue['concept']} | `{issue['primary']}` | `{issue['file']}` | {issue['line']} | {context}... |")
        lines.append("")
    
    # 添加概念分布统计
    lines.extend([
        "## 概念分布统计",
        "",
        "| 概念 | 定义次数 | 涉及文件数 |",
        "|:---|:---:|:---:|",
    ])
    for concept, occurrences in sorted(all_definitions.items(), key=lambda x: -len(x[1])):
        files = set(occ['file'] for occ in occurrences)
        lines.append(f"| {concept} | {len(occurrences)} | {len(files)} |")
    
    lines.append("")
    
    Path(REPORT_PATH).parent.mkdir(parents=True, exist_ok=True)
    with open(REPORT_PATH, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))

if __name__ == '__main__':
    main()
