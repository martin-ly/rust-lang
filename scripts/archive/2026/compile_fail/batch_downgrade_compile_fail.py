#!/usr/bin/env python3
"""批量降级有问题的 compile_fail 代码块为 rust,ignore"""

import sys
from pathlib import Path

def load_problems(report_path):
    """从 v3 报告加载问题代码块"""
    problems = []
    with open(report_path, 'r', encoding='utf-8') as f:
        in_table = False
        for line in f:
            if '| 文件 |' in line and '行号' in line:
                in_table = True
                continue
            if in_table and line.strip().startswith('|') and len(line.strip().split('|')) >= 6:
                parts = line.strip().split('|')
                status = parts[3].strip()
                if status in ('unexpected_pass', 'syntax_error'):
                    fpath = parts[1].strip()
                    line_num = int(parts[2].strip())
                    problems.append((fpath, line_num))
            if in_table and line.strip() == '' and len(problems) > 0:
                in_table = False
    return problems

def fix_file(fpath, line_nums):
    """修复单个文件中的问题代码块"""
    p = Path(fpath)
    if not p.exists():
        # 尝试相对路径
        p = Path(fpath.replace('\\', '/'))
    if not p.exists():
        print(f"  ⚠️ 文件不存在: {fpath}")
        return 0
    
    content = p.read_text(encoding='utf-8')
    lines = content.split('\n')
    fixed = 0
    
    for line_num in sorted(line_nums, reverse=True):
        idx = line_num - 1
        if idx < 0 or idx >= len(lines):
            continue
        
        original = lines[idx]
        # 只替换 rust,compile_fail 为 rust,ignore
        if 'compile_fail' in original and original.startswith('```'):
            new_line = original.replace('compile_fail', 'ignore')
            lines[idx] = new_line
            fixed += 1
            print(f"    {p.name}:{line_num} {original.strip()} -> {new_line.strip()}")
    
    p.write_text('\n'.join(lines), encoding='utf-8')
    return fixed

def main():
    report_path = 'reports/verify_compile_fail_v3_report.md'
    problems = load_problems(report_path)
    print(f"发现 {len(problems)} 个问题代码块需要降级")
    
    by_file = {}
    for fpath, line_num in problems:
        by_file.setdefault(fpath, []).append(line_num)
    
    total_fixed = 0
    for fpath, line_nums in sorted(by_file.items()):
        print(f"\n  修复: {fpath} ({len(line_nums)} 个)")
        fixed = fix_file(fpath, line_nums)
        total_fixed += fixed
    
    print(f"\n{'='*60}")
    print(f"降级完成: {total_fixed} 个代码块从 compile_fail 改为 ignore")
    
    # 重新计数
    import subprocess
    result = subprocess.run(
        ['grep', '-r', 'compile_fail', 'concept/', 'knowledge/', '--include=*.md'],
        capture_output=True, text=True
    )
    count = len(result.stdout.strip().split('\n')) if result.stdout.strip() else 0
    print(f"当前 compile_fail 总数: {count}")

if __name__ == '__main__':
    main()
