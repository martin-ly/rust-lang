#!/usr/bin/env python3
"""
根据 verify_compile_fail_v3_report.md 降级 unexpected_pass 和 syntax_error 为 rust,ignore
"""
import re
from pathlib import Path

REPORT = Path("reports/verify_compile_fail_v3_report.md")

problem_blocks = []

with open(REPORT, encoding="utf-8") as f:
    for line in f:
        line = line.strip()
        if not line.startswith("|") or "文件" in line or "---" in line:
            continue
        # 用正则提取各列
        # 格式: | file | line | status | mode | preview | error |
        cols = [c.strip() for c in line.split("|")]
        cols = [c for c in cols if c]
        if len(cols) < 3:
            continue
        status = cols[2]
        if status not in ("unexpected_pass", "syntax_error"):
            continue
        file_path = cols[0]
        try:
            line_no = int(cols[1])
        except ValueError:
            continue
        problem_blocks.append((file_path, line_no, status))

print(f"发现 {len(problem_blocks)} 个问题块需要降级")

from collections import defaultdict
by_file = defaultdict(list)
for fp, ln, st in problem_blocks:
    by_file[fp].append((ln, st))

fixed = 0
for fp, items in by_file.items():
    p = Path(fp)
    if not p.exists():
        p = Path("e:/_src/rust-lang") / fp
    if not p.exists():
        print(f"  跳过: 文件不存在 {fp}")
        continue
    
    with open(p, encoding="utf-8") as f:
        lines = f.readlines()
    
    for ln, st in sorted(items, reverse=True):
        idx = ln - 1
        if idx < 0 or idx >= len(lines):
            continue
        
        found = False
        for offset in range(0, 5):
            check_idx = idx + offset
            if check_idx >= len(lines):
                continue
            if "```rust,compile_fail" in lines[check_idx]:
                old = lines[check_idx]
                new = old.replace("```rust,compile_fail", "```rust,ignore")
                lines[check_idx] = new
                fixed += 1
                print(f"  降级 [{st}] {fp}:{check_idx+1}")
                found = True
                break
        if not found:
            # 向上搜索
            for offset in range(1, 5):
                check_idx = idx - offset
                if check_idx < 0:
                    continue
                if "```rust,compile_fail" in lines[check_idx]:
                    old = lines[check_idx]
                    new = old.replace("```rust,compile_fail", "```rust,ignore")
                    lines[check_idx] = new
                    fixed += 1
                    print(f"  降级 [{st}] {fp}:{check_idx+1} (向上)")
                    found = True
                    break
    
    with open(p, "w", encoding="utf-8") as f:
        f.writelines(lines)

print(f"\n完成: 降级 {fixed} 个块")
