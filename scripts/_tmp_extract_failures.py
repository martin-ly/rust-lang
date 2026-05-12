import re
from pathlib import Path

report = Path('reports/code_block_compile_report.md').read_text(encoding='utf-8')

in_failures = False
failures = []
for line in report.split('\n'):
    if '## 编译失败的代码块' in line:
        in_failures = True
        continue
    if '## 编译通过的代码块' in line:
        break
    if in_failures and line.startswith('| ') and '文件' not in line and '---' not in line:
        parts = [p.strip() for p in line.split('|')]
        if len(parts) >= 5:
            file_path = parts[1].replace('\\', '/')
            line_num = int(parts[2])
            failures.append((file_path, line_num))

for fp, ln in failures:
    md = Path(fp)
    if not md.exists():
        continue
    lines = md.read_text(encoding='utf-8').split('\n')
    idx = ln - 1
    if idx < 0 or idx >= len(lines) or not lines[idx].startswith('```'):
        continue
    fence = lines[idx].strip()
    code = []
    j = idx + 1
    while j < len(lines) and not lines[j].startswith('```'):
        code.append(lines[j])
        j += 1
    print(f'=== {fp}:{ln} {fence} ===')
    for c in code[:6]:
        print(c)
    if len(code) > 6:
        print(f'... ({len(code)} lines total)')
    print()
