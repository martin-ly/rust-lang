#!/usr/bin/env python3
import re
from pathlib import Path

SOURCE_PATTERNS = [
    r"\[来源[：:]\s*[^\]]+\]",
    r"\[学术来源[：:][^\]]*\]",
    r"\[工业来源[：:][^\]]*\]",
    r"> \*\*来源[：:][^\*]*\*\*",
    r"> \*\*权威来源[：:][^\*]*\*\*",
    r">\s*\*\*\[[^\]]+\]\*\*",
    r"\[RFC\s+\d+[^\]]*\]",
    r"\[POPL\s+\d{4}[^\]]*\]",
    r"\[PLDI\s+\d{4}[^\]]*\]",
    r"\[ECOOP\s+\d{4}[^\]]*\]",
    r"\[SOSP\s+\d{4}[^\]]*\]",
    r"\[OOPSLA\s+\d{4}[^\]]*\]",
    r"\[JFP\s+\d{4}[^\]]*\]",
    r"\[ICFP\s+\d{4}[^\]]*\]",
    r"\[FM\s+\d{4}[^\]]*\]",
    r"\[VSTTE\s+\d{4}[^\]]*\]",
    r"\[RustBelt[^\]]*\]",
    r"\[Iris[^\]]*\]",
    r"\[Kani[^\]]*\]",
    r"\[Verus[^\]]*\]",
    r"\[Creusot[^\]]*\]",
    r"\[Prusti[^\]]*\]",
    r"\[Aeneas[^\]]*\]",
    r"\[RefinedRust[^\]]*\]",
    r"\[Miri[^\]]*\]",
    r"Jung et al\.\s*,\s*\*[^\*]+\*\s*,\s*(?:POPL|PLDI|ECOOP|OOPSLA|JFP|ICFP)\s+\d{4}",
    r"O'Hearn\s+\d{4}",
    r"Girard\s+\d{4}",
    r"Tofte-Talpin\s+\d{4}",
    r"\[Wikipedia[：:]?\s*[^\]]+\]",
    r"\[Rust Reference[^\]]*\]",
    r"\[Rust Book[^\]]*\]",
    r"\[Rustonomicon[^\]]*\]",
    r"\[The Rust Programming Language[^\]]*\]",
    r"\[Rust\s+\d+\.\d+\s+Release Notes\]",
    r"\[Rust\s+\d{4}\s+Edition\s+Guide\]",
    r"\[RFC\s+\d{4}[^\]]*\]",
    r"来源[：:]\s*\[[^\]]+\]\s*·\s*[^\n]*✅",
    r"来源[：:]\s*\[[^\]]+\]\s*·\s*[^\n]*🔍",
]

files = list(Path('docs').rglob('*.md'))
files = [f for f in files if 'archive' not in str(f).replace('\\','/').lower()]
low_files = []
for fp in files:
    content = fp.read_text(encoding='utf-8')
    annotations = 0
    for p in SOURCE_PATTERNS:
        annotations += len(re.findall(p, content, re.IGNORECASE))
    paragraphs = [p for p in re.split(r'\n\s*\n', content) if len(p.strip()) > 20]
    para_count = len(paragraphs)
    claims = len(re.findall(r'^(?:>|#+\s*[^:]+[:：]|\*\*定理|\*\*定义|\*\*公理)', content, re.MULTILINE))
    denominator = max(para_count + claims * 2, 1)
    rate = annotations / denominator
    if rate < 0.15 and para_count > 5:
        low_files.append((str(fp).replace('\\','/'), annotations, para_count, claims, rate))

low_files.sort(key=lambda x: x[4])
print(f'Total docs files scanned: {len(files)}')
print(f'Files with source rate < 15% and >5 paragraphs: {len(low_files)}')
print()
for f, a, p, c, r in low_files:
    print(f'{f}: {a} annotations, {p} paragraphs, {c} claims, rate={r:.2%}')

# Also compute average for docs track
total_rate = 0
count = 0
for fp in files:
    content = fp.read_text(encoding='utf-8')
    annotations = 0
    for p in SOURCE_PATTERNS:
        annotations += len(re.findall(p, content, re.IGNORECASE))
    paragraphs = [p for p in re.split(r'\n\s*\n', content) if len(p.strip()) > 20]
    para_count = len(paragraphs)
    claims = len(re.findall(r'^(?:>|#+\s*[^:]+[:：]|\*\*定理|\*\*定义|\*\*公理)', content, re.MULTILINE))
    denominator = max(para_count + claims * 2, 1)
    rate = annotations / denominator
    total_rate += rate
    count += 1
print(f'\nCurrent average citation rate for docs/: {total_rate/count:.2%}')
