import re
from collections import Counter

with open('chinese_blocks.txt', 'r', encoding='utf-8') as f:
    content = f.read()

blocks = content.split('---BLOCK---\n')[1:]

all_lines = []
for b in blocks:
    for line in b.strip().split('\n'):
        stripped = line.strip()
        if stripped.startswith('///') or stripped.startswith('//!'):
            if stripped.startswith('/// '):
                text = stripped[4:]
            elif stripped.startswith('//! '):
                text = stripped[4:]
            elif stripped.startswith('///'):
                text = stripped[3:]
            elif stripped.startswith('//!'):
                text = stripped[3:]
            else:
                text = stripped
            text = text.strip()
            if text and re.search(r'[\u4e00-\u9fff]', text):
                all_lines.append(text)

counts = Counter(all_lines)
total = len(all_lines)

for n in [50, 100, 200, 300, 500]:
    covered = sum(c for _, c in counts.most_common(n))
    print(f"Top {n} lines cover {covered}/{total} = {covered/total*100:.1f}%")

# Also show cumulative for top 300 with counts
print("\nTop 300 lines with counts:")
for i, (line, count) in enumerate(counts.most_common(300), 1):
    print(f"{i:3d}. ({count:3d}) {line}")
