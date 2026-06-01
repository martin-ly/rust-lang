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
            # Remove the doc comment prefix
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
print(f"Unique non-empty Chinese lines: {len(counts)}")
print("\nTop 200 most common non-empty Chinese lines:")
for i, (line, count) in enumerate(counts.most_common(200), 1):
    print(f"{i:3d}. ({count:3d}) {line}")
