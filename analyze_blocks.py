import re
from collections import Counter

with open('chinese_blocks.txt', 'r', encoding='utf-8') as f:
    content = f.read()

blocks = content.split('---BLOCK---\n')[1:]

# Count lines
line_counts = Counter()
for b in blocks:
    line_counts[len(b.strip().split('\n'))] += 1

print("Block size distribution:")
for size, count in sorted(line_counts.items())[:20]:
    print(f"  {size} lines: {count}")

# Extract individual lines
all_lines = []
for b in blocks:
    for line in b.strip().split('\n'):
        stripped = line.strip()
        if stripped.startswith('///') or stripped.startswith('//!'):
            all_lines.append(stripped)

print(f"\nTotal individual doc comment lines: {len(all_lines)}")
print(f"Unique individual doc comment lines: {len(set(all_lines))}")

print("\nTop 50 most common lines:")
for line, count in Counter(all_lines).most_common(50):
    print(f"  {count:4d}: {line}")
