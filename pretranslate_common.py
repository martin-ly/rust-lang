import re
import json
from collections import Counter

with open('chinese_blocks.txt', 'r', encoding='utf-8') as f:
    content = f.read()

blocks = content.split('---BLOCK---\n')[1:]
block_counts = Counter(b.strip() for b in blocks if b.strip())

print(f"Total unique blocks: {len(block_counts)}")
print(f"Total occurrences: {sum(block_counts.values())}")

# Show top 100 blocks
top_blocks = block_counts.most_common(100)
for i, (block, count) in enumerate(top_blocks, 1):
    lines = block.split('\n')
    preview = ' | '.join(l.strip() for l in lines[:3])
    if len(lines) > 3:
        preview += ' ...'
    print(f"{i:3d}. ({count:3d}) {preview}")
