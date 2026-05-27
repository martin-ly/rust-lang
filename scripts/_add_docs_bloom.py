#!/usr/bin/env python3
"""Batch add Bloom annotations to docs/ markdown files."""
import re
from pathlib import Path

bloom_map = {
    'docs/00_meta/': 'L2 (理解)',
    'docs/01_core/': 'L1-L2 (记忆/理解)',
    'docs/01_learning/': 'L1-L2 (记忆/理解)',
    'docs/02_reference/quick_reference/': 'L2-L3 (理解/速查)',
    'docs/02_reference/': 'L2 (理解)',
    'docs/03_guides/': 'L2-L3 (理解/应用)',
    'docs/03_practice/': 'L3 (应用)',
    'docs/04_research/': 'L4-L5 (分析/评价)',
    'docs/04_thinking/': 'L4-L5 (分析/评价)',
    'docs/05_guides/workflow/': 'L3-L4 (应用/分析)',
    'docs/05_guides/': 'L3-L4 (应用/分析)',
    'docs/06_toolchain/': 'L3 (应用)',
    'docs/07_future/': 'L4-L5 (分析/评价)',
    'docs/07_project/': 'L4-L5 (分析/评价)',
}

skip_dirs = ['docs/archive/', 'docs/templates/', 'docs/content/']

count = 0
for f in sorted(Path('docs').rglob('*.md')):
    path_str = str(f).replace('\\', '/')
    if any(path_str.startswith(s) for s in skip_dirs):
        continue
    
    content = f.read_text(encoding='utf-8', errors='ignore')
    # Strip BOM if present
    content = content.lstrip('\ufeff')
    if 'Bloom' in content:
        continue
    
    # Determine Bloom level based on path
    bloom = None
    for prefix, level in sorted(bloom_map.items(), key=lambda x: -len(x[0])):
        if path_str.startswith(prefix):
            bloom = level
            break
    
    if not bloom:
        # Default for research_notes, rust-formal-engineering-system, etc.
        if 'research_notes' in path_str or 'rust-formal' in path_str or 'rust-ownership-decidability' in path_str or 'RUST_SAFETY_CRITICAL' in path_str:
            bloom = 'L5-L6 (分析/评价/创造)'
        elif path_str.count('/') == 1 and path_str.startswith('docs/'):
            # Root-level docs files
            bloom = 'L2-L3 (理解/应用)'
        else:
            continue
    
    # Insert Bloom annotation after first H1 heading
    lines = content.split('\n')
    insert_idx = 0
    for i, line in enumerate(lines):
        if line.startswith('# ') and insert_idx == 0:
            insert_idx = i + 1
            break
    
    if insert_idx > 0:
        bloom_line = f"\n> **Bloom 层级**: {bloom}"
        lines.insert(insert_idx, bloom_line)
        f.write_text('\n'.join(lines), encoding='utf-8')
        count += 1
        if count <= 5:
            print(f"Added Bloom to {path_str}: {bloom}")

print(f"\nTotal files updated: {count}")
