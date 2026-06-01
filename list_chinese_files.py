import os
import re

directories = [
    'crates/c10_networks/src',
    'crates/c11_macro_system/src',
    'crates/c11_macro_system_proc/src',
    'crates/c12_wasm/src',
    'crates/c13_embedded/src',
    'exercises/src',
]

files = []
for d in directories:
    if not os.path.exists(d):
        continue
    for root, _, fnames in os.walk(d):
        for fname in fnames:
            if fname.endswith('.rs'):
                filepath = os.path.join(root, fname)
                with open(filepath, 'r', encoding='utf-8') as f:
                    content = f.read()
                if re.search(r'(^/// .*[\u4e00-\u9fff]|^//! .*[\u4e00-\u9fff])', content, re.MULTILINE):
                    size = os.path.getsize(filepath)
                    # Count Chinese blocks
                    lines = content.split('\n')
                    block_count = 0
                    i = 0
                    while i < len(lines):
                        if lines[i].startswith('///') or lines[i].startswith('//!'):
                            block_type = '///' if lines[i].startswith('///') else '//!'
                            block = []
                            while i < len(lines) and lines[i].startswith(block_type):
                                block.append(lines[i])
                                i += 1
                            if re.search(r'[\u4e00-\u9fff]', ''.join(block)):
                                block_count += 1
                        else:
                            i += 1
                    files.append((filepath, size, block_count))

files.sort(key=lambda x: x[1])
print(f"Total files with Chinese comments: {len(files)}")
for f, s, bc in files:
    print(f"{s:6d} {bc:3d} {f}")
