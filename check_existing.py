import os
import re

def has_english_after_chinese(filepath):
    with open(filepath, 'r', encoding='utf-8') as f:
        lines = f.readlines()
    
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith('///') or line.startswith('//!'):
            block = []
            block_type = '///' if line.startswith('///') else '//!'
            while i < len(lines) and lines[i].startswith(block_type):
                block.append(lines[i])
                i += 1
            text = ''.join(block)
            if re.search(r'[\u4e00-\u9fff]', text):
                # Check if next block is same type and English
                if i < len(lines) and lines[i].startswith(block_type):
                    next_block = []
                    while i < len(lines) and lines[i].startswith(block_type):
                        next_block.append(lines[i])
                        i += 1
                    next_text = ''.join(next_block)
                    if not re.search(r'[\u4e00-\u9fff]', next_text):
                        # Already has English translation
                        continue
                    else:
                        # Next block is also Chinese, needs translation
                        return True
                else:
                    # No next block or next is different type, needs translation
                    return True
        else:
            i += 1
    return False

directories = [
    'crates/c10_networks/src',
    'crates/c11_macro_system/src',
    'crates/c11_macro_system_proc/src',
    'crates/c12_wasm/src',
    'crates/c13_embedded/src',
    'exercises/src'
]

needs_translation = []
already_translated = []
for d in directories:
    if not os.path.exists(d):
        continue
    for root, _, files in os.walk(d):
        for fname in files:
            if fname.endswith('.rs'):
                filepath = os.path.join(root, fname)
                if has_english_after_chinese(filepath):
                    needs_translation.append(filepath)
                else:
                    # Check if file has any Chinese comments at all
                    with open(filepath, 'r', encoding='utf-8') as f:
                        content = f.read()
                    if re.search(r'(^/// .*[\u4e00-\u9fff]|^//! .*[\u4e00-\u9fff])', content, re.MULTILINE):
                        already_translated.append(filepath)

print(f"Files needing translation: {len(needs_translation)}")
print(f"Files already translated: {len(already_translated)}")
for f in needs_translation[:20]:
    print(f"  NEEDS: {f}")
for f in already_translated[:20]:
    print(f"  DONE:  {f}")
