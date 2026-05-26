import os, re

def cleanup_file(path):
    with open(path, 'r', encoding='utf-8') as f:
        lines = f.read().split('\n')
    
    # Find how many trailing lines are source garbage or blank
    remove_count = 0
    for line in reversed(lines):
        stripped = line.strip()
        if re.match(r'> \[来源:', stripped):
            remove_count += 1
        elif stripped == '':
            remove_count += 1
        else:
            break
    
    if remove_count == 0:
        return 0
    
    # But be careful: keep blank lines that separate content from trailing sources
    # Only remove if there are actual source lines in the trailing block
    trailing_block = lines[-remove_count:] if remove_count > 0 else []
    has_source = any(re.match(r'> \[来源:', line.strip()) for line in trailing_block)
    
    if not has_source:
        return 0
    
    # New content: remove the trailing block entirely
    new_lines = lines[:-remove_count]
    # Strip trailing blank lines from the remaining content (keep one if any content exists)
    while len(new_lines) > 0 and new_lines[-1].strip() == '':
        new_lines.pop()
    
    with open(path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(new_lines))
        if new_lines:  # add final newline
            f.write('\n')
    
    return remove_count

# Process concept/ directory
processed = 0
total_removed = 0
for root, _, fs in os.walk('concept'):
    for fname in fs:
        if not fname.endswith('.md'):
            continue
        path = os.path.join(root, fname)
        n = cleanup_file(path)
        if n > 0:
            processed += 1
            total_removed += n

print(f"Cleaned {processed} files, removed {total_removed} trailing lines")
