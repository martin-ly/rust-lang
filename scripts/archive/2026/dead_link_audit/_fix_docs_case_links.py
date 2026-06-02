import os, re

def norm(p):
    return os.path.normpath(p).replace('\\', '/')

# Fix case mismatch: 00_MASTER_INDEX.md -> 00_master_index.md in docs/ files
fixed = 0
for root, dirs, files in os.walk('docs'):
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for f in files:
        if not f.endswith('.md'):
            continue
        path = norm(os.path.join(root, f))
        with open(path, 'r', encoding='utf-8') as fh:
            content = fh.read()
        original = content
        # Replace 00_MASTER_INDEX.md with 00_master_index.md when used as link target
        content = re.sub(r'\(00_MASTER_INDEX\.md\)', '(00_master_index.md)', content)
        content = re.sub(r'`docs/00_MASTER_INDEX\.md`', '`docs/00_master_index.md`', content)
        if content != original:
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(content)
            fixed += 1

print(f'Fixed {fixed} files')
