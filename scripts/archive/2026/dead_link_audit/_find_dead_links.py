import os, re
from collections import defaultdict

BASE = 'knowledge'
# Build rename mapping: old_name -> new_name per directory
rename_map = {}  # dir_path -> {old_name: new_name}
for root, dirs, files in os.walk(BASE):
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for f in files:
        if f.endswith('.md') and re.match(r'^\d{2}_', f):
            old_name = re.sub(r'^\d{2}_', '', f)
            rename_map.setdefault(root, {})[old_name] = f

# Now scan dead links and categorize
all_files = set()
for root, dirs, files in os.walk(BASE):
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for f in files:
        all_files.add(os.path.join(root, f).replace('\\', '/'))

dead = defaultdict(list)
for root, dirs, files in os.walk(BASE):
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for f in files:
        if not f.endswith('.md'):
            continue
        path = os.path.join(root, f).replace('\\', '/')
        with open(path, 'r', encoding='utf-8') as fh:
            content = fh.read()
        for m in re.finditer(r'\]\(([^)]+)\)', content):
            link = m.group(1)
            if not link.endswith('.md'):
                continue
            if link.startswith('http'):
                continue
            if link.startswith('/'):
                target = link[1:]
            else:
                target = os.path.normpath(os.path.join(root, link)).replace('\\', '/')
            if target not in all_files:
                dead[link].append(os.path.relpath(path, BASE).replace('\\', '/'))

# Print top dead links with their referring files
for link, refs in sorted(dead.items(), key=lambda x: -len(x[1]))[:50]:
    print(f'{len(refs):3d}  {link}')
    for r in refs[:3]:
        print(f'      from {r}')
