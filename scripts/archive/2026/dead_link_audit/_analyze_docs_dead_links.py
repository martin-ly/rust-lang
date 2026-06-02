import os, re
from collections import defaultdict

def norm(p):
    return os.path.normpath(p).replace('\\', '/')

# Build all files set
all_files = set()
for base in ['knowledge', 'concept', 'docs', 'exercises', 'book', 'crates']:
    if not os.path.isdir(base):
        continue
    for root, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        for f in files:
            all_files.add(norm(os.path.join(root, f)))

# Scan docs/ for dead links
dead = defaultdict(list)
for root, dirs, files in os.walk('docs'):
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for f in files:
        if not f.endswith('.md'):
            continue
        path = norm(os.path.join(root, f))
        try:
            with open(path, 'r', encoding='utf-8') as fh:
                content = fh.read()
        except Exception:
            continue
        for m in re.finditer(r'\]\(([^)]+)\)', content):
            link = m.group(1)
            if not link.endswith('.md'):
                continue
            if link.startswith('http') or link.startswith('#'):
                continue
            if link.startswith('/'):
                target = link[1:]
            else:
                target = norm(os.path.join(root, link))
            if target not in all_files:
                dead[link].append(norm(os.path.relpath(path, 'docs')))

print(f'Total unique dead links: {len(dead)}')
print(f'Total dead link occurrences: {sum(len(v) for v in dead.values())}')
print()
for link, refs in sorted(dead.items(), key=lambda x: -len(x[1]))[:40]:
    print(f'{len(refs):3d}  {link}')
