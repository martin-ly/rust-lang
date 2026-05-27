import os, re
from collections import defaultdict

def norm(p):
    return os.path.normpath(p).replace(chr(92), '/')

# Build all files set including all project directories
all_files = set()
for base in ['knowledge', 'concept', 'docs', 'exercises', 'book', 'crates', 'guides', 'reports', 'content']:
    if not os.path.isdir(base):
        continue
    for root, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        for f in files:
            all_files.add(norm(os.path.join(root, f)))
# Also add root-level files
for f in os.listdir('.'):
    if os.path.isfile(f):
        all_files.add(norm(f))

dead = defaultdict(list)
for root, dirs, files in os.walk('docs'):
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for f in files:
        if not f.endswith('.md'):
            continue
        rel_dir = norm(os.path.relpath(root, 'docs'))
        if 'archive' in rel_dir or f == 'LINK_CHECK_REPORT.md':
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

print(f'Active docs dead links: {len(dead)} unique, {sum(len(v) for v in dead.values())} occurrences')
for link, refs in sorted(dead.items(), key=lambda x: -len(x[1]))[:30]:
    print(f'{len(refs):3d}  {link}')
    for r in refs[:2]:
        print(f'      from {r}')
