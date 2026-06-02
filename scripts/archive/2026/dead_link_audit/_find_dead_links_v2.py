import os, re
from collections import defaultdict

def norm(p):
    return os.path.normpath(p).replace('\\', '/')

BASE = 'knowledge'

all_files = set()
for base in ['knowledge', 'concept', 'docs', 'exercises']:
    if not os.path.isdir(base):
        continue
    for root, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        for f in files:
            all_files.add(norm(os.path.join(root, f)))

dead = defaultdict(list)
for root, dirs, files in os.walk(BASE):
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for f in files:
        if not f.endswith('.md'):
            continue
        path = norm(os.path.join(root, f))
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
                target = norm(os.path.join(root, link))
            if target not in all_files:
                dead[link].append(norm(os.path.relpath(path, BASE)))

print(f'Total dead links: {len(dead)}')
c = __import__('collections').Counter
for link, cnt in c.Counter(d[1] for d in dead.items()).most_common(50):
    pass

for link, refs in sorted(dead.items(), key=lambda x: -len(x[1]))[:50]:
    print(f'{len(refs):3d}  {link}')
    for r in refs[:2]:
        print(f'      from {r}')
