import os, re
from collections import defaultdict

BASE = 'knowledge'

def norm(p):
    return os.path.normpath(p).replace('\\', '/')

# Build old->new mapping for knowledge/
k_map = {}  # old_name -> new_name
for root, dirs, files in os.walk(BASE):
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for f in files:
        if f.endswith('.md') and re.match(r'^\d{2}_', f):
            old = re.sub(r'^\d{2}_', '', f)
            k_map[old] = f

# Build old->new mapping for concept/
c_map = {}
for root, dirs, files in os.walk('concept'):
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for f in files:
        if f.endswith('.md') and re.match(r'^\d{2}_', f):
            old = re.sub(r'^\d{2}_', '', f)
            c_map[old] = f

# Build old->new for docs/
d_map = {}
for root, dirs, files in os.walk('docs'):
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for f in files:
        if f.endswith('.md'):
            d_map[f.lower()] = f

all_files = set()
for base in ['knowledge', 'concept', 'docs', 'exercises']:
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

# Try to classify each dead link
for link, refs in sorted(dead.items(), key=lambda x: -len(x[1]))[:80]:
    fname = os.path.basename(link)
    fixed = None
    if fname in k_map:
        fixed = link.replace(fname, k_map[fname])
    elif fname in c_map:
        fixed = link.replace(fname, c_map[fname])
    elif fname.lower() in d_map:
        fixed = link.replace(fname, d_map[fname.lower()])
    status = 'FIXABLE' if fixed else 'UNKNOWN'
    print(f'{len(refs):3d}  [{status}]  {link}')
    if fixed:
        print(f'              -> {fixed}')
