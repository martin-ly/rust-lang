import os, re

def norm(p):
    return os.path.normpath(p).replace('\\', '/')

all_files = set()
for base in ['knowledge', 'concept', 'docs', 'exercises', 'book', 'crates']:
    if not os.path.isdir(base):
        continue
    for root, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        for f in files:
            all_files.add(norm(os.path.join(root, f)))

# Replicate _analyze_docs_dead_links.py logic exactly
for root, dirs, files in os.walk('docs'):
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for f in files:
        if f != 'AI_RUST_ECOSYSTEM_GUIDE.md':
            continue
        path = norm(os.path.join(root, f))
        with open(path, 'r', encoding='utf-8') as fh:
            content = fh.read()
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
            exists = target in all_files
            if 'c01_ownership' in link:
                print(f'root={root}')
                print(f'link={link}')
                print(f'target={target}')
                print(f'exists={exists}')
