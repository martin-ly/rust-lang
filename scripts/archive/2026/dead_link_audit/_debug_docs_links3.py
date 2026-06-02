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

# Check one specific file
src = 'docs/05_guides/AI_RUST_ECOSYSTEM_GUIDE.md'
with open(src, 'r', encoding='utf-8') as fh:
    content = fh.read()

for m in re.finditer(r'\]\(([^)]+)\)', content):
    link = m.group(1)
    if 'c01_ownership' in link:
        target = norm(os.path.join(os.path.dirname(src), link))
        exists = target in all_files
        print(f'link={link}')
        print(f'target={target}')
        print(f'exists={exists}')
        if not exists:
            # Try to find similar paths
            similar = [p for p in all_files if '00_MASTER_INDEX' in p and 'c01' in p]
            print(f'similar={similar[:3]}')
        break
