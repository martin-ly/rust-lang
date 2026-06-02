import os, re
from collections import defaultdict

def norm(p):
    return os.path.normpath(p).replace('\\', '/')

# Build all files set (case-sensitive)
all_files = set()
all_files_lower = {}  # lowercase -> actual
for base in ['knowledge', 'concept', 'docs', 'exercises', 'book', 'crates']:
    if not os.path.isdir(base):
        continue
    for root, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        for f in files:
            path = norm(os.path.join(root, f))
            all_files.add(path)
            all_files_lower[path.lower()] = path

# Scan docs/ for dead links
dead = defaultdict(list)
case_mismatch = defaultdict(list)
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
                # Check if it's a case mismatch
                if target.lower() in all_files_lower:
                    case_mismatch[link].append((norm(os.path.relpath(path, 'docs')), all_files_lower[target.lower()]))
                else:
                    dead[link].append(norm(os.path.relpath(path, 'docs')))

print(f'Case mismatch links: {len(case_mismatch)} (occurrences: {sum(len(v) for v in case_mismatch.values())})')
for link, refs in sorted(case_mismatch.items(), key=lambda x: -len(x[1]))[:20]:
    print(f'  {len(refs):3d}  {link}  ->  {refs[0][1]}')

print()
print(f'Real dead links: {len(dead)} (occurrences: {sum(len(v) for v in dead.values())})')
for link, refs in sorted(dead.items(), key=lambda x: -len(x[1]))[:30]:
    print(f'  {len(refs):3d}  {link}')
