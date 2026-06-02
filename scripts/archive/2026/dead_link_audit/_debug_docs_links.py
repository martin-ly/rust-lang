import os

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

target = norm(os.path.join('docs/05_guides/', '../../crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md'))
print('target:', target)
print('in all_files:', target in all_files)
print('sample paths:', [p for p in all_files if 'c01_ownership' in p][:3])
