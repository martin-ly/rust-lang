import os

def norm(p):
    return os.path.normpath(p).replace('\\', '/')

# Simulate os.walk behavior on Windows
root = 'docs\\05_guides'
link = '../../crates/c01_ownership_borrow_scope/docs/00_MASTER_INDEX.md'
target = norm(os.path.join(root, link))
print(f'root={root}, link={link}')
print(f'target={target}')

root2 = 'docs/05_guides'
target2 = norm(os.path.join(root2, link))
print(f'root={root2}, target={target2}')
