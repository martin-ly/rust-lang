import os, re

def norm(p):
    return os.path.normpath(p).replace(chr(92), '/')

# Patterns to fix in active docs files (excluding archive/ and LINK_CHECK_REPORT.md)
fixes = {
    # Case mismatch
    '../00_MASTER_INDEX.md': '../00_master_index.md',
    './00_MASTER_INDEX.md': './00_master_index.md',
    # Dead links to content/README.md
    '../../content/emerging/README.md': '',
    '../../content/ecosystem/README.md': '',
    # Guides path fix (check if exists)
    '../../guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md': '../../guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md',
    '../../../guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2025.md': '../../../guides/AI_ASSISTED_RUST_PROGRAMMING_GUIDE_2026.md',
}

removed_deprecated = 0
fixed_other = 0

for root, dirs, files in os.walk('docs'):
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for f in files:
        if not f.endswith('.md'):
            continue
        rel_dir = norm(os.path.relpath(root, 'docs'))
        if 'archive' in rel_dir or f == 'LINK_CHECK_REPORT.md':
            continue
        path = norm(os.path.join(root, f))
        with open(path, 'r', encoding='utf-8') as fh:
            content = fh.read()
        original = content

        # Remove all links pointing to archive/deprecated_20260318/
        content = re.sub(
            r'\[([^\]]*)\]\(([^)]*archive/deprecated_20260318/[^)]*)\)',
            r'\1',  # keep only the text, remove the link
            content
        )

        # Apply other fixes
        for old, new in fixes.items():
            if new:
                content = content.replace(old, new)
            else:
                content = re.sub(rf'\[([^\]]*)\]\({re.escape(old)}\)', r'\1', content)

        if content != original:
            if 'deprecated_20260318' not in content and 'deprecated_20260318' in original:
                removed_deprecated += 1
            else:
                fixed_other += 1
            with open(path, 'w', encoding='utf-8') as fh:
                fh.write(content)

print(f'Files with deprecated links removed: {removed_deprecated}')
print(f'Files with other fixes: {fixed_other}')
