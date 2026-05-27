import os, re
from collections import defaultdict

def norm(p):
    return os.path.normpath(p).replace('\\', '/')

# Build per-directory rename mapping
# dir_path (from project root) -> {old_basename: new_basename}
rename_map = defaultdict(dict)

for base in ['knowledge', 'concept', 'docs', 'exercises']:
    if not os.path.isdir(base):
        continue
    for root, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        for f in files:
            if not f.endswith('.md'):
                continue
            # If file has NN_ prefix, add mapping from old_name (without prefix)
            m = re.match(r'^(\d{2})_(.+)$', f)
            if m:
                old_name = m.group(2)
                dir_path = norm(root)
                rename_map[dir_path][old_name] = f
            # Also add case-insensitive mapping for ALL_CAPS files
            if f.upper() == f and f.endswith('.md') and not re.match(r'^\d{2}_', f):
                # e.g., ACADEMIC_RESEARCH_LANDSCAPE.md
                # Check if there's a numbered version in same dir
                pass  # handled below

# For case-sensitive issues: also map lowercase old names
# Some files may reference UPPERCASE names but actual file is lowercase with prefix
for dir_path, mappings in list(rename_map.items()):
    for old_name, new_name in list(mappings.items()):
        rename_map[dir_path][old_name.lower()] = new_name
        rename_map[dir_path][old_name.upper()] = new_name

# Special handling for UPPERCASE files in knowledge/04_expert/safety_critical/
# These files have NN_ prefix but links use old ALL_CAPS names
for root, dirs, files in os.walk('knowledge'):
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for f in files:
        if f.endswith('.md') and re.match(r'^\d{2}_', f):
            dir_path = norm(root)
            old_name = re.sub(r'^\d{2}_', '', f)
            rename_map[dir_path][old_name] = f
            rename_map[dir_path][old_name.lower()] = f
            rename_map[dir_path][old_name.upper()] = f
            # Also without .md for good measure
            rename_map[dir_path][old_name.replace('.md', '')] = f

# Also map per-directory for ALL files (not just renamed ones)
all_files = set()
file_lookup = {}  # dir_path -> set of basenames
for base in ['knowledge', 'concept', 'docs', 'exercises']:
    if not os.path.isdir(base):
        continue
    for root, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if not d.startswith('.')]
        dir_path = norm(root)
        file_lookup[dir_path] = set(files)
        for f in files:
            all_files.add(norm(os.path.join(root, f)))

# Fix links in knowledge/ files
fixed_count = 0
unknown_links = defaultdict(list)

for root, dirs, files in os.walk('knowledge'):
    dirs[:] = [d for d in dirs if not d.startswith('.')]
    for f in files:
        if not f.endswith('.md'):
            continue
        src_path = norm(os.path.join(root, f))
        with open(src_path, 'r', encoding='utf-8') as fh:
            content = fh.read()
        original = content
        
        def replacer(m):
            global fixed_count
            link = m.group(1)
            if not link.endswith('.md'):
                return m.group(0)
            if link.startswith('http') or link.startswith('#'):
                return m.group(0)
            
            # Compute target path
            if link.startswith('/'):
                target = link[1:]
            else:
                target = norm(os.path.join(root, link))
            
            if target in all_files:
                return m.group(0)  # valid link
            
            # Try to fix
            target_dir = os.path.dirname(target)
            target_basename = os.path.basename(target)
            
            # Check if target directory has a mapped version
            if target_dir in rename_map:
                mappings = rename_map[target_dir]
                if target_basename in mappings:
                    new_basename = mappings[target_basename]
                    new_link = link.replace(target_basename, new_basename)
                    fixed_count += 1
                    return f']({new_link})'
                # Try case-insensitive
                for old_name, new_name in mappings.items():
                    if old_name.lower() == target_basename.lower():
                        new_link = link.replace(target_basename, new_name)
                        fixed_count += 1
                        return f']({new_link})'
            
            # Try target dir itself with different casing or path normalization
            # Check if it's a concept/ link where the target might be in a different subdir
            unknown_links[link].append(norm(os.path.relpath(src_path, 'knowledge')))
            return m.group(0)
        
        new_content = re.sub(r'\]\(([^)]+)\)', replacer, content)
        if new_content != original:
            with open(src_path, 'w', encoding='utf-8') as fh:
                fh.write(new_content)

print(f'Fixed {fixed_count} links')
print(f'Remaining unknown links: {len(unknown_links)}')
for link, refs in sorted(unknown_links.items(), key=lambda x: -len(x[1]))[:40]:
    print(f'  {len(refs):3d}  {link}')
