import re
from pathlib import Path

def get_file_title(filepath):
    """Extract title from markdown file (first # heading)."""
    content = filepath.read_text(encoding="utf-8")
    match = re.search(r'^#\s+(.+)$', content, re.MULTILINE)
    if match:
        return match.group(1).strip()
    return filepath.stem

def fix_readme(d):
    readme = d / "README.md"
    if not readme.exists():
        return 0
    
    content = readme.read_text(encoding="utf-8")
    
    # Find existing links
    links = set(re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content))
    
    md_files = [p for p in d.rglob("*.md") if p.name != "README.md"]
    
    linked = set()
    d_abs = d.resolve()
    for p in md_files:
        rel = str(p.relative_to(d)).replace("\\", "/")
        for text, link in links:
            if link.endswith(".md"):
                resolved = (readme.parent / link).resolve()
                try:
                    if str(resolved.relative_to(d_abs)).replace("\\", "/") == rel:
                        linked.add(rel)
                except ValueError:
                    pass
    
    all_files = set(str(p.relative_to(d)).replace("\\", "/") for p in md_files)
    missing = sorted(all_files - linked)
    
    if not missing:
        return 0
    
    # Build supplement section
    lines = ["\n### 补充文件索引\n"]
    for rel in missing:
        filepath = d / rel
        title = get_file_title(filepath)
        lines.append(f"- [{title}](./{rel})")
    lines.append("")
    
    supplement = "\n".join(lines)
    
    # Insert after the file index section
    # Find "## 二、文件索引与关系" or similar
    section_match = re.search(r'(##\s+.*?文件索引.*?\n)', content)
    if section_match:
        # Find the next ## section after file index
        start = section_match.end()
        next_section = re.search(r'\n##\s', content[start:])
        if next_section:
            insert_pos = start + next_section.start()
        else:
            insert_pos = len(content)
        new_content = content[:insert_pos] + supplement + content[insert_pos:]
    else:
        # No file index section found, append to end
        new_content = content.rstrip() + "\n" + supplement
    
    if new_content != content:
        readme.write_text(new_content, encoding="utf-8")
        return len(missing)
    return 0

fixed_count = {}
for d in sorted(Path("concept").iterdir()):
    if not d.is_dir() or d.name.startswith("."):
        continue
    count = fix_readme(d)
    if count > 0:
        fixed_count[d.name] = count

print(f"Fixed {len(fixed_count)} READMEs")
for name, count in fixed_count.items():
    print(f"  {name}: +{count} links")
