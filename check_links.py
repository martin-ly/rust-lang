#!/usr/bin/env python3
"""Check for broken local links in markdown files."""

import os
import re
from collections import defaultdict

# Regex to match markdown links: [text](path)
link_pattern = re.compile(r'\[([^\]]+)\]\(([^)]+)\)')
# Skip http/https links and anchors-only links
external_pattern = re.compile(r'^(https?://|mailto:|#)')


def get_all_md_files(base_dir):
    """Get all markdown files in directory."""
    md_files = set()
    for root, dirs, files in os.walk(base_dir):
        for f in files:
            if f.endswith('.md'):
                full_path = os.path.join(root, f)
                rel_path = os.path.relpath(full_path, base_dir).replace('\\', '/')
                md_files.add(rel_path)
    return md_files


def extract_links(md_file, base_dir):
    """Extract all local links from a markdown file."""
    links = []
    try:
        with open(md_file, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
    except Exception:
        return links

    for match in link_pattern.finditer(content):
        text, path = match.groups()
        clean_path = path.split('#')[0]
        clean_path = clean_path.split('?')[0]

        if not clean_path or external_pattern.match(clean_path):
            continue

        file_rel = os.path.relpath(md_file, base_dir).replace('\\', '/')
        file_dir = os.path.dirname(file_rel)

        if clean_path.startswith('/'):
            resolved = clean_path[1:]
        else:
            if file_dir:
                resolved = os.path.normpath(os.path.join(file_dir, clean_path)).replace('\\', '/')
            else:
                resolved = clean_path.replace('\\', '/')

        resolved = resolved.rstrip('/')
        # Remove leading ./ if present
        if resolved.startswith('./'):
            resolved = resolved[2:]
        links.append((text, clean_path, resolved))

    return links


def main():
    base_dir = 'docs'
    md_files = get_all_md_files(base_dir)

    broken_links = []
    total_links = 0

    for md_file in md_files:
        full_path = os.path.join(base_dir, md_file)
        links = extract_links(full_path, base_dir)

        for text, original_path, resolved_path in links:
            total_links += 1

            is_valid = False
            if resolved_path in md_files:
                is_valid = True
            elif (resolved_path + '/README.md') in md_files:
                is_valid = True
            elif original_path.endswith('/') and (resolved_path + '/README.md') in md_files:
                is_valid = True

            if not is_valid:
                broken_links.append((md_file, text, original_path, resolved_path))

    print(f'Total markdown files: {len(md_files)}')
    print(f'Total local links checked: {total_links}')
    print(f'Broken links found: {len(broken_links)}')
    print()

    if broken_links:
        print('=== BROKEN LINKS (grouped by source file) ===')
        by_source = defaultdict(list)
        for source, text, original, resolved in broken_links:
            by_source[source].append((text, original, resolved))

        for source in sorted(by_source.keys()):
            print(f'\n{source}:')
            for text, original, resolved in by_source[source][:5]:
                display_text = text[:50] + '...' if len(text) > 50 else text
                print(f'  - "{display_text}" -> {original}')
            if len(by_source[source]) > 5:
                print(f'  ... and {len(by_source[source]) - 5} more in this file')

        # Save full report
        with open('broken_links_report.txt', 'w', encoding='utf-8') as f:
            f.write(f'Total markdown files: {len(md_files)}\n')
            f.write(f'Total local links checked: {total_links}\n')
            f.write(f'Broken links found: {len(broken_links)}\n\n')
            f.write('=== ALL BROKEN LINKS ===\n\n')
            for source in sorted(by_source.keys()):
                f.write(f'{source}:\n')
                for text, original, resolved in by_source[source]:
                    f.write(f'  Link: "{text}"\n')
                    f.write(f'  Original: {original}\n')
                    f.write(f'  Resolved: {resolved}\n\n')

        print(f'\n\nFull report saved to: broken_links_report.txt')


if __name__ == '__main__':
    main()
