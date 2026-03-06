#!/usr/bin/env python3
"""
Cross-reference verification script for rust-ownership-decidability documentation.

This script:
1. Scans all markdown files for internal links
2. Checks if linked files exist
3. Identifies missing cross-references
4. Generates a verification report
"""

import os
import re
from pathlib import Path
from collections import defaultdict
import json

# Configuration
DOCS_ROOT = Path(".")
REPORT_FILE = "CROSS_REFERENCE_VERIFICATION_REPORT.md"

# Track statistics
total_links_checked = 0
broken_links = []
missing_cross_references = []
all_files = set()
all_links = defaultdict(list)  # source -> list of (target, line_num, line_content)
markdown_files = []
coq_files = []


def find_all_files():
    """Find all markdown and Coq files in the documentation."""
    global markdown_files, coq_files
    
    for root, dirs, files in os.walk(DOCS_ROOT):
        # Skip archive and progress directories for cleaner output
        dirs[:] = [d for d in dirs if d not in ['.git']]
        
        for file in files:
            file_path = Path(root) / file
            rel_path = file_path.relative_to(DOCS_ROOT)
            all_files.add(str(rel_path).replace('\\', '/'))
            
            if file.endswith('.md'):
                markdown_files.append(str(rel_path).replace('\\', '/'))
            elif file.endswith('.v'):
                coq_files.append(str(rel_path).replace('\\', '/'))


def extract_links_from_markdown(file_path):
    """Extract all internal links from a markdown file."""
    links = []
    
    try:
        with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
            content = f.read()
            lines = content.split('\n')
    except Exception as e:
        print(f"Error reading {file_path}: {e}")
        return links
    
    # Pattern for markdown links: [text](url)
    link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
    
    for line_num, line in enumerate(lines, 1):
        matches = re.finditer(link_pattern, line)
        for match in matches:
            link_text = match.group(1)
            link_url = match.group(2)
            
            # Skip external links and anchors-only links
            if link_url.startswith('http://') or link_url.startswith('https://') or \
               link_url.startswith('#') or link_url.startswith('mailto:'):
                continue
            
            # Skip images and special protocols
            if link_url.startswith('!') or link_url.startswith('data:'):
                continue
            
            links.append((link_text, link_url, line_num, line.strip()))
    
    return links


def resolve_link(source_file, link_url):
    """Resolve a relative link to an absolute path from docs root."""
    # Remove anchor part
    if '#' in link_url:
        link_url = link_url.split('#')[0]
    
    # Remove query parameters
    if '?' in link_url:
        link_url = link_url.split('?')[0]
    
    if not link_url:
        return None
    
    # Handle absolute paths (from docs root)
    if link_url.startswith('/'):
        return link_url[1:]
    
    # Handle relative paths
    source_dir = os.path.dirname(source_file)
    resolved = os.path.normpath(os.path.join(source_dir, link_url))
    return resolved.replace('\\', '/')


def check_all_links():
    """Check all links in all markdown files."""
    global total_links_checked
    
    for md_file in markdown_files:
        links = extract_links_from_markdown(DOCS_ROOT / md_file)
        
        for link_text, link_url, line_num, line_content in links:
            total_links_checked += 1
            resolved = resolve_link(md_file, link_url)
            
            if resolved:
                all_links[md_file].append((resolved, link_text, line_num, line_content))
                
                # Check if file exists
                if resolved not in all_files:
                    broken_links.append({
                        'source': md_file,
                        'target': link_url,
                        'resolved': resolved,
                        'line': line_num,
                        'context': line_content[:100]
                    })


def identify_missing_cross_references():
    """Identify files that could benefit from additional cross-references."""
    
    # Define key concept files that should be linked
    key_concepts = {
        'ownership': ['01-core-concepts/detailed-concepts/ownership-deep-dive.md',
                      '01-core-concepts/short-concepts/ownership-concept-card.md'],
        'borrowing': ['01-core-concepts/detailed-concepts/borrowing-in-depth.md',
                      '01-core-concepts/short-concepts/borrowing-concept-card.md'],
        'lifetimes': ['01-core-concepts/detailed-concepts/lifetimes-mastery.md',
                      '01-core-concepts/short-concepts/lifetime-concept-card.md'],
        'formal': ['formal-foundations/README.md'],
        'coq': ['coq-formalization/README.md'],
        'examples': ['COMPLETE_EXAMPLES_AND_COUNTEREXAMPLES.md'],
    }
    
    # Check each markdown file for potential missing links
    for md_file in markdown_files:
        if not os.path.exists(DOCS_ROOT / md_file):
            continue
            
        try:
            with open(DOCS_ROOT / md_file, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read().lower()
        except:
            continue
        
        # Check if file mentions key concepts but doesn't link to them
        for concept, target_files in key_concepts.items():
            # Skip if already links to target
            has_link = False
            if md_file in all_links:
                for resolved, _, _, _ in all_links[md_file]:
                    if any(t in resolved for t in target_files):
                        has_link = True
                        break
            
            if not has_link and concept in content:
                # Check if file should link to this concept
                # Skip README files of the concept itself
                if not any(md_file.endswith(t) for t in target_files):
                    missing_cross_references.append({
                        'source': md_file,
                        'concept': concept,
                        'suggested_targets': target_files
                    })


def generate_master_index():
    """Generate/update the master index with all cross-references."""
    
    index_content = """# Documentation Master Index

> Auto-generated cross-reference index for the Rust Ownership Decidability documentation.

## Table of Contents

1. [Documentation Structure](#documentation-structure)
2. [Core Concept Links](#core-concept-links)
3. [Formal Verification Links](#formal-verification-links)
4. [Case Study Links](#case-study-links)
5. [Cross-Reference Map](#cross-reference-map)

---

## Documentation Structure

### Core Documentation

| Document | Description |
|----------|-------------|
| [README.md](README.md) | Project overview and navigation |
| [READING_GUIDE.md](READING_GUIDE.md) | How to read this documentation |
| [FINAL_MASTER_INDEX.md](FINAL_MASTER_INDEX.md) | Manual master index |
| [MASTER_COMPREHENSIVE_ANALYSIS.md](MASTER_COMPREHENSIVE_ANALYSIS.md) | Comprehensive analysis |

### Core Concepts

| Topic | Detailed Guide | Quick Reference |
|-------|---------------|-----------------|
| Ownership | [ownership-deep-dive.md](01-core-concepts/detailed-concepts/ownership-deep-dive.md) | [ownership-concept-card.md](01-core-concepts/short-concepts/ownership-concept-card.md) |
| Borrowing | [borrowing-in-depth.md](01-core-concepts/detailed-concepts/borrowing-in-depth.md) | [borrowing-concept-card.md](01-core-concepts/short-concepts/borrowing-concept-card.md) |
| Lifetimes | [lifetimes-mastery.md](01-core-concepts/detailed-concepts/lifetimes-mastery.md) | [lifetime-concept-card.md](01-core-concepts/short-concepts/lifetime-concept-card.md) |

### Formal Foundations

| Area | Entry Point |
|------|-------------|
| Formal Models | [formal-foundations/models/](formal-foundations/models/) |
| Semantics | [formal-foundations/semantics/](formal-foundations/semantics/) |
| Proofs | [formal-foundations/proofs/](formal-foundations/proofs/) |
| Coq Formalization | [coq-formalization/](coq-formalization/) |

### Case Studies

| Category | Index |
|----------|-------|
| All Case Studies | [case-studies/README.md](case-studies/README.md) |
| Embedded | [case-studies/embedded/README.md](case-studies/embedded/README.md) |
| Blockchain | [case-studies/blockchain/README.md](case-studies/blockchain/README.md) |
| Web Development | [case-studies/wasm/README.md](case-studies/wasm/README.md) |

---

## Core Concept Links

### Ownership System

- **Theory**: [ownership-types.md](formal-foundations/models/ownership-types.md)
- **Practice**: [ownership-deep-dive.md](01-core-concepts/detailed-concepts/ownership-deep-dive.md)
- **Examples**: See examples in [COMPLETE_EXAMPLES_AND_COUNTEREXAMPLES.md](COMPLETE_EXAMPLES_AND_COUNTEREXAMPLES.md)

### Borrowing System

- **Theory**: [borrow-semantics.md](formal-foundations/models/borrow-semantics.md)
- **Practice**: [borrowing-in-depth.md](01-core-concepts/detailed-concepts/borrowing-in-depth.md)
- **Coq Proof**: [ReborrowComplete.v](coq-formalization/theories/Advanced/ReborrowComplete.v)

### Lifetimes

- **Theory**: [lifetime-logic.md](formal-foundations/models/lifetime-logic.md)
- **Practice**: [lifetimes-mastery.md](01-core-concepts/detailed-concepts/lifetimes-mastery.md)
- **Coq Proof**: [MetatheoryTermination.v](coq-formalization/theories/Advanced/MetatheoryTermination.v)

### Type System

- **Theory**: [type-system-formalization.md](formal-foundations/semantics/type-system-formalization.md)
- **Coq**: [TypeSystem.v](coq-formalization/theories/Typing/TypeSystem.v)

---

## Formal Verification Links

### Key Theorems

| Theorem | Natural Language | Coq Formalization |
|---------|-----------------|-------------------|
| Termination | [THEOREM_INTUITIONS.md](THEOREM_INTUITIONS.md) | [MetatheoryTermination.v](coq-formalization/theories/Advanced/MetatheoryTermination.v) |
| Decidability | [decidability_theorems.md](theorems/decidability_theorems.md) | [MetatheoryDecidability.v](coq-formalization/theories/Advanced/MetatheoryDecidability.v) |
| Type Safety | [memory-safety-proof.md](formal-foundations/proofs/memory-safety-proof.md) | [MetatheoryKeyProofs.v](coq-formalization/theories/Advanced/MetatheoryKeyProofs.v) |

### Coq File Organization

```
coq-formalization/
├── Syntax/           # Type and expression definitions
├── Typing/           # Type system rules
├── Semantics/        # Operational semantics
├── Metatheory/       # Key theorems and proofs
└── Advanced/         # Rust 1.94+ features
```

---

## Case Study Links

### Standard Library Case Studies

| Crate | Formal Analysis |
|-------|-----------------|
| Vec | [std-vec-formal-analysis.md](case-studies/std-vec-formal-analysis.md) |
| String | [std-string-formal-analysis.md](case-studies/std-string-formal-analysis.md) |
| HashMap | [std-hashmap-formal-analysis.md](case-studies/std-hashmap-formal-analysis.md) |
| Iterator | [std-iterator-formal-analysis.md](case-studies/std-iterator-formal-analysis.md) |
| Smart Pointers | [std-smart-pointers-formal-analysis.md](case-studies/std-smart-pointers-formal-analysis.md) |

### Async Ecosystem

| Crate | Formal Analysis |
|-------|-----------------|
| Tokio Runtime | [tokio-runtime-formal-analysis.md](case-studies/tokio-runtime-formal-analysis.md) |
| Async-std | [async-std-formal-analysis.md](case-studies/async-std-formal-analysis.md) |
| Futures | [futures-crate-formal-analysis.md](case-studies/futures-crate-formal-analysis.md) |

---

## Cross-Reference Map

"""
    
    # Add the cross-reference map
    index_content += "### Files Referenced By\n\n"
    
    # Build reverse mapping
    referenced_by = defaultdict(list)
    for source, links in all_links.items():
        for resolved, link_text, line_num, _ in links:
            referenced_by[resolved].append((source, link_text, line_num))
    
    # Sort by number of references
    sorted_refs = sorted(referenced_by.items(), key=lambda x: len(x[1]), reverse=True)
    
    for target, sources in sorted_refs[:50]:  # Top 50 most referenced
        if len(sources) > 0:
            index_content += f"\n**{target}** (referenced {len(sources)} times)\n"
            for source, link_text, line_num in sources[:5]:  # Show first 5
                index_content += f"  - [{source}]({source}): \"{link_text[:50]}...\"\n"
            if len(sources) > 5:
                index_content += f"  - ... and {len(sources) - 5} more\n"
    
    index_content += "\n---\n\n*This index was auto-generated. Last updated: " + \
                     __import__('datetime').datetime.now().isoformat() + "*\n"
    
    return index_content


def generate_report():
    """Generate the verification report."""
    
    report = f"""# Cross-Reference Verification Report

**Generated**: {__import__('datetime').datetime.now().isoformat()}

## Executive Summary

This report documents the cross-reference verification for the rust-ownership-decidability documentation.

| Metric | Count |
|--------|-------|
| Total Markdown Files | {len(markdown_files)} |
| Total Coq Files | {len(coq_files)} |
| Total Files | {len(all_files)} |
| Total Links Checked | {total_links_checked} |
| Broken Links Found | {len(broken_links)} |
| Missing Cross-References | {len(missing_cross_references)} |

## Broken Links

"""
    
    if broken_links:
        report += "### List of Broken Links\n\n"
        report += "| Source File | Broken Link | Line | Context |\n"
        report += "|-------------|-------------|------|---------|\n"
        
        for link in sorted(broken_links, key=lambda x: x['source']):
            context = link['context'].replace('|', '\\|')[:60]
            report += f"| {link['source']} | `{link['target']}` | {link['line']} | {context}... |\n"
    else:
        report += "✅ **No broken links found!**\n"
    
    report += "\n## Missing Cross-References\n\n"
    
    if missing_cross_references:
        report += "Files that mention key concepts but don't link to them:\n\n"
        report += "| Source File | Concept | Suggested Link |\n"
        report += "|-------------|---------|----------------|\n"
        
        for item in sorted(missing_cross_references, key=lambda x: x['source'])[:50]:
            targets = ', '.join(item['suggested_targets'])
            report += f"| {item['source']} | {item['concept']} | {targets} |\n"
    else:
        report += "✅ **No obvious missing cross-references detected!**\n"
    
    report += "\n## Recommendations\n\n"
    report += """### For Improving Navigation

1. **Add 'See Also' sections** to key documents linking related concepts
2. **Create topic hubs** for major themes (ownership, borrowing, lifetimes)
3. **Add breadcrumbs** at the top of each file showing its place in the hierarchy
4. **Link case studies to theory** - each case study should link to relevant formal foundations
5. **Link examples to proofs** - practical examples should reference Coq proofs

### For Maintaining Cross-References

1. Run this verification script regularly
2. Add link checking to CI/CD pipeline
3. Use relative paths for internal links
4. Avoid hardcoding file paths in multiple places

## Appendix: File Statistics

### Markdown Files by Directory

"""
    
    # Count files by directory
    dir_counts = defaultdict(int)
    for f in markdown_files:
        dir_name = os.path.dirname(f).split('/')[0] if '/' in f else 'root'
        dir_counts[dir_name] += 1
    
    for dir_name, count in sorted(dir_counts.items(), key=lambda x: x[1], reverse=True):
        report += f"- **{dir_name}**: {count} files\n"
    
    report += f"""

### Coq Files by Directory

"""
    
    coq_dirs = defaultdict(int)
    for f in coq_files:
        dir_name = os.path.dirname(f)
        coq_dirs[dir_name] += 1
    
    for dir_name, count in sorted(coq_dirs.items(), key=lambda x: x[1], reverse=True):
        report += f"- **{dir_name}**: {count} files\n"
    
    report += "\n---\n\n*Report generated by check_cross_references.py*\n"
    
    return report


def main():
    print("=" * 60)
    print("Cross-Reference Verification Tool")
    print("=" * 60)
    
    print("\n1. Finding all files...")
    find_all_files()
    print(f"   Found {len(markdown_files)} markdown files")
    print(f"   Found {len(coq_files)} Coq files")
    
    print("\n2. Checking all links...")
    check_all_links()
    print(f"   Checked {total_links_checked} links")
    
    if broken_links:
        print(f"   ⚠️  Found {len(broken_links)} broken links")
    else:
        print("   ✅ No broken links found")
    
    print("\n3. Identifying missing cross-references...")
    identify_missing_cross_references()
    print(f"   Found {len(missing_cross_references)} potential missing links")
    
    print("\n4. Generating master index...")
    index_content = generate_master_index()
    index_path = DOCS_ROOT / "MASTER_INDEX_AUTO.md"
    with open(index_path, 'w', encoding='utf-8') as f:
        f.write(index_content)
    print(f"   Written to {index_path}")
    
    print("\n5. Generating verification report...")
    report_content = generate_report()
    report_path = DOCS_ROOT / REPORT_FILE
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write(report_content)
    print(f"   Written to {report_path}")
    
    print("\n" + "=" * 60)
    print("Verification Complete!")
    print("=" * 60)
    print(f"\nSummary:")
    print(f"  - Markdown files: {len(markdown_files)}")
    print(f"  - Links checked: {total_links_checked}")
    print(f"  - Broken links: {len(broken_links)}")
    print(f"  - Missing refs: {len(missing_cross_references)}")


if __name__ == "__main__":
    main()
