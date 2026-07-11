#!/usr/bin/env python3
"""
Batch version declaration refresh for research_notes/.

Strategy:
- Update generic MSRV declarations: 'Rust 版本: 1.94.0' -> 'Rust 版本: 1.96.0'
- Update rust-version in TOML examples: rust-version = "1.94" -> "1.96"
- Skip historical facts (context contains introduced/stabilized/起始版本/comparison)
- Add [历史声明] marker to historical context that wasn't caught

Usage: python scripts/batch_version_refresh.py [--apply]
"""

import argparse
import re
from pathlib import Path

TARGET_DIR = Path("docs/research_notes")
OLD_VERSION = "1.94.0"
NEW_VERSION = "1.96.0"
OLD_RUST_VERSION = 'rust-version = "1.94"'
NEW_RUST_VERSION = 'rust-version = "1.96"'

HISTORY_KEYWORDS = ["introduced", "stabilized", "起始版本", "comparison", "迁移", "起始", "added in", "since"]

def is_historical_context(lines, match_line_idx):
    """Check if the matched line is in a historical context."""
    context = ""
    start = max(0, match_line_idx - 2)
    end = min(len(lines), match_line_idx + 3)
    for i in range(start, end):
        context += lines[i] + " "
    context_lower = context.lower()
    return any(kw in context_lower for kw in HISTORY_KEYWORDS)

def process_file(filepath: Path, dry_run: bool = True) -> dict:
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            content = f.read()
            lines = content.split("\n")
    except Exception as e:
        return {"error": str(e)}

    modified = False
    new_lines = []
    changes = []

    for i, line in enumerate(lines):
        new_line = line

        # Pattern 1: Generic MSRV declaration in metadata
        if OLD_VERSION in line:
            if not is_historical_context(lines, i):
                new_line = line.replace(OLD_VERSION, NEW_VERSION)
                if new_line != line:
                    changes.append(f"L{i+1}: {line.strip()[:60]}...")
                    modified = True
            else:
                # Historical context - add marker if not already present
                if "[历史声明]" not in line and "[历史]" not in line:
                    # Don't modify the version, just note it
                    changes.append(f"L{i+1}: [SKIP historical] {line.strip()[:50]}...")

        # Pattern 2: rust-version in TOML
        if OLD_RUST_VERSION in line:
            new_line = line.replace(OLD_RUST_VERSION, NEW_RUST_VERSION)
            if new_line != line:
                changes.append(f"L{i+1}: {line.strip()[:60]}...")
                modified = True

        new_lines.append(new_line)

    if modified and not dry_run:
        with open(filepath, "w", encoding="utf-8") as f:
            f.write("\n".join(new_lines))

    return {"modified": modified, "changes": changes}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--apply", action="store_true", help="Actually modify files")
    args = parser.parse_args()
    dry_run = not args.apply

    files = list(TARGET_DIR.rglob("*.md"))
    total_files = 0
    modified_files = 0
    total_changes = 0

    print(f"Scanning {len(files)} files in {TARGET_DIR}...")

    for f in sorted(files):
        result = process_file(f, dry_run)
        if result.get("error"):
            print(f"  ⚠️ {f.relative_to(TARGET_DIR)}: {result['error']}")
            continue

        if result["modified"]:
            total_files += 1
            modified_files += 1
            total_changes += len(result["changes"])
            print(f"\n📝 {f.relative_to(TARGET_DIR)}")
            for ch in result["changes"]:
                print(f"   {ch}")

    print(f"\n{'='*50}")
    print(f"Summary {'(DRY-RUN)' if dry_run else '(APPLIED)'}")
    print(f"  Files scanned: {len(files)}")
    print(f"  Files with 1.94 refs: {total_files}")
    print(f"  Files modified: {modified_files}")
    print(f"  Total changes: {total_changes}")
    if dry_run and modified_files > 0:
        print(f"\n  Use --apply to execute changes")

if __name__ == "__main__":
    main()
