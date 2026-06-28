#!/usr/bin/env python3
"""Batch-fix common broken external link patterns in Markdown files.

Run with --dry-run first to preview. Currently handles:
- Wikipedia spaces -> underscores and known wrong titles
- Some commonly-moved URLs (tokio.rs, marabos.nl, releases.rs)
- Trailing markdown punctuation in extracted URLs
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCAN_DIRS = ["concept", "knowledge", "docs"]

WIKIPEDIA_FIXES = {
    # wrong -> correct (case/underscore fixes)
    "https://en.wikipedia.org/wiki/Type_System": "https://en.wikipedia.org/wiki/Type_system",
    "https://en.wikipedia.org/wiki/Generic_Programming": "https://en.wikipedia.org/wiki/Generic_programming",
    "https://en.wikipedia.org/wiki/Separation_Logic": "https://en.wikipedia.org/wiki/Separation_logic",
    "https://en.wikipedia.org/wiki/Affine_Logic": "https://en.wikipedia.org/wiki/Affine_logic",
    "https://en.wikipedia.org/wiki/Higher_kinded_type": "https://en.wikipedia.org/wiki/Higher-kinded_type",
    "https://en.wikipedia.org/wiki/Trait_based_Programming": "https://en.wikipedia.org/wiki/Trait-based_programming",
    "https://en.wikipedia.org/wiki/Programming_Language_Comparison": "https://en.wikipedia.org/wiki/Comparison_of_programming_languages",
    "https://en.wikipedia.org/wiki/Ownership_type": "https://en.wikipedia.org/wiki/Ownership_types",
    "https://en.wikipedia.org/wiki/Region_based_memory_management": "https://en.wikipedia.org/wiki/Region-based_memory_management",
    "https://en.wikipedia.org/wiki/Design_pattern": "https://en.wikipedia.org/wiki/Design_pattern",
    "https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization_(RAII)": "https://en.wikipedia.org/wiki/Resource_acquisition_is_initialization",
}

URL_REPLACEMENTS = {
    # Known moved/removed resources
    "https://releases.rs/1.95.0/": "https://releases.rs/",
    # Tokio topics reorganized into tutorial (old /tokio/topics/X pages removed)
    "https://tokio.rs/tokio/topics/runtime": "https://tokio.rs/tokio/tutorial",
    "https://tokio.rs/tokio/topics/internals": "https://tokio.rs/tokio/topics",
    "https://tokio.rs/tokio/topics/cancellation": "https://tokio.rs/tokio/tutorial/select",
    "https://tokio.rs/tokio/topics/shared-state": "https://tokio.rs/tokio/tutorial/shared-state",
    "https://tokio.rs/tokio/topics/backpressure": "https://tokio.rs/tokio/tutorial",
    "https://tokio.rs/tokio/topics/io": "https://tokio.rs/tokio/tutorial/io",
    "https://tokio.rs/tokio/topics/runtime-internals": "https://tokio.rs/tokio/topics",
    "https://tokio.rs/docs": "https://tokio.rs/tokio/tutorial",
    # TRPL 3rd edition chapter renames
    "https://doc.rust-lang.org/book/ch13-00-functional-features-of-rust.html": "https://doc.rust-lang.org/book/ch13-00-functional-features.html",
    "https://doc.rust-lang.org/book/ch16-00-fearless-concurrency.html": "https://doc.rust-lang.org/book/ch16-00-concurrency.html",
    "https://doc.rust-lang.org/book/ch17-01-futures-and-async.html": "https://doc.rust-lang.org/book/ch17-01-futures-and-syntax.html",
    "https://doc.rust-lang.org/book/ch17-03-std-futures.html": "https://doc.rust-lang.org/book/ch17-02-concurrency-with-async.html",
}


def fix_url(url: str) -> str | None:
    """Return fixed URL or None.

    Only applies safe, known transformations:
    - Wikipedia spaces -> underscores
    - Wikipedia missing closing paren in disambiguation titles
    - Known wrong Wikipedia titles / moved URLs
    """
    original = url

    # Wikipedia specific fixes
    if url.startswith("https://en.wikipedia.org/wiki/"):
        # Fix missing closing paren for Wikipedia disambiguation titles
        if url.count("(") > url.count(")"):
            url += ")"

        title = url[len("https://en.wikipedia.org/wiki/"):]
        # Remove fragment temporarily
        fragment = ""
        if "#" in title:
            title, fragment = title.split("#", 1)
        fixed_title = title.replace(" ", "_")
        # Preserve fragment
        new_url = "https://en.wikipedia.org/wiki/" + fixed_title
        if fragment:
            new_url += "#" + fragment
        if new_url != url:
            url = new_url

    # Known exact replacements
    if url in WIKIPEDIA_FIXES:
        url = WIKIPEDIA_FIXES[url]
    if url in URL_REPLACEMENTS:
        url = URL_REPLACEMENTS[url]

    return url if url != original else None


def fix_text(text: str) -> tuple[str, int]:
    """Fix URLs in Markdown text. Returns (new_text, change_count)."""
    changes = 0

    # Helper to replace URL if fixable
    def maybe_replace(match: re.Match) -> str:
        nonlocal changes
        url = match.group(0)
        fixed = fix_url(url)
        if fixed and fixed != url:
            changes += 1
            return fixed
        return url

    # Markdown links [text](url)
    def replace_md_link(match: re.Match) -> str:
        nonlocal changes
        text_part = match.group(1)
        url = match.group(2)
        fixed = fix_url(url)
        if fixed and fixed != url:
            changes += 1
            return f"[{text_part}]({fixed})"
        return match.group(0)

    # Process Markdown links with balanced parens
    new_text = ""
    i = 0
    while i < len(text):
        if text.startswith("```", i):
            end = text.find("\n```", i + 3)
            if end == -1:
                new_text += text[i:]
                break
            new_text += text[i:end + 4]
            i = end + 4
            continue
        if text.startswith("`", i):
            end = text.find("`", i + 1)
            if end == -1:
                new_text += text[i:]
                break
            new_text += text[i:end + 1]
            i = end + 1
            continue
        if text[i] == "[" and i + 1 < len(text):
            close_bracket = text.find("]", i + 1)
            if close_bracket != -1 and close_bracket + 1 < len(text) and text[close_bracket + 1] == "(":
                # find matching paren
                depth = 1
                j = close_bracket + 2
                while j < len(text):
                    if text[j] == "(":
                        depth += 1
                    elif text[j] == ")":
                        depth -= 1
                        if depth == 0:
                            break
                    j += 1
                if j < len(text):
                    link_text = text[i + 1:close_bracket]
                    url = text[close_bracket + 2:j]
                    fixed = fix_url(url)
                    if fixed and fixed != url:
                        changes += 1
                        new_text += f"[{link_text}]({fixed})"
                    else:
                        new_text += text[i:j + 1]
                    i = j + 1
                    continue
        # bare URL
        match = re.match(r"https?://[^\s\"'<>\]`|]+", text[i:])
        if match:
            url = match.group(0)
            fixed = fix_url(url)
            if fixed and fixed != url:
                changes += 1
                new_text += fixed
            else:
                new_text += url
            i += len(url)
            continue
        new_text += text[i]
        i += 1

    return new_text, changes


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dry-run", action="store_true")
    args = parser.parse_args()

    total_changes = 0
    files_changed = 0

    for dir_name in SCAN_DIRS:
        base = ROOT / dir_name
        if not base.exists():
            continue
        for path in base.rglob("*.md"):
            text = path.read_text(encoding="utf-8")
            new_text, changes = fix_text(text)
            if changes:
                total_changes += changes
                files_changed += 1
                if not args.dry_run:
                    path.write_text(new_text, encoding="utf-8")
                print(f"{'[DRY-RUN] ' if args.dry_run else ''}{path.relative_to(ROOT)}: {changes} changes")

    print(f"\nTotal: {total_changes} URL fixes across {files_changed} files")
    return 0


if __name__ == "__main__":
    sys.exit(main())
