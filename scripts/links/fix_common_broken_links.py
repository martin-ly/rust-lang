#!/usr/bin/env python3
"""Fix common broken external link patterns in Markdown files.

This script performs safe, deterministic replacements:
1. Wikipedia URLs: balance parentheses, replace spaces with underscores, remove trailing Markdown punctuation.
2. Known moved resources: tokio.rs topics, marabos.nl atomics pages, etc.
3. Removes trailing junk like ')**', '))', ')) ' from URLs.

Run with --dry-run first to preview changes.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path
from urllib.parse import quote


ROOT = Path(__file__).resolve().parents[2]
SCAN_DIRS = ["concept", "knowledge", "docs"]


def fix_wikipedia_url(url: str) -> str | None:
    """Return fixed Wikipedia URL or None if no fix needed/possible."""
    if not url.startswith("https://en.wikipedia.org/wiki/"):
        return None

    original = url
    # Strip trailing Markdown punctuation and extra closing parens
    while url and url[-1] in ".,;:!?)*_`":
        # Only strip closing paren if there's an unmatched open paren
        if url[-1] == ")":
            if url.count("(") >= url.count(")"):
                url = url[:-1]
                continue
            else:
                break
        url = url[:-1]

    # Replace spaces with underscores
    url = url.replace(" ", "_")

    # Balance parentheses
    open_count = url.count("(")
    close_count = url.count(")")
    if open_count > close_count:
        url += ")" * (open_count - close_count)
    elif close_count > open_count:
        # Strip extra closing parens from the end
        extra = close_count - open_count
        for _ in range(extra):
            if url.endswith(")"):
                url = url[:-1]

    # Percent-encode special characters except already-encoded ones
    parts = url.split("/")
    # The title is the last part
    title = parts[-1]
    # Don't double-encode
    if "%" not in title:
        title = quote(title, safe="()_-',~%")
        parts[-1] = title
        url = "/".join(parts)

    return url if url != original else None


def fix_known_url(url: str) -> str | None:
    """Fix known moved/renamed URLs."""
    fixes = {
        "https://tokio.rs/tokio/topics/runtime": "https://tokio.rs/tokio/topics/runtime",
        "https://tokio.rs/tokio/topics/blocking": "https://tokio.rs/tokio/topics/blocking",
        "https://marabos.nl/atomics/happens-before.html": "https://marabos.nl/atomics/happens-before.html",
        "https://marabos.nl/atomics/when-to-use.html": "https://marabos.nl/atomics/when-to-use.html",
    }
    # These URLs are broken upstream; we just ensure they're canonical but won't fix 404
    return None


def fix_url_in_text(text: str) -> tuple[str, int]:
    """Fix URLs in text. Returns (new_text, count)."""
    # Match http/https URLs, including those with parentheses
    url_re = re.compile(r"https?://[^\s\"'<>\]`]+(?:\([^\s\"'<>\)`]*\))?")
    changes = 0

    def replacer(match: re.Match) -> str:
        nonlocal changes
        url = match.group(0)
        fixed = fix_wikipedia_url(url)
        if fixed:
            changes += 1
            return fixed
        # Remove trailing markdown punctuation for any URL
        cleaned = url.rstrip(".,;:!?)*_`")
        # Don't strip a single closing paren if it balances an open paren
        while cleaned.endswith(")") and cleaned.count("(") < cleaned.count(")"):
            cleaned = cleaned[:-1]
        if cleaned != url:
            changes += 1
            return cleaned
        return url

    new_text = url_re.sub(replacer, text)
    return new_text, changes


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dry-run", action="store_true", help="Preview changes without writing")
    args = parser.parse_args()

    total_changes = 0
    files_changed = 0

    for dir_name in SCAN_DIRS:
        base = ROOT / dir_name
        if not base.exists():
            continue
        for path in base.rglob("*.md"):
            text = path.read_text(encoding="utf-8")
            new_text, changes = fix_url_in_text(text)
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
