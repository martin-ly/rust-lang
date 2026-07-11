#!/usr/bin/env python3
"""Fix rust-lang.github.io/rfcs/ links with wrong slugs.

Fetches the RFC list from GitHub API, builds a number->slug map,
then scans Markdown files and corrects RFC URLs whose slug does not
match the repository filename.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

import urllib.request
import urllib.error
import json


ROOT = Path(__file__).resolve().parents[2]
SCAN_DIRS = ["concept", "knowledge", "docs"]
CACHE_FILE = ROOT / "target" / "i18n_rfc_map.json"

RFC_BASE = "https://rust-lang.github.io/rfcs/"
TREE_API = "https://api.github.com/repos/rust-lang/rfcs/git/trees/master?recursive=1"


def fetch_rfc_map() -> dict[str, str]:
    """Fetch RFC filenames from GitHub tree API and build number -> slug map."""
    mapping: dict[str, str] = {}
    req = urllib.request.Request(
        TREE_API,
        headers={
            "Accept": "application/vnd.github.v3+json",
            "User-Agent": "rust-lang-i18n-link-fix/1.0",
        },
    )
    try:
        with urllib.request.urlopen(req, timeout=60) as resp:
            data = json.load(resp)
    except urllib.error.HTTPError as e:
        print(f"GitHub API error: {e}", file=sys.stderr)
        return mapping
    for item in data.get("tree", []):
        path = item.get("path", "")
        if not path.startswith("text/"):
            continue
        name = path.split("/")[-1]
        m = re.match(r"(\d{4})-(.+)\.md$", name)
        if m:
            mapping[m.group(1)] = m.group(2)
    return mapping


def load_rfc_map() -> dict[str, str]:
    """Load cached RFC map or fetch and cache it."""
    if CACHE_FILE.exists():
        try:
            with open(CACHE_FILE, encoding="utf-8") as f:
                data = json.load(f)
            if data:
                return data
        except (json.JSONDecodeError, OSError):
            pass
    mapping = fetch_rfc_map()
    if mapping:
        CACHE_FILE.parent.mkdir(parents=True, exist_ok=True)
        with open(CACHE_FILE, "w", encoding="utf-8") as f:
            json.dump(mapping, f, indent=2)
    return mapping


def fix_rfc_url(url: str, rfc_map: dict[str, str]) -> str | None:
    if not url.startswith(RFC_BASE):
        return None
    rest = url[len(RFC_BASE):]
    # Strip trailing punctuation / markdown noise
    rest = rest.rstrip(".,;:!?)]}")
    if not rest.endswith(".html"):
        return None
    stem = rest[:-5]  # e.g. "1414-lifetime-elision"
    m = re.match(r"(\d{4})-(.+)", stem)
    if not m:
        return None
    number, slug = m.group(1), m.group(2)
    correct_slug = rfc_map.get(number)
    if correct_slug and correct_slug != slug:
        return f"{RFC_BASE}{number}-{correct_slug}.html"
    return None


def fix_text(text: str, rfc_map: dict[str, str]) -> tuple[str, int]:
    changes = 0
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
                    fixed = fix_rfc_url(url, rfc_map)
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
            fixed = fix_rfc_url(url, rfc_map)
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

    print("Loading RFC list...", file=sys.stderr)
    rfc_map = load_rfc_map()
    print(f"Loaded {len(rfc_map)} RFC entries.", file=sys.stderr)
    if not rfc_map:
        print("No RFC mapping available, aborting.", file=sys.stderr)
        return 1

    total_changes = 0
    files_changed = 0
    for dir_name in SCAN_DIRS:
        base = ROOT / dir_name
        if not base.exists():
            continue
        for path in base.rglob("*.md"):
            text = path.read_text(encoding="utf-8", errors="ignore")
            new_text, changes = fix_text(text, rfc_map)
            if changes:
                total_changes += changes
                files_changed += 1
                if not args.dry_run:
                    path.write_text(new_text, encoding="utf-8")
                print(f"{'[DRY-RUN] ' if args.dry_run else ''}{path.relative_to(ROOT)}: {changes} changes")

    print(f"\nTotal: {total_changes} RFC URL fixes across {files_changed} files")
    return 0


if __name__ == "__main__":
    sys.exit(main())
