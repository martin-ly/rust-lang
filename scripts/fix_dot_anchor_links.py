#!/usr/bin/env python3
"""
Remove redundant leading dot from same-file anchor links.

Converts:
    [text](.#anchor)
to:
    [text](#anchor)

Only touches Markdown files and only link targets that begin with '.#'.
Relative links like './path' or '../path' are left unchanged.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LINK_RE = re.compile(r"(\[[^\]]*\]\()\.#")


def fix_file(path: Path) -> int:
    text = path.read_text(encoding="utf-8")
    new_text, count = LINK_RE.subn(r"\1#", text)
    if count:
        path.write_text(new_text, encoding="utf-8")
    return count


def main() -> int:
    total = 0
    files = 0
    for md in ROOT.rglob("*.md"):
        try:
            md.relative_to(ROOT / ".git")
            continue
        except ValueError:
            pass
        try:
            md.relative_to(ROOT / "target")
            continue
        except ValueError:
            pass
        n = fix_file(md)
        if n:
            total += n
            files += 1
    print(f"Fixed {total} redundant '.#' anchor links in {files} files.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
