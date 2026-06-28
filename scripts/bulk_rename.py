#!/usr/bin/env python3
"""
Bulk rename repository paths to snake_case and update internal references.

Usage:
    python scripts/bulk_rename.py <old_path> <new_path> [<old_path> <new_path> ...]

All paths are relative to the repository root. The script uses `git mv` for
tracked files and falls back to `mv` for untracked files. It then updates
references in tracked text files.
"""

from __future__ import annotations

import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

# Extensions considered worth scanning for internal references.
TEXT_EXTENSIONS = {
    ".md",
    ".json",
    ".toml",
    ".yaml",
    ".yml",
    ".py",
    ".rs",
    ".sh",
    ".js",
    ".hbs",
}


def run_git(args: list[str], check: bool = True) -> str:
    result = subprocess.run(
        ["git", *args], cwd=ROOT, capture_output=True, text=True, check=check
    )
    return result.stdout


def is_tracked(path: Path) -> bool:
    result = subprocess.run(
        ["git", "ls-files", "--error-unmatch", str(path)],
        cwd=ROOT,
        capture_output=True,
        text=True,
    )
    return result.returncode == 0


def rename_file(old: Path, new: Path) -> None:
    if not old.exists():
        raise FileNotFoundError(old)
    new.parent.mkdir(parents=True, exist_ok=True)
    if is_tracked(old):
        run_git(["mv", str(old), str(new)])
    else:
        old.rename(new)


def iter_tracked_files() -> list[Path]:
    out = run_git(["ls-files"], check=False)
    return [ROOT / line for line in out.splitlines() if line]


def escape_literal(s: str) -> str:
    return re.escape(s)


def update_references(renames: list[tuple[Path, Path]]) -> None:
    files = iter_tracked_files()
    # Build replacement specs once.
    specs: list[tuple[re.Pattern[str], str]] = []
    for old, new in renames:
        rel_old = old.relative_to(ROOT).as_posix()
        rel_new = new.relative_to(ROOT).as_posix()
        # Whole relative path from repo root (POSIX and Windows separators).
        specs.append((re.compile(escape_literal(rel_old)), rel_new))
        specs.append(
            (re.compile(escape_literal(rel_old.replace("/", "\\"))), rel_new.replace("/", "\\"))
        )
        # Path relative to a sibling under the same parent directory (common in links).
        parent_old = old.parent.relative_to(ROOT).as_posix() if old.parent != ROOT else ""
        parent_new = new.parent.relative_to(ROOT).as_posix() if new.parent != ROOT else ""
        if parent_old:
            old_from_parent = f"{parent_old}/{old.name}"
            new_from_parent = f"{parent_new}/{new.name}"
            specs.append((re.compile(escape_literal(old_from_parent)), new_from_parent))
            specs.append(
                (
                    re.compile(escape_literal(old_from_parent.replace("/", "\\"))),
                    new_from_parent.replace("/", "\\"),
                )
            )
        # Bare filename (only when it appears as part of a path/link, not plain text).
        specs.append((re.compile(r"(?<=[/\\])" + escape_literal(old.name) + r"(?=[\s\"'>)\]\n]|$)"), new.name))

    for f in files:
        if f.suffix.lower() not in TEXT_EXTENSIONS:
            continue
        try:
            text = f.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        new_text = text
        for pat, repl in specs:
            new_text = pat.sub(lambda _m, r=repl: r, new_text)
        if new_text != text:
            f.write_text(new_text, encoding="utf-8")


def main(argv: list[str]) -> int:
    if len(argv) % 2 != 0 or len(argv) < 2:
        print("Usage: bulk_rename.py <old> <new> [<old> <new> ...]", file=sys.stderr)
        return 1

    renames: list[tuple[Path, Path]] = []
    for i in range(0, len(argv), 2):
        old = ROOT / argv[i]
        new = ROOT / argv[i + 1]
        renames.append((old, new))

    for old, new in renames:
        if not old.exists():
            # Already renamed or never existed; still update references below.
            print(f"Skipping (missing): {old.relative_to(ROOT)}")
            continue
        print(f"Renaming: {old.relative_to(ROOT)} -> {new.relative_to(ROOT)}")
        rename_file(old, new)

    print("Updating references...")
    update_references(renames)
    print("Done.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
