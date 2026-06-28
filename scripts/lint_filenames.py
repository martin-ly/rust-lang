#!/usr/bin/env python3
"""
Filename lint: enforce snake_case / number_prefix_snake_case naming.

Default mode checks files changed relative to a base ref (origin/main).
Use --all to check every tracked file (returns warnings only by default).
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parents[1]

# Ensure stdout can emit UTF-8 paths on Windows.
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")

# Special files allowed at any depth (all-caps conventional names).
ALLOWED_SPECIAL_FILES = {
    "README.md",
    "INDEX.md",
    "CONTRIBUTING.md",
    "CHANGELOG.md",
    "SECURITY.md",
    "CODE_OF_CONDUCT.md",
    "LICENSE",
    "Cargo.toml",
    "rust-toolchain.toml",
}

# Top-level directories that are grandfathered or hidden config dirs.
ALLOWED_TOP_DIRS = {
    ".cargo",
    ".git",
    ".github",
    ".kimi",
    ".vscode",
    "archive",
    "book",
    "concept",
    "content",
    "crates",
    "docs",
    "examples",
    "exercises",
    "guides",
    "k8s",
    "knowledge",
    "reports",
    "scripts",
    "supply-chain",
    "target",
    "theme",
    "tools",
}

DEFAULT_EXCLUDE_PREFIXES = {
    "archive/",
    ".kimi/archive/",
    "target/",
    ".git/",
}

# Matches snake_case or number_prefix_snake_case directory/file base names.
_SNAKE_RE = re.compile(r"^[0-9]+(_[0-9]+)*_[a-z0-9_]+$|^[a-z0-9_]+$")

# Matches conventional filenames like name.ext, with optional single dot extension.
_FILE_RE = re.compile(
    r"^(?:[0-9]+(_[0-9]+)*_[a-z0-9_]+|[a-z0-9_]+)(\.[a-zA-Z0-9]+)?$"
)


def is_allowed_file(name: str) -> bool:
    if name in ALLOWED_SPECIAL_FILES:
        return True
    if name.startswith("."):
        return True  # hidden files (e.g., .gitignore)
    return bool(_FILE_RE.fullmatch(name))


def is_allowed_dir(name: str, depth: int) -> bool:
    if depth == 1 and name in ALLOWED_TOP_DIRS:
        return True
    if name.startswith("."):
        return True
    return bool(_SNAKE_RE.fullmatch(name))


def _rel_posix(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def is_excluded(path: Path, excludes: set[str]) -> bool:
    rel = _rel_posix(path)
    for prefix in excludes:
        if rel.startswith(prefix):
            return True
    return False


def get_changed_files(base_ref: str) -> list[Path]:
    result = subprocess.run(
        ["git", "diff", "--name-only", "--diff-filter=ACMR", base_ref],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    paths = [ROOT / p for p in result.stdout.splitlines() if p]
    return [p for p in paths if p.exists()]


def get_all_files() -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files"], cwd=ROOT, capture_output=True, text=True, check=True
    )
    return [ROOT / p for p in result.stdout.splitlines() if p]


def check_path(path: Path) -> list[str]:
    violations: list[str] = []
    parts = path.relative_to(ROOT).parts
    for depth, component in enumerate(parts[:-1], start=1):
        if not is_allowed_dir(component, depth):
            violations.append(f"directory '{component}' in {path.relative_to(ROOT)}")
    filename = parts[-1]
    if not is_allowed_file(filename):
        violations.append(f"file '{filename}' in {path.relative_to(ROOT)}")
    return violations


def main() -> int:
    parser = argparse.ArgumentParser(description="Lint filenames for snake_case.")
    parser.add_argument(
        "--since-ref",
        default="origin/main",
        help="Base ref for changed-file mode (default: origin/main).",
    )
    parser.add_argument(
        "--all",
        action="store_true",
        help="Check all tracked files instead of only changed files.",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Return non-zero even in --all mode if violations are found.",
    )
    parser.add_argument(
        "--exclude",
        action="append",
        default=[],
        help="Additional path prefix to exclude (can be given multiple times).",
    )
    args = parser.parse_args()

    excludes = DEFAULT_EXCLUDE_PREFIXES | set(args.exclude)
    files = get_all_files() if args.all else get_changed_files(args.since_ref)
    all_violations: list[str] = []
    for f in files:
        if is_excluded(f, excludes):
            continue
        all_violations.extend(check_path(f))

    if not all_violations:
        print("No naming violations found.")
        return 0

    mode = "all tracked files" if args.all else f"files changed since {args.since_ref}"
    print(f"Naming violations ({mode}):")
    for v in all_violations:
        print(f"  - {v}")

    if not args.all or args.strict:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
