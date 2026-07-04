#!/usr/bin/env python3
"""
命名规范检查器

检查活跃目录中的文件/目录是否符合 NAMING_CONVENTION.md 的 snake_case 要求。

用法:
    python3 scripts/check_naming_convention.py
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

SCAN_DIRS = ["concept", "knowledge", "docs", "content", "guides", "examples", "exercises", "scripts", "tools"]
EXCLUDE_DIRS = {
    "archive", "deprecated", "sources", "target", ".git",
    "node_modules", "__pycache__", ".venv", "venv", ".pytest_cache",
}

SNAKE_PATTERN = re.compile(r"^[a-z0-9_\-.]+$")

ALLOWED_STANDARD = {
    "readme.md", "contributing.md", "license", "copying", "agents.md",
    "changelog.md", "changes.md", "cargo.toml", "cargo.lock",
    ".gitignore", ".gitattributes", ".editorconfig", ".markdownlint.json",
    ".cursorignore", ".clippy.toml", "dockerfile", "docker-compose.yml",
    "docker-compose.yaml", "makefile", "justfile", "summary.md", "index.md",
    "book.toml", "rust-toolchain.toml", "package.json", "tsconfig.json",
    ".eslintrc.json", ".prettierrc", "pyproject.toml", "setup.py", "requirements.txt",
    "main.rs", "lib.rs", "mod.rs", "build.rs", "main.py", "__init__.py",
}


def is_valid(name: str) -> bool:
    if name.lower() in ALLOWED_STANDARD:
        return True
    if name.startswith("."):
        return True
    return bool(SNAKE_PATTERN.match(name))


def main() -> int:
    violations = []
    for d in SCAN_DIRS:
        root = ROOT / d
        if not root.exists():
            continue
        for p in root.rglob("*"):
            if any(part in EXCLUDE_DIRS for part in p.parts):
                continue
            if not is_valid(p.name):
                violations.append(str(p.relative_to(ROOT)))

    if violations:
        print(f"❌ 发现 {len(violations)} 个不符合 snake_case 的命名:")
        for v in violations:
            print(f"  - {v}")
        return 1

    print("✅ 活跃目录中所有文件/目录均符合 snake_case 命名规范。")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
