#!/usr/bin/env python3
"""列出 crates/*/docs/ 中仍然较大且可能包含通用概念解释的文件。"""

from pathlib import Path

ROOT = Path("e:/_src/rust-lang")
DOCS_DIR = ROOT / "crates"

large_files = []
for docs_dir in DOCS_DIR.rglob("docs"):
    if not docs_dir.is_dir():
        continue
    for md_file in docs_dir.rglob("*.md"):
        if not md_file.is_file():
            continue
        lines = md_file.read_text(encoding="utf-8").count("\n") + 1
        if lines > 200:
            rel = md_file.relative_to(ROOT).as_posix()
            large_files.append((lines, rel))

large_files.sort(reverse=True)

print(f"crates/*/docs/ 中 >200 行的 .md 文件数: {len(large_files)}")
print("\n前 30 个最大文件:")
for lines, rel in large_files[:30]:
    print(f"  {lines:5d}  {rel}")
