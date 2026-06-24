#!/usr/bin/env python3
"""为缺失 `内容分级` 元数据的 C 类 Markdown 文件补齐头部。"""

import sys
from pathlib import Path

DIRECTORIES = [
    Path("docs/research_notes"),
    Path("docs/rust-ownership-decidability"),
]

GRADE = "> **内容分级**: 归档级"


def process_file(path: Path) -> bool:
    text = path.read_text(encoding="utf-8-sig")
    if "内容分级" in text:
        return False

    lines = text.splitlines(keepends=True)
    insert_idx = None
    for i, line in enumerate(lines):
        if line.lstrip().startswith("> **"):
            insert_idx = i
            break

    if insert_idx is None:
        # 没有元数据块：在标题后插入
        for i, line in enumerate(lines):
            if line.startswith("# "):
                insert_idx = i + 1
                # 跳过 trailing blank lines
                while insert_idx < len(lines) and lines[insert_idx].strip() == "":
                    insert_idx += 1
                break

    if insert_idx is None:
        print(f"WARN: 无法确定插入位置: {path}", file=sys.stderr)
        return False

    # 确保插入位置前有空行（如果前面不是空行或文件开头）
    prefix = []
    if insert_idx > 0 and lines[insert_idx - 1].strip() != "":
        prefix.append("\n")
    new_lines = prefix + [GRADE + "\n", "\n"]
    lines[insert_idx:insert_idx] = new_lines
    path.write_text("".join(lines), encoding="utf-8")
    return True


def main() -> int:
    modified = 0
    for directory in DIRECTORIES:
        if not directory.exists():
            continue
        for path in sorted(directory.rglob("*.md")):
            if process_file(path):
                print(f"+ {path}")
                modified += 1
    print(f"\n共修改 {modified} 个文件")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
