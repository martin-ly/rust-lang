#!/usr/bin/env python3
"""移除 docs/ 中指向状态/维护说明/最后更新/下次更新等非标题行的目录项。"""
import re
from pathlib import Path

DOCS_DIR = Path("docs")

# 通用模式：目录项中包含 **状态** / **维护说明** / **最后更新** / **下次更新**
GENERAL_PATTERNS = [
    r"^\s+-\s+\[\*\*状态\*\*:.*$",
    r"^\s+-\s+\[\*\*维护说明\*\*:.*$",
    r"^\s+-\s+\[\*\*最后更新\*\*:.*$",
    r"^\s+-\s+\[\*\*下次更新\*\*：.*$",
    r"^\s+-\s+\[\*\*下次更新\*\*:.*$",
]

# 特定文件：指向不存在的标题
SPECIFIC = {
    "research_notes/10_comprehensive_systematic_overview.md": r"^\s+-\s+\[思维表征方式全索引\].*$",
    "research_notes/10_contributing.md": [
        r"^\s+-\s+\[质量标准\].*$",
        r"^\s+-\s+\[检查清单\].*$",
    ],
    "research_notes/10_design_mechanism_rationale.md": r"^\s+-\s+\[DESIGN_MECHANISM_RATIONALE 矩阵总览\].*$",
    "research_notes/10_learning_path_comprehensive.md": r"^\s+-\s+\[反例集\].*$",
}


def remove_patterns(path: Path, patterns):
    if not path.exists():
        return 0
    content = path.read_text(encoding="utf-8")
    lines = content.splitlines()
    new_lines = []
    removed = 0
    for line in lines:
        drop = any(re.match(p, line) for p in patterns)
        if drop:
            removed += 1
        else:
            new_lines.append(line)
    if removed:
        path.write_text("\n".join(new_lines), encoding="utf-8")
        print(f"已清理 {path}: {removed} 行")
    return removed


def main():
    total = 0

    # 扫描所有 docs/ 文件应用通用模式
    for md in sorted(DOCS_DIR.rglob("*.md")):
        total += remove_patterns(md, GENERAL_PATTERNS)

    # 特定文件
    for rel_path, patterns in SPECIFIC.items():
        if isinstance(patterns, str):
            patterns = [patterns]
        total += remove_patterns(DOCS_DIR / rel_path, patterns)

    print(f"\n总计移除 {total} 个无效目录项")


if __name__ == "__main__":
    main()
