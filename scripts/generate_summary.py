#!/usr/bin/env python3
"""自动生成 mdBook SUMMARY.md，基于 concept/ 目录结构。"""

import os
import re
from pathlib import Path

CONCEPT_DIR = Path("concept")
OUTPUT_FILE = CONCEPT_DIR / "SUMMARY.md"

# 定义目录顺序和显示名称
DIR_ORDER = [
    ("README.md", "总览"),
    ("00.md", "L0 元信息层"),
    ("00_meta", "L0 元信息"),
    ("01.md", "L1 基础层"),
    ("01_foundation", "L1 基础概念"),
    ("02.md", "L2 进阶层"),
    ("02_intermediate", "L2 进阶概念"),
    ("03.md", "L3 高级层"),
    ("03_advanced", "L3 高级概念"),
    ("04.md", "L4 形式化层"),
    ("04_formal", "L4 形式化理论"),
    ("05.md", "L5 对比层"),
    ("05_comparative", "L5 对比分析"),
    ("06.md", "L6 生态层"),
    ("06_ecosystem", "L6 生态工程"),
    ("07.md", "L7 前沿层"),
    ("07_future", "L7 前沿趋势"),
]


def extract_title(filepath: Path) -> str:
    """从 Markdown 文件提取标题（第一个 # 行）。"""
    try:
        content = filepath.read_text(encoding="utf-8")
        for line in content.splitlines()[:20]:
            match = re.match(r"^#\s+(.+)", line.strip())
            if match:
                return match.group(1).strip()
    except Exception:
        pass
    return filepath.stem


def list_md_files(directory: Path) -> list[Path]:
    """列出目录下的 Markdown 文件（排除隐藏文件），按文件名排序。"""
    files = sorted([f for f in directory.iterdir() if f.is_file() and f.suffix == ".md" and not f.name.startswith(".")])
    return files


def generate_summary() -> str:
    lines = ["# Summary", ""]

    processed_dirs = set()

    for entry, display_name in DIR_ORDER:
        path = CONCEPT_DIR / entry

        if path.is_file():
            title = extract_title(path)
            rel = path.relative_to(CONCEPT_DIR).as_posix()
            lines.append(f"- [{title}]({rel})")
            lines.append("")

        elif path.is_dir():
            readme = path / "README.md"
            if readme.exists():
                lines.append(f"- [{display_name}]({readme.relative_to(CONCEPT_DIR).as_posix()})")
            else:
                lines.append(f"- [{display_name}]()")
            for md_file in list_md_files(path):
                title = extract_title(md_file)
                rel = md_file.relative_to(CONCEPT_DIR).as_posix()
                # 跳过 README.md 作为默认页面
                if md_file.name == "README.md":
                    continue
                lines.append(f"  - [{title}]({rel})")
            lines.append("")
            processed_dirs.add(entry)

    # 处理未在 DIR_ORDER 中列出的目录或文件
    for item in sorted(CONCEPT_DIR.iterdir()):
        rel_name = item.relative_to(CONCEPT_DIR).as_posix()
        if rel_name in [e for e, _ in DIR_ORDER]:
            continue
        if item.is_file() and item.suffix == ".md":
            title = extract_title(item)
            rel = item.relative_to(CONCEPT_DIR).as_posix()
            lines.append(f"- [{title}]({rel})")
            lines.append("")

    return "\n".join(lines)


if __name__ == "__main__":
    summary = generate_summary()
    OUTPUT_FILE.write_text(summary, encoding="utf-8")
    print(f"✅ 已生成 {OUTPUT_FILE}")
    print(f"   总条目数: {summary.count(chr(10) + '-')}")
