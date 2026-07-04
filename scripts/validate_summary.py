#!/usr/bin/env python3
"""
校验 concept/SUMMARY.md 与实际文件的一致性。

检查项：
1. SUMMARY 中链接的每个 .md 文件是否真实存在。
2. concept/ 下（排除 archive/、sources/、README.md）的每个 .md 文件是否都在 SUMMARY 中有链接。
3. 文件路径是否与推荐的主题子目录结构一致（警告级别）。

用法：
    python scripts/validate_summary.py
"""

from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import concept_config

SUMMARY_PATH = concept_config.CONCEPT_DIR / "SUMMARY.md"


def parse_summary_links(summary_text: str) -> list[tuple[str, str]]:
    """解析 SUMMARY.md 中的 Markdown 链接，返回 (显示文本, 相对路径) 列表。

    兼容链接文本中的代码段、嵌套方括号与反斜杠转义。
    """
    links: list[tuple[str, str]] = []
    i = 0
    n = len(summary_text)
    while i < n:
        if summary_text[i] == "[" and (i == 0 or summary_text[i - 1] != "\\"):
            start = i
            depth = 1
            i += 1
            in_code = False
            code_delim = ""
            while i < n and depth > 0:
                if not in_code:
                    if summary_text[i] == "\\" and i + 1 < n:
                        i += 2
                        continue
                    if summary_text[i] == "`":
                        j = i
                        while j < n and summary_text[j] == "`":
                            j += 1
                        code_delim = summary_text[i:j]
                        in_code = True
                        i = j
                        continue
                    if summary_text[i] == "[":
                        depth += 1
                    elif summary_text[i] == "]":
                        depth -= 1
                else:
                    if summary_text[i : i + len(code_delim)] == code_delim:
                        in_code = False
                        i += len(code_delim)
                        continue
                i += 1
            if depth == 0 and i < n and summary_text[i] == "(":
                j = i + 1
                pdepth = 1
                while j < n and pdepth > 0:
                    if summary_text[j] == "\\" and j + 1 < n:
                        j += 2
                        continue
                    if summary_text[j] == "(":
                        pdepth += 1
                    elif summary_text[j] == ")":
                        pdepth -= 1
                    j += 1
                link_text = summary_text[start + 1 : i - 1]
                path = summary_text[i + 1 : j - 1]
                links.append((link_text.strip(), path.strip()))
                i = j
                continue
        i += 1
    return links


def collect_concept_files() -> set[Path]:
    """收集 concept/ 下应出现在 SUMMARY 中的 .md 文件（相对 concept/ 根目录）。"""
    files: set[Path] = set()
    for path in concept_config.iter_concept_files():
        rel = path.relative_to(concept_config.CONCEPT_DIR)
        name = rel.name
        parts = rel.parts
        # 排除 SUMMARY 自身
        if name == "SUMMARY.md":
            continue
        # 排除占位符、模板、审计清单等元文件（可手动审查，不要求出现在 SUMMARY）
        if any(p in {"placeholders"} for p in parts):
            continue
        if name in {"bilingual_template.md", "template_deduplication_guide.md", "audit_checklist.md"}:
            continue
        # 排除根级 README.md、PLAN.md 等非核心文件
        if name in {"README.md", "PLAN.md"} and len(parts) == 1:
            continue
        files.add(rel)
    return files


def main() -> int:
    if not SUMMARY_PATH.exists():
        print(f"❌ SUMMARY 文件不存在: {SUMMARY_PATH}")
        return 1

    summary_text = SUMMARY_PATH.read_text(encoding="utf-8")
    links = parse_summary_links(summary_text)

    linked_paths: set[Path] = set()
    missing_files: list[tuple[str, str]] = []
    for text, raw_path in links:
        # SUMMARY 中的路径相对于 concept/ 根目录
        if not raw_path.endswith(".md"):
            # 外部 URL、锚点等不参与 concept/ 文件一致性检查
            continue
        p = Path(raw_path)
        linked_paths.add(p)
        target = concept_config.CONCEPT_DIR / p
        if not target.exists():
            missing_files.append((text, raw_path))

    concept_files = collect_concept_files()
    unlinked_files = sorted(concept_files - linked_paths)

    # 主题子目录一致性检查
    theme_warnings: list[str] = []
    for rel in concept_files:
        parts = rel.parts
        if len(parts) < 2:
            continue
        layer_dir = parts[0]
        if layer_dir not in concept_config.THEME_SUBDIRS:
            continue
        # 如果文件不在推荐的主题子目录中（也不是 README.md），给出警告
        if len(parts) == 2:
            name = parts[1]
            if name != "README.md":
                theme_warnings.append(f"{rel}: 建议移入 {layer_dir}/<theme>/ 子目录")

    exit_code = 0
    print(f"SUMMARY 链接总数: {len(links)}")
    print(f"concept/ 有效文件总数: {len(concept_files)}")

    if missing_files:
        exit_code = 1
        print(f"\n❌ SUMMARY 中存在 {len(missing_files)} 个死链:")
        for text, raw_path in missing_files:
            print(f"  - [{text}]({raw_path})")

    if unlinked_files:
        exit_code = 1
        print(f"\n❌ 有 {len(unlinked_files)} 个 concept/ 文件未在 SUMMARY 中链接:")
        for p in unlinked_files:
            print(f"  - {p}")

    if theme_warnings:
        print(f"\n⚠️  主题子目录建议 ({len(theme_warnings)} 项，非阻塞):")
        for w in theme_warnings[:20]:
            print(f"  - {w}")
        if len(theme_warnings) > 20:
            print(f"  ... 还有 {len(theme_warnings) - 20} 项")

    if exit_code == 0:
        print("\n✅ SUMMARY 与实际文件一致")
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
