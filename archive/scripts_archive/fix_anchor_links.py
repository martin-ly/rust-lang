#!/usr/bin/env python3
"""
为 docs 目录下的 Markdown 文件批量添加显式锚点，修复「同文件锚点不存在」类损坏链接。

用法: python scripts/fix_anchor_links.py [--dry-run]
"""
import re
import os
import sys
import argparse
from pathlib import Path
from collections import defaultdict

# 项目根目录
PROJECT_ROOT = Path(__file__).resolve().parent.parent
REPORT_PATH = PROJECT_ROOT / "docs" / "LINK_CHECK_REPORT.md"
DOCS_ROOT = PROJECT_ROOT / "docs"


def parse_report(report_path: Path) -> list[tuple[str, str, str]]:
    """
    解析 LINK_CHECK_REPORT.md，提取「同文件锚点不存在」的 (源文件, 锚点id, 链接文本)。
    返回去重后的列表（同一文件同一锚点只保留一次）。
    """
    content = report_path.read_text(encoding="utf-8")
    entries = []

    # 找到「锚点不存在」表格，解析到下一个 ### 或 ## 为止
    in_table = False
    for line in content.splitlines():
        stripped = line.strip()
        if stripped.startswith("### ") and "锚点不存在" in stripped:
            in_table = True
            continue
        if in_table:
            if stripped.startswith("### ") or (stripped.startswith("## ") and "锚点不存在" not in stripped):
                break
            if stripped.startswith("|") and "|" in stripped[1:]:
                parts = [p.strip() for p in stripped.split("|")[1:-1]]
                if len(parts) >= 4:
                    source, link_text, link_path, problem = parts[0], parts[1], parts[2], parts[3]
                    if "同文件锚点不存在" not in problem:
                        continue
                    # 提取锚点：链接路径格式为 `#xxx` 或 `#锚点`
                    match = re.search(r"`(#([^`]+))`", link_path)
                    if not match:
                        match = re.search(r"#([^#\s]+)", link_path)
                    if match:
                        anchor = match.group(2) if match.lastindex >= 2 else match.group(1)
                        # 锚点 id：去掉开头的 #
                        if anchor.startswith("#"):
                            anchor = anchor[1:]
                        # 规范化路径：反斜杠转正斜杠
                        source_norm = source.replace("\\", "/")
                        if not source_norm.startswith("docs/"):
                            source_norm = "docs/" + source_norm.lstrip("/")
                        entries.append((source_norm, anchor, link_text))

    # 去重：(文件, 锚点) 唯一
    seen = set()
    unique = []
    for src, anchor, text in entries:
        key = (src, anchor)
        if key not in seen:
            seen.add(key)
            unique.append((src, anchor, text))
    return unique


def normalize_title_for_match(title: str) -> str:
    """规范化标题文本用于匹配（去除泛型等）"""
    t = title.strip()
    t = re.sub(r"<[^>]+>", "", t)  # 移除 <T> 等
    t = re.sub(r"\s+", " ", t)
    return t.strip()


def find_title_line_index(
    lines: list[str], link_text: str, anchor: str, existing_anchors: dict[str, int]
) -> int | None:
    """
    在文件中查找应添加锚点的标题行索引。
    - link_text: 链接显示的文本
    - anchor: 目标锚点 id（如 -目录、212-vec、排序算法-1）
    - existing_anchors: 已有 {#id} 的锚点 -> 行号，用于去重
    """
    # 解析重复后缀：排序算法-1 表示第 2 个「排序算法」
    occurrence = 1
    base_anchor = anchor
    if re.match(r".+-\d+$", anchor):
        m = re.match(r"(.+)-(\d+)$", anchor)
        if m:
            base_anchor = m.group(1)
            occurrence = int(m.group(2)) + 1  # -1 -> 第2次, -2 -> 第3次

    # 规范化链接文本用于匹配
    link_norm = normalize_title_for_match(link_text)
    if not link_norm:
        link_norm = base_anchor.replace("-", " ")

    candidates = []
    for i, line in enumerate(lines):
        m = re.match(r"^(#{1,6})\s+(.+?)(?:\s*\{#([^}]+)\})?\s*$", line)
        if not m:
            continue
        level, title_content, explicit_anchor = m.group(1), m.group(2), m.group(3)
        title_norm = normalize_title_for_match(title_content)

        # 检查是否已有所需锚点
        if explicit_anchor == anchor:
            return None  # 已有，无需添加

        # 匹配：链接文本应包含在标题中，或标题包含链接文本，或通过 base_anchor 反推
        if link_norm in title_norm or title_norm in link_norm:
            candidates.append((i, title_content, explicit_anchor))
            continue
        # 反推：anchor 如 "212-vec" 可能对应 "2.1.2 Vec"
        anchor_as_title = base_anchor.replace("-", " ").replace("_", " ")
        if anchor_as_title in title_norm or title_norm in anchor_as_title:
            candidates.append((i, title_content, explicit_anchor))
            continue
        # 更宽松：标题去掉 emoji 后与链接文本相似
        title_no_emoji = re.sub(r"[\u2600-\u27BF\U0001F300-\U0001F9FF]", "", title_norm)
        if link_norm in title_no_emoji or title_no_emoji in link_norm:
            candidates.append((i, title_content, explicit_anchor))

    if not candidates:
        return None

    # 若 occurrence > 1，取第 occurrence 个匹配
    if occurrence > 1 and len(candidates) >= occurrence:
        return candidates[occurrence - 1][0]
    return candidates[0][0]


def add_anchor_to_file(file_path: Path, anchor: str, link_text: str, dry_run: bool) -> bool:
    """
    在指定文件的对应标题行末尾添加 {#anchor}。
    返回是否进行了修改。
    """
    try:
        content = file_path.read_text(encoding="utf-8")
    except Exception as e:
        print(f"  [跳过] 无法读取: {e}", file=sys.stderr)
        return False

    lines = content.splitlines()
    existing = {}
    for i, line in enumerate(lines):
        m = re.search(r"\{#([^}]+)\}", line)
        if m:
            existing[m.group(1)] = i

    idx = find_title_line_index(lines, link_text, anchor, existing)
    if idx is None:
        return False

    line = lines[idx]
    if re.search(r"\{#" + re.escape(anchor) + r"\}", line):
        return False

    # 若已有其他 {#...}，替换为包含新锚点的（理论上不应出现，因上面已检查）
    if re.search(r"\{#[^}]+\}\s*$", line):
        # 已有锚点且不是目标锚点，跳过（可能是不同锚点）
        return False

    new_line = line.rstrip()
    if not new_line.endswith("}"):
        new_line = new_line + " {#" + anchor + "}"
    else:
        return False

    if not dry_run:
        lines[idx] = new_line
        file_path.write_text("\n".join(lines) + ("\n" if content.endswith("\n") else ""), encoding="utf-8")
    return True


def main():
    parser = argparse.ArgumentParser(description="修复同文件锚点不存在")
    parser.add_argument("--dry-run", action="store_true", help="仅预览，不写入文件")
    args = parser.parse_args()

    if not REPORT_PATH.exists():
        print(f"错误: 报告文件不存在 {REPORT_PATH}", file=sys.stderr)
        sys.exit(1)

    entries = parse_report(REPORT_PATH)
    # 过滤：只处理 docs 下非 archive 的文件
    entries = [(src, anchor, text) for src, anchor, text in entries if "archive" not in src]

    # 按文件分组
    by_file: dict[str, list[tuple[str, str]]] = defaultdict(list)
    for src, anchor, text in entries:
        by_file[src].append((anchor, text))

    fixed_files = []
    total_fixes = 0

    for rel_path, items in sorted(by_file.items()):
        full_path = PROJECT_ROOT / rel_path
        if not full_path.exists():
            print(f"  [跳过] 文件不存在: {rel_path}", file=sys.stderr)
            continue

        file_fixes = 0
        for anchor, link_text in items:
            if add_anchor_to_file(full_path, anchor, link_text, dry_run=args.dry_run):
                file_fixes += 1
                total_fixes += 1

        if file_fixes > 0:
            fixed_files.append((rel_path, file_fixes))

    # 输出结果
    mode = "[dry-run] " if args.dry_run else ""
    print(f"\n{mode}修复完成:")
    print(f"  修复文件数: {len(fixed_files)}")
    print(f"  添加锚点数: {total_fixes}")
    if fixed_files:
        print("\n修复的文件列表:")
        for path, count in sorted(fixed_files, key=lambda x: -x[1]):
            print(f"  - {path} ({count} 个锚点)")

    return 0


if __name__ == "__main__":
    sys.exit(main())
