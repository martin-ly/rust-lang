#!/usr/bin/env python3
"""
修复 docs/02_reference/quick_reference/ 下速查卡文件的锚点问题。

主要问题：
1. 标题自定义锚点格式混乱，如 `## ⚙️ 配置文件 {#️-配置文件}`。
2. 目录中的链接指向重复或错误的锚点，如 `#️-配置文件-️-配置文件`。

处理策略：
- 读取每个 quick_reference 文件。
- 为每个标题计算规范的 GitHub 风格锚点（保留中文、移除 emoji/变体选择符/标点）。
- 规范化标题中的显式 `{#...}` 锚点。
- 识别目录（TOC）区域，更新其中的锚点链接，使其指向正确的锚点。
- 清理目录链接文本中混入的 `{#...}`。
- 保留中文内容与 emoji 标题文本。
"""

import re
import sys
from pathlib import Path
from collections import Counter

QUICK_REF_DIR = Path("docs/02_reference/quick_reference")

# 目录标题匹配：## 📋 目录 / ## 📑 目录 / ## 目录 等
TOC_HEADING_RE = re.compile(r"^##\s+.*目录\s*(\{#[^}]*\})?\s*$")

# Markdown 标题
HEADING_RE = re.compile(r"^(#{1,6})\s+(.+)$")

# 显式锚点
EXPLICIT_ANCHOR_RE = re.compile(r"\s*\{#[^}]+\}\s*$")

# Markdown 链接 [text](url)
LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")

# 分隔线
SEPARATOR_RE = re.compile(r"^---\s*$")


def normalize_anchor(text: str) -> str:
    """
    将标题文本转换为 GitHub 风格的锚点 ID。
    保留中文字符、ASCII 字母/数字/连字符；移除 emoji、变体选择符、标点。
    """
    # 移除显式锚点后缀
    text = EXPLICIT_ANCHOR_RE.sub("", text)
    # 移除首尾空白
    text = text.strip()
    # 转为小写
    text = text.lower()
    # 保留 \w（含 CJK）、空格、连字符；其余移除
    text = re.sub(r"[^\w\s-]", "", text, flags=re.UNICODE)
    # 空白序列替换为单个连字符
    text = re.sub(r"\s+", "-", text)
    # 移除首尾连字符
    text = text.strip("-")
    return text


def strip_explicit_anchor(text: str) -> str:
    """移除标题/链接文本末尾的显式锚点标记。"""
    return EXPLICIT_ANCHOR_RE.sub("", text).rstrip()


def unescape_markdown(text: str) -> str:
    """反转义 Markdown 转义字符（如 \\_, \\&, \\-）。"""
    return re.sub(r"\\(.)", r"\1", text)


def strip_inline_formatting(text: str) -> str:
    """移除加粗、斜体、行内代码等内联格式标记，用于文本匹配。"""
    # 移除行内代码
    text = re.sub(r"`+[^`]*`+", "", text)
    # 移除加粗/斜体标记（顺序处理）
    for marker in ("**", "*", "__", "_"):
        text = re.sub(re.escape(marker) + r"(.*?)" + re.escape(marker), r"\1", text)
    return text.strip()


def parse_headings(content: str):
    """
    解析文件中的所有 Markdown 标题。
    返回 [(level, raw_text, display_text, anchor), ...]
    """
    headings = []
    seen_anchors = Counter()
    for line in content.splitlines():
        m = HEADING_RE.match(line)
        if not m:
            continue
        level = len(m.group(1))
        raw_text = m.group(2).rstrip()
        display_text = strip_explicit_anchor(raw_text)
        base_anchor = normalize_anchor(raw_text)
        # 处理重复标题：GitHub 风格为第二次及以后追加 -1, -2, ...
        if base_anchor in seen_anchors:
            anchor = f"{base_anchor}-{seen_anchors[base_anchor]}"
        else:
            anchor = base_anchor
        seen_anchors[base_anchor] += 1
        headings.append((level, raw_text, display_text, anchor))
    return headings


def find_toc_region_lines(content: str):
    """
    定位第一个目录区域的起止行索引（半开区间 [start, end)）。
    目录从 `## ...目录` 开始，到下一个 `---` 分隔线或文件末尾结束。
    """
    lines = content.splitlines()
    start = None
    for i, line in enumerate(lines):
        if TOC_HEADING_RE.match(line):
            start = i
            break
    if start is None:
        return None

    # 默认到文件末尾；如果遇到 --- 分隔线则停止
    end = len(lines)
    for i in range(start + 1, len(lines)):
        if SEPARATOR_RE.match(lines[i]):
            end = i
            break
    return start, end


def compute_heading_map(headings):
    """
    建立 display_text -> anchor 的映射，并保留出现顺序用于处理重复标题。
    """
    display_to_anchors = {}
    display_order = {}
    for idx, (_, _, display_text, anchor) in enumerate(headings):
        display_to_anchors.setdefault(display_text, []).append(anchor)
        display_order.setdefault(display_text, []).append(idx)
    return display_to_anchors, display_order


def fix_file(path: Path, dry_run: bool = False):
    """修复单个文件，返回修改统计与未修复项。"""
    content = path.read_text(encoding="utf-8")
    original_lines = content.splitlines()
    headings = parse_headings(content)
    display_to_anchors, _ = compute_heading_map(headings)

    # 1. 为所有标题统一添加/规范化显式锚点
    heading_raw_to_anchor = {}
    for _, raw_text, display_text, anchor in headings:
        heading_raw_to_anchor[raw_text] = anchor

    new_lines = []
    changed_headings = 0
    for line in original_lines:
        m = HEADING_RE.match(line)
        if m:
            raw_text = m.group(2).rstrip()
            if raw_text in heading_raw_to_anchor:
                anchor = heading_raw_to_anchor[raw_text]
                display = strip_explicit_anchor(raw_text)
                explicit = EXPLICIT_ANCHOR_RE.search(raw_text)
                # 统一写成“标题文本 {#anchor}”，确保与目录链接对齐
                new_text = f"{display} {{#{anchor}}}"
                if not explicit or anchor != explicit.group(0).strip()[2:-1].strip():
                    changed_headings += 1
                new_lines.append(f"{m.group(1)} {new_text}")
                continue
        new_lines.append(line)

    # 2. 修复文件中所有同文件锚点链接（跳过代码块）
    fixed_links = 0
    unfixed_links = []
    top_anchor_updated = False

    in_code_block = False
    anchor_usage = Counter()
    # 为未匹配链接预清空计数（每个文件单独计数）

    for i, line in enumerate(new_lines):
        # 简单代码块边界检测（不考虑语言标识后的内容）
        stripped = line.strip()
        if stripped.startswith("```"):
            in_code_block = not in_code_block
            continue
        if in_code_block:
            continue

        def replace_link(match):
            nonlocal fixed_links
            text = match.group(1)
            url = match.group(2)
            if not url.startswith("#"):
                return match.group(0)
            stripped_text = strip_explicit_anchor(text).strip()
            # 构建宽松匹配键：反转义并移除内联格式
            match_key = strip_inline_formatting(unescape_markdown(stripped_text))
            target = None
            for display_text, anchors in display_to_anchors.items():
                clean_display = strip_inline_formatting(unescape_markdown(display_text))
                if clean_display == match_key:
                    idx = anchor_usage[match_key]
                    if idx < len(anchors):
                        target = anchors[idx]
                    else:
                        # 链接数超过标题数，回退到最后一个
                        target = anchors[-1]
                    anchor_usage[match_key] += 1
                    break
            if target:
                fixed_links += 1
                # 清理链接文本中的显式锚点，但保留原始格式标记
                clean_text = strip_explicit_anchor(text)
                return f"[{clean_text}](#{target})"
            else:
                unfixed_links.append((i + 1, text, url))
                return match.group(0)

        new_lines[i] = LINK_RE.sub(replace_link, line)

    # 3. 若文件顶部存在 <a id="...">，且对应标题有规范锚点，则同步更新
    if new_lines and new_lines[0].startswith("<a id="):
        first_heading = next((h for h in headings if h[0] == 1), None)
        if first_heading:
            _, _, _, anchor = first_heading
            new_lines[0] = f'<a id="{anchor}"></a>'
            top_anchor_updated = True

    new_content = "\n".join(new_lines)
    if new_content != content and not dry_run:
        path.write_text(new_content, encoding="utf-8")

    return {
        "changed_headings": changed_headings,
        "fixed_links": fixed_links,
        "unfixed_links": unfixed_links,
        "top_anchor_updated": top_anchor_updated,
        "modified": new_content != content,
    }


def main():
    dry_run = "--dry-run" in sys.argv

    md_files = sorted(QUICK_REF_DIR.glob("*.md"))
    print(f"发现 {len(md_files)} 个 Markdown 文件")
    if dry_run:
        print("(当前为预览模式，不会写入文件)\n")

    total_fixed = 0
    total_unfixed = []
    modified_files = []

    for path in md_files:
        stats = fix_file(path, dry_run=dry_run)
        if stats["modified"]:
            modified_files.append(path.name)
        total_fixed += stats["fixed_links"]
        total_unfixed.extend((path.name, line, text, url) for line, text, url in stats["unfixed_links"])
        if stats["modified"] or stats["unfixed_links"]:
            print(f"  {path.name}: 规范化标题 {stats['changed_headings']} 个, 修复链接 {stats['fixed_links']} 个, 未修复 {len(stats['unfixed_links'])} 个")

    print(f"\n总计: 修改文件 {len(modified_files)} 个, 修复链接 {total_fixed} 个, 未修复 {len(total_unfixed)} 个")

    if total_unfixed:
        print("\n未修复的目录项（无对应标题）:")
        for fname, line, text, url in total_unfixed:
            print(f"  {fname}:{line} [{text}]({url})")

    if modified_files:
        print(f"\n修改的文件列表:")
        for name in modified_files:
            print(f"  - {name}")


if __name__ == "__main__":
    main()
