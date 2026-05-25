#!/usr/bin/env python3
"""
清理主标题、目录项 text/anchor 中的 [来源: ...] 嵌入污染。

处理模式：
  1. 主标题（# 开头）中的 [来源: [Name](URL)] → 删除
  2. 目录项（- [text](anchor)）中的 [来源: Name] → 删除
  3. 目录项 anchor 中的 -来源-name → 删除
"""

import re
from pathlib import Path

# 匹配 [来源: [Name](URL)]
RE_CITATION_LINK = re.compile(r"\[来源:\s*\[.*?\]\(.*?\)\]")
# 匹配 [来源: Name]（无 URL）
RE_CITATION_PLAIN = re.compile(r"\[来源:\s*[^\]]+\]")
# 匹配目录项中的转义 \[来源: Name\]
RE_CITATION_ESCAPED = re.compile(
    re.escape("\\[") + r"来源:\s*[^\]]+" + re.escape("\\]")
)
# anchor 中的 -来源-xxx 段
RE_ANCHOR_SOURCE = re.compile(r"-来源-[^\)#\s]+(?=[\)#\s]|$)")
# 清理后可能出现的连续空格
RE_MULTI_SPACE = re.compile(r"  +")


def clean_citations_from_text(text):
    """从文本中移除所有 [来源: ...] 嵌入，保留换行符"""
    # 分离换行符
    newline = ""
    if text.endswith("\r\n"):
        newline = "\r\n"
        text = text[:-2]
    elif text.endswith("\n"):
        newline = "\n"
        text = text[:-1]
    elif text.endswith("\r"):
        newline = "\r"
        text = text[:-1]

    text = RE_CITATION_LINK.sub("", text)
    text = RE_CITATION_PLAIN.sub("", text)
    text = RE_CITATION_ESCAPED.sub("", text)
    text = RE_MULTI_SPACE.sub(" ", text)
    # 清理中文和标点间多余的空格
    text = text.replace("( ", "(").replace(" )", ")")
    text = text.replace("[ ", "[").replace(" ]", "]")
    text = text.strip()

    return text + newline


def clean_anchor(anchor):
    """清理 anchor 中的 -来源-xxx 段，并规范化连字符"""
    anchor = RE_ANCHOR_SOURCE.sub("", anchor)
    anchor = re.sub(r"-+", "-", anchor)
    anchor = anchor.strip("-#")
    return anchor


def process_file(filepath):
    with open(filepath, "r", encoding="utf-8") as f:
        lines = f.readlines()

    modified = False
    new_lines = []

    for line in lines:
        original = line

        # 模式 1: 主标题行 (# 开头)
        if line.strip().startswith("# ") and "[来源:" in line:
            line = clean_citations_from_text(line)
            modified = True

        # 模式 2: 目录项 (- [text](anchor)) 中的 [来源: ...]
        if line.strip().startswith("- [") and "[来源:" in line:
            line = clean_citations_from_text(line)
            # 再清理 anchor 中的 -来源-xxx
            if "-来源-" in line:
                line = clean_anchor(line)
            modified = True

        # 模式 3: 目录项 anchor 中单独的 -来源-xxx
        elif line.strip().startswith("- [") and "-来源-" in line:
            line = clean_anchor(line)
            modified = True

        new_lines.append(line)

    if modified:
        with open(filepath, "w", encoding="utf-8") as f:
            f.writelines(new_lines)
        print(f"  已清理: {filepath}")
        return True
    return False


def main():
    target_dir = Path("concept")
    files = sorted(target_dir.rglob("*.md"))

    cleaned_count = 0
    for filepath in files:
        parts = [p.lower() for p in str(filepath.relative_to(target_dir)).replace("\\", "/").split("/")]
        if "archive" in parts:
            continue
        if process_file(filepath):
            cleaned_count += 1

    print(f"\n共清理 {cleaned_count} 个文件")


if __name__ == "__main__":
    main()
