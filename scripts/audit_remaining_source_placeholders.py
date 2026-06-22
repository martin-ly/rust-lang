#!/usr/bin/env python3
"""审计全仓库 Markdown 中仍未链接化的来源占位符。

输出：按出现频次排序的未映射标签，以及涉及文件数。
"""

import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TARGET_DIRS = [Path("docs"), Path("book"), Path("guides"), Path("reports"), Path(".kimi"), Path("exercises"), Path("examples"), Path("content"), Path("concept"), Path("knowledge")]

# 简单跳过 fenced code block；不处理内嵌反引号外的内容。
FENCED_RE = re.compile(r"```[\s\S]*?```")
LINK_RE = re.compile(r"\]\([^)]+\)")


def find_unmapped(text: str):
    """返回未映射来源占位符的列表（仅文本，不含代码块）。"""
    results = []
    # 保护 fenced block
    segments = FENCED_RE.split(text)
    for i, seg in enumerate(segments):
        if i % 2 == 1:
            continue
        # 处理 bracketed 来源占位符，允许一层嵌套括号
        idx = 0
        while True:
            m = re.search(r"\[来源[：:]\s*", seg[idx:])
            if not m:
                break
            start = idx + m.start()
            inner_start = idx + m.end()
            # 查找匹配的 ]，允许一层嵌套 [ ... ]
            depth = 0
            pos = inner_start
            found = False
            while pos < len(seg):
                ch = seg[pos]
                if ch == "[":
                    depth += 1
                elif ch == "]":
                    if depth == 0:
                        found = True
                        break
                    depth -= 1
                pos += 1
            if not found:
                break
            content = seg[inner_start:pos]
            whole = seg[start : pos + 1]
            # 如果内容里已经有 ]( 链接，视为已映射
            if not LINK_RE.search(whole):
                # 去掉首尾可能的 [ ]
                label = content.strip()
                while label.startswith("[") and label.endswith("]"):
                    label = label[1:-1].strip()
                if label:
                    results.append(label)
            idx = pos + 1

        # 处理无括号前缀的 "来源: ..."
        for m in re.finditer(r"(?<!\[)来源[：:]\s*([^\n\[\]]+?)(?=\s*$|\s+[,，;；]|\s*\|)", seg):
            label = m.group(1).strip()
            # 忽略已经是链接的
            if "](" not in label and label:
                results.append(label)
    return results


def main():
    counter = Counter()
    file_hits = Counter()
    for root in TARGET_DIRS:
        full_root = ROOT / root
        if not full_root.exists():
            continue
        for p in sorted(full_root.rglob("*.md")):
            if "archive" in p.parts or "node_modules" in p.parts:
                continue
            try:
                text = p.read_text(encoding="utf-8", errors="ignore")
            except Exception:
                continue
            labels = find_unmapped(text)
            if labels:
                file_hits[str(p.relative_to(ROOT))] += len(labels)
                counter.update(labels)

    print(f"未映射来源标签种类: {len(counter)}")
    print(f"未映射来源标签总数: {sum(counter.values())}")
    print(f"涉及文件数: {len(file_hits)}")
    print()
    print("| 频次 | 标签 |")
    print("|---:|:---|")
    for label, cnt in counter.most_common(100):
        print(f"| {cnt} | {label} |")

    print("\n涉及文件（前 30，按命中数）:")
    for path, cnt in file_hits.most_common(30):
        print(f"  {cnt:4d}  {path}")


if __name__ == "__main__":
    main()
