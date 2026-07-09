#!/usr/bin/env python3
"""找出 concept/ 中未被 SUMMARY.md 链接的 .md 文件。"""

import re
from pathlib import Path

ROOT = Path("e:/_src/rust-lang")
CONCEPT_DIR = ROOT / "concept"
SUMMARY = CONCEPT_DIR / "SUMMARY.md"

# 读取 SUMMARY.md 中的所有链接
def extract_links(text: str) -> set[str]:
    # Markdown 链接: [title](path)
    pattern = re.compile(r"\]\(([^)]+)\)")
    links = set()
    for match in pattern.finditer(text):
        link = match.group(1).split("#")[0].strip()  # 去掉锚点
        if link and not link.startswith(("http://", "https://", "mailto:")):
            links.add(link)
    return links


summary_text = SUMMARY.read_text(encoding="utf-8")
summary_links = extract_links(summary_text)

# 收集所有 concept/ 下的 .md 文件（排除 archive/ 和 placeholders/，可调整）
all_md_files = set()
for path in CONCEPT_DIR.rglob("*.md"):
    rel = path.relative_to(CONCEPT_DIR).as_posix()
    if rel == "SUMMARY.md":
        continue
    all_md_files.add(rel)

# 计算未链接文件
unlinked = sorted(all_md_files - summary_links)

print(f"SUMMARY.md 中链接的 concept/ 文件数: {len(summary_links & all_md_files)}")
print(f"concept/ 中总 .md 文件数: {len(all_md_files)}")
print(f"未在 SUMMARY.md 中链接的文件数: {len(unlinked)}")
print()
print("未链接文件列表:")
for f in unlinked:
    print(f"  - {f}")
