#!/usr/bin/env python3
"""修复 concept/ 文件的 EN/Summary 占位符，使用文件 stem 生成规范英文名。

v2 策略：
- 若当前 EN 已包含有效英文（无中文字符且无 (Chinese) 标记），跳过。
- 否则优先从标题括号中提取英文；否则使用文件 stem 生成 Title Case 英文名。
- Summary 同步为英文短句。
"""

import re
from pathlib import Path

CONCEPT_DIR = Path("concept")


def title_case_stem(stem: str) -> str:
    """将 `01_ownership_inventories_brown_book` 转为 `Ownership Inventories Brown Book`。"""
    # 去掉数字前缀，如 01_ownership -> ownership
    stem = re.sub(r'^\d+_', '', stem)
    # 将下划线替换为空格并 Title Case
    return ' '.join(word.capitalize() for word in stem.split('_'))


def extract_existing_english(title: str) -> str:
    m = re.search(r'[（(]([A-Za-z][A-Za-z0-9\s/_!\-]*)[）)]', title)
    if m:
        return m.group(1).strip()
    return ""


def is_placeholder_en(line: str) -> bool:
    if not line:
        return True
    if "(Chinese)" in line:
        return True
    # 若包含中文字符，视为占位
    if any('\u4e00' <= c <= '\u9fff' for c in line):
        return True
    return False


def update_file(path: Path) -> bool:
    text = path.read_text(encoding="utf-8")
    rel = path.relative_to(CONCEPT_DIR)

    title_match = re.search(r'^#\s+(.+)$', text, re.MULTILINE)
    title = title_match.group(1).strip() if title_match else ""

    en_match = re.search(r'(?m)^>\s+\*\*EN\*\*:\s*(.+)$', text)
    summary_match = re.search(r'(?m)^>\s+\*\*Summary\*\*:\s*(.+)$', text)

    # 决定英文标题
    en_title = ""
    if not en_match or is_placeholder_en(en_match.group(1)):
        en_title = extract_existing_english(title)
        if not en_title:
            en_title = title_case_stem(path.stem)

    if not en_title:
        return False

    changed = False

    if en_match:
        old = en_match.group(1).strip()
        if is_placeholder_en(old):
            text = text[:en_match.start()] + f"> **EN**: {en_title}" + text[en_match.end():]
            changed = True
    elif title_match:
        insert_pos = title_match.end()
        text = text[:insert_pos] + f"\n>\n> **EN**: {en_title}" + text[insert_pos:]
        changed = True
    else:
        # 无标题时直接在文件开头插入
        text = f"> **EN**: {en_title}\n\n" + text
        changed = True

    # 同步 Summary
    new_summary = f"{en_title}. Core Rust concept."
    if summary_match:
        old_summary = summary_match.group(1).strip()
        if is_placeholder_en(old_summary):
            text = text[:summary_match.start()] + f"> **Summary**: {new_summary}" + text[summary_match.end():]
            changed = True
    else:
        # 在 EN 后插入 Summary
        en_match2 = re.search(r'(?m)^>\s+\*\*EN\*\*:.+$', text)
        if en_match2:
            insert_pos = en_match2.end()
            text = text[:insert_pos] + f"\n> **Summary**: {new_summary}" + text[insert_pos:]
            changed = True

    if changed:
        path.write_text(text, encoding="utf-8")
    return changed


def main():
    files = sorted(CONCEPT_DIR.rglob("*.md"))
    updated = 0
    for f in files:
        if update_file(f):
            updated += 1
            print(f"{f.relative_to(CONCEPT_DIR)}")
    print(f"\n共更新 {updated} 个文件")


if __name__ == "__main__":
    main()
