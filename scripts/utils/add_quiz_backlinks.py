#!/usr/bin/env python3
"""add_quiz_backlinks.py — concept→quiz 回链批量补链（W3-b，幂等）

对 quiz_registry.yaml 中每个独立 quiz 的 concept_pages：
若权威页尚未链接到该 quiz，则在其「相关概念」节插入回链行：

    - [对应测验](相对路径) — 主题

若无「相关概念」节，则在文件末尾新建该节。执行后运行
`python scripts/update_quiz_registry.py` 重算回链状态。

用法：
  python scripts/utils/add_quiz_backlinks.py [--dry-run]
"""
from __future__ import annotations

import argparse
import os
import pathlib
import re
import sys

import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent.parent
REGISTRY = ROOT / "concept" / "00_meta" / "quiz_registry.yaml"
SECTION_HEAD = re.compile(r"^## .*相关概念.*$", re.M)


def insert_backlink(page: pathlib.Path, quiz: pathlib.Path, topic: str) -> bool:
    """在 page 中插入指向 quiz 的回链行。已存在则跳过。返回是否修改。"""
    text = page.read_text(encoding="utf-8")
    href = pathlib.PureWindowsPath(os.path.relpath(quiz, page.parent)).as_posix()
    line = f"- [对应测验]({href}) — {topic}\n"
    if quiz.name in text:
        # 已存在但含反斜杠（Windows relpath 遗留）则规范化为正斜杠
        fixed = re.sub(r"\]\(([^)]*\\[^)]*)\)", lambda m: "](" + m.group(1).replace("\\", "/") + ")", text)
        if fixed != text:
            page.write_text(fixed, encoding="utf-8")
            return True
        return False
    m = SECTION_HEAD.search(text)
    if m:
        # 插入到节标题之后（跳过紧随的空行，保持标题后空行 + 列表）
        pos = m.end()
        rest = text[pos:]
        if rest.startswith("\n\n"):
            new_text = text[: pos + 2] + line + text[pos + 2:]
        else:
            new_text = text[:pos] + "\n\n" + line + text[pos:]
    else:
        new_text = text.rstrip("\n") + f"\n\n---\n\n## 相关概念\n\n{line}"
    page.write_text(new_text, encoding="utf-8")
    return True


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    registry = yaml.safe_load(REGISTRY.read_text(encoding="utf-8"))
    inserted, skipped = 0, 0
    for q in registry.get("standalone_quizzes", []):
        quiz = ROOT / q["path"]
        if not quiz.exists():
            print(f"! quiz missing: {q['path']}", file=sys.stderr)
            continue
        topic = q.get("topic", "")
        for cp in q.get("concept_pages", []):
            page = ROOT / cp
            if not page.exists():
                print(f"! concept page missing: {cp}", file=sys.stderr)
                continue
            if args.dry_run:
                text = page.read_text(encoding="utf-8")
                if quiz.name not in text or "\\" in text:
                    print(f"DRY {cp}  <-  {q['path']}")
                    inserted += 1
                else:
                    skipped += 1
                continue
            if insert_backlink(page, quiz, topic):
                print(f"+ {cp}  <-  {quiz.name}")
                inserted += 1
            else:
                skipped += 1
    print(f"inserted: {inserted}  skipped(exists): {skipped}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
