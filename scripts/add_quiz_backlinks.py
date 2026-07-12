#!/usr/bin/env python3
"""add_quiz_backlinks.py — concept 权威页 → 独立 quiz 回链批量补全（W3-b，幂等）

对 concept/00_meta/quiz_registry.yaml 中每个 standalone quiz 的 concept_pages：
若该 concept 页未链接到 quiz，则在其「相关概念」节（`## ...相关概念...`）标题后
插入一条 `- [对应测验](<相对路径>) — <topic>`；若无相关概念节，则在文末追加一个。

幂等：已存在链接的页面跳过。默认 dry-run，--apply 执行写入。

用法：
    python scripts/add_quiz_backlinks.py [--apply] [--verbose]
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "concept" / "00_meta" / "quiz_registry.yaml"
RELATED_RE = re.compile(r"^## .*相关概念.*$", re.M)


def has_link_to(src_text: str, src_path: pathlib.Path, target: pathlib.Path) -> bool:
    for m in re.finditer(r"\[[^\]]*\]\(([^)]+\.md)\)", src_text):
        href = m.group(1).split("#")[0]
        if href.startswith("http"):
            continue
        try:
            if (src_path.parent / href).resolve() == target.resolve():
                return True
        except OSError:
            continue
    return False


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--apply", action="store_true", help="实际写入（默认 dry-run）")
    ap.add_argument("--verbose", "-v", action="store_true")
    args = ap.parse_args()

    try:
        import yaml
    except ImportError:
        print("ERROR: 需要 PyYAML（pip install pyyaml）", file=sys.stderr)
        return 2

    registry = yaml.safe_load(REGISTRY.read_text(encoding="utf-8"))
    added, skipped, missing = 0, 0, []

    for q in registry.get("standalone_quizzes", []):
        quiz_path = ROOT / q["path"]
        topic = q.get("topic", quiz_path.stem)
        if not quiz_path.exists():
            missing.append(q["path"])
            continue
        for cp in q.get("concept_pages", []):
            cp_path = ROOT / cp
            if not cp_path.exists():
                missing.append(cp)
                continue
            text = cp_path.read_text(encoding="utf-8")
            if has_link_to(text, cp_path, quiz_path):
                skipped += 1
                continue
            import os
            rel = pathlib.PurePath(os.path.relpath(quiz_path, cp_path.parent)).as_posix()
            bullet = f"- [对应测验]({rel}) — {topic}\n"
            m = RELATED_RE.search(text)
            if m:
                insert_at = m.end()
                new_text = text[:insert_at] + "\n\n" + bullet.rstrip("\n") + text[insert_at:]
            else:
                new_text = text.rstrip("\n") + "\n\n---\n\n## 相关概念\n\n" + bullet
            if args.apply:
                cp_path.write_text(new_text, encoding="utf-8")
            added += 1
            print(f"  {'ADD ' if args.apply else 'PLAN'} {cp} -> {q['path']}")

    print(f"== 汇总 ==  新增回链: {added}  已存在跳过: {skipped}  缺失文件: {len(missing)}")
    for p in missing:
        print(f"  MISS {p}")
    if not args.apply and added:
        print("（dry-run；加 --apply 执行写入）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
