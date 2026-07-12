#!/usr/bin/env python3
"""refresh_quiz_registry.py — 从文件实测刷新 quiz_registry.yaml（W3-b，幂等）

从磁盘实测并回填注册表字段：
  - 每个 standalone quiz：questions / meta_questions / question_types / difficulty
    （解析规则与 scripts/check_quiz_system.py 一致），以及 quiz_to_concept /
    concept_to_quiz_backlink 双向链接布尔；
  - embedded_quizzes.pages / total_blocks 聚合统计（concept/ 下非独立 quiz 页面中
    `### 测验 N` 块计数）。

保留 topic / concept_pages / layer 等人工维护字段与条目顺序。

用法：
    python scripts/refresh_quiz_registry.py [--dry-run]
"""
from __future__ import annotations

import argparse
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
REGISTRY = ROOT / "concept" / "00_meta" / "quiz_registry.yaml"

Q_HEAD = re.compile(r"^### (Q\d+|问题 \d+)[.：:]\s*(.*)$", re.M)
META_HEAD = re.compile(r"^### 测验\s*\d+", re.M)
EMOJI = {"🟢": "basic", "🟡": "intermediate", "🔴": "expert"}


def question_blocks(text: str):
    matches = list(Q_HEAD.finditer(text))
    for i, m in enumerate(matches):
        end = matches[i + 1].start() if i + 1 < len(matches) else len(text)
        yield m.group(2), text[m.start():end]


def classify(rest: str, body: str) -> str:
    if "【单选】" in rest:
        return "single_choice"
    if "【多选】" in rest:
        return "multiple_choice"
    if "【判断】" in rest:
        return "true_false"
    if re.search(r"^- A\.", body, re.M):
        return "single_choice"
    return "code_reading"


def analyze_quiz(path: pathlib.Path):
    text = path.read_text(encoding="utf-8")
    types, diff, n = set(), {k: 0 for k in EMOJI.values()}, 0
    for rest, body in question_blocks(text):
        n += 1
        types.add(classify(rest, body))
        for emoji, key in EMOJI.items():
            if rest.startswith(emoji):
                diff[key] += 1
                break
    meta = len(META_HEAD.findall(text))
    return {"questions": n, "meta": meta, "types": sorted(types), "diff": diff}


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
    ap.add_argument("--dry-run", action="store_true", help="只打印差异，不写回")
    args = ap.parse_args()

    try:
        import yaml
    except ImportError:
        print("ERROR: 需要 PyYAML（pip install pyyaml）", file=sys.stderr)
        return 2

    registry = yaml.safe_load(REGISTRY.read_text(encoding="utf-8"))
    changes = []

    for q in registry.get("standalone_quizzes", []):
        path = ROOT / q["path"]
        if not path.exists():
            print(f"  MISS {q['path']}")
            continue
        a = analyze_quiz(path)
        qtext = path.read_text(encoding="utf-8")
        cps = [ROOT / cp for cp in q.get("concept_pages", [])]
        new_vals = {
            "questions": a["questions"],
            "meta_questions": a["meta"],
            "question_types": a["types"],
            "difficulty": a["diff"],
            "quiz_to_concept": any(cp.exists() and has_link_to(qtext, path, cp) for cp in cps),
            "concept_to_quiz_backlink": any(
                cp.exists() and has_link_to(cp.read_text(encoding="utf-8"), cp, path) for cp in cps
            ),
        }
        for k, v in new_vals.items():
            if q.get(k) != v:
                changes.append(f"{q['path']}: {k} {q.get(k)} -> {v}")
                q[k] = v

    quiz_set = {q["path"] for q in registry.get("standalone_quizzes", [])}
    pages, blocks, items = 0, 0, []
    for p in sorted((ROOT / "concept").rglob("*.md")):
        rel = p.relative_to(ROOT).as_posix()
        if rel in quiz_set:
            continue
        n = len(META_HEAD.findall(p.read_text(encoding="utf-8", errors="replace")))
        if n:
            pages += 1
            blocks += n
            items.append({"path": rel, "blocks": n})
    emb = registry.setdefault("embedded_quizzes", {})
    if emb.get("pages") != pages or emb.get("total_blocks") != blocks:
        changes.append(f"embedded_quizzes: {emb.get('pages')}页/{emb.get('total_blocks')}块 -> {pages}页/{blocks}块")
        emb["pages"] = pages
        emb["total_blocks"] = blocks
    if emb.get("items") != items:
        old_n = len(emb.get("items") or [])
        changes.append(f"embedded_quizzes.items: {old_n} 条 -> {len(items)} 条")
        emb["items"] = items

    print(f"== 刷新结果 ==  变更 {len(changes)} 项")
    for c in changes:
        print(f"  {c}")
    if changes and not args.dry_run:
        REGISTRY.write_text(
            yaml.dump(registry, allow_unicode=True, sort_keys=False, width=120),
            encoding="utf-8",
        )
        print(f"已写回 {REGISTRY.relative_to(ROOT)}")
    elif changes:
        print("（dry-run；去掉 --dry-run 写回）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
