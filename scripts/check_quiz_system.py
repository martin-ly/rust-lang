#!/usr/bin/env python3
"""check_quiz_system.py — 测验体系一致性检查器（W3-a 观察门）

检查项：
  1. 注册表一致性：concept/00_meta/quiz_registry.yaml 中 15 个独立 quiz 的
     path / questions / meta_questions / 难度分布 与实际文件一致；
     embedded_quizzes 聚合统计（页数/块数）与实际一致。
  2. 题型多样性：每个独立 quiz ≥3 种题型（代码阅读/单选/多选/判断）。
  3. 难度标注率：独立 quiz 每道题必须带 🟢/🟡/🔴 标注（目标 100%）。
  4. 双向链接率：quiz→concept（前置/解析链接）与 concept→quiz（回链）。
     回链缺失仅统计报告（W3-b 批量补链），默认不视为失败。

默认观察模式 exit 0；--strict 时检查 1-3 失败即 exit 1（回链缺失不计入阻断）。

用法：
  python scripts/check_quiz_system.py [--strict] [--verbose]
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
EMBED_HEAD = re.compile(r"^### 测验\s*\d+", re.M)
EMOJI = {"🟢": "basic", "🟡": "intermediate", "🔴": "expert"}


def question_blocks(text: str):
    """Yield (heading_rest, body) per question heading."""
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
    types, diff, annotated, n = set(), {k: 0 for k in EMOJI.values()}, 0, 0
    for rest, body in question_blocks(text):
        n += 1
        types.add(classify(rest, body))
        for emoji, key in EMOJI.items():
            if rest.startswith(emoji):
                diff[key] += 1
                annotated += 1
                break
    meta = len(META_HEAD.findall(text))
    return {"questions": n, "meta": meta, "types": types, "diff": diff, "annotated": annotated}


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
    ap.add_argument("--strict", action="store_true", help="检查 1-3 失败时 exit 1")
    ap.add_argument("--verbose", "-v", action="store_true")
    args = ap.parse_args()

    try:
        import yaml
    except ImportError:
        print("ERROR: 需要 PyYAML（pip install pyyaml）", file=sys.stderr)
        return 2

    registry = yaml.safe_load(REGISTRY.read_text(encoding="utf-8"))
    failures, warnings = [], []

    # ---- 检查 1：注册表一致性 ----
    print("== 检查 1：注册表一致性 ==")
    quizzes = registry.get("standalone_quizzes", [])
    for q in quizzes:
        path = ROOT / q["path"]
        if not path.exists():
            failures.append(f"[registry] 文件不存在: {q['path']}")
            continue
        a = analyze_quiz(path)
        if a["questions"] != q["questions"]:
            failures.append(
                f"[registry] {q['path']}: 题数不符 registry={q['questions']} actual={a['questions']}"
            )
        if a["meta"] != q.get("meta_questions", 0):
            failures.append(
                f"[registry] {q['path']}: 元测验数不符 registry={q.get('meta_questions')} actual={a['meta']}"
            )
        if a["diff"] != q.get("difficulty", {}):
            failures.append(
                f"[registry] {q['path']}: 难度分布不符 registry={q.get('difficulty')} actual={a['diff']}"
            )
        if sorted(a["types"]) != sorted(q.get("question_types", [])):
            failures.append(
                f"[registry] {q['path']}: 题型构成不符 registry={q.get('question_types')} actual={sorted(a['types'])}"
            )
        if args.verbose:
            print(f"  OK {q['path']}: {a['questions']} 题, types={sorted(a['types'])}, diff={a['diff']}")
    print(f"  独立 quiz: {len(quizzes)} 个")

    emb = registry.get("embedded_quizzes", {})
    actual_pages, actual_blocks = [], 0
    quiz_set = {q["path"] for q in quizzes}
    for p in sorted((ROOT / "concept").rglob("*.md")):
        rel = p.as_posix().split("rust-lang/", 1)[-1]
        if rel in quiz_set:
            continue
        n = len(EMBED_HEAD.findall(p.read_text(encoding="utf-8", errors="replace")))
        if n:
            actual_pages.append(rel)
            actual_blocks += n
    if emb.get("pages") != len(actual_pages) or emb.get("total_blocks") != actual_blocks:
        failures.append(
            f"[registry] 嵌入式测验统计不符: registry={emb.get('pages')}页/{emb.get('total_blocks')}块 "
            f"actual={len(actual_pages)}页/{actual_blocks}块"
        )
    print(f"  嵌入式测验: {len(actual_pages)} 页 / {actual_blocks} 块")

    # ---- 检查 2：题型多样性 ----
    print("== 检查 2：题型多样性（每 quiz ≥3 种）==")
    for q in quizzes:
        path = ROOT / q["path"]
        if not path.exists():
            continue
        a = analyze_quiz(path)
        status = "OK" if len(a["types"]) >= 3 else "FAIL"
        print(f"  [{status}] {path.name}: {len(a['types'])} 种 {sorted(a['types'])}")
        if len(a["types"]) < 3:
            failures.append(f"[diversity] {q['path']}: 仅 {len(a['types'])} 种题型")

    # ---- 检查 3：难度标注率 ----
    print("== 检查 3：难度标注率 ==")
    total_q, total_annotated = 0, 0
    for q in quizzes:
        path = ROOT / q["path"]
        if not path.exists():
            continue
        a = analyze_quiz(path)
        total_q += a["questions"]
        total_annotated += a["annotated"]
        if a["annotated"] < a["questions"]:
            failures.append(
                f"[difficulty] {q['path']}: {a['annotated']}/{a['questions']} 题带难度标注"
            )
        if args.verbose:
            print(f"  {path.name}: {a['annotated']}/{a['questions']}")
    rate = (total_annotated / total_q * 100) if total_q else 0.0
    print(f"  总计: {total_annotated}/{total_q} = {rate:.1f}%")

    # ---- 检查 4：双向链接率（回链缺失仅统计）----
    print("== 检查 4：双向链接 ==")
    q2c_ok, backlink_ok, missing_backlinks = 0, 0, []
    for q in quizzes:
        path = ROOT / q["path"]
        if not path.exists():
            continue
        qtext = path.read_text(encoding="utf-8")
        cps = [ROOT / cp for cp in q.get("concept_pages", [])]
        if any(cp.exists() and has_link_to(qtext, path, cp) for cp in cps):
            q2c_ok += 1
        else:
            failures.append(f"[link] {q['path']}: 缺失 quiz→concept 链接")
        if any(cp.exists() and has_link_to(cp.read_text(encoding="utf-8"), cp, path) for cp in cps):
            backlink_ok += 1
        else:
            missing_backlinks.append(q["path"])
    print(f"  quiz→concept: {q2c_ok}/{len(quizzes)}")
    print(f"  concept→quiz 回链: {backlink_ok}/{len(quizzes)}（缺失 {len(missing_backlinks)}，W3-b 批量补链）")
    if missing_backlinks and args.verbose:
        for m in missing_backlinks:
            print(f"    缺回链: {m}")
    if missing_backlinks:
        warnings.append(f"concept→quiz 回链缺失 {len(missing_backlinks)}/{len(quizzes)}")

    # ---- 汇总 ----
    print("== 汇总 ==")
    print(f"  失败: {len(failures)}  观察项警告: {len(warnings)}")
    for f in failures:
        print(f"  FAIL {f}")
    for w in warnings:
        print(f"  WARN {w}")

    if failures and args.strict:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
