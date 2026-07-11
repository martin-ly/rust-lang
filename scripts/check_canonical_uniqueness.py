#!/usr/bin/env python3
"""check_canonical_uniqueness.py — concept/ 权威页唯一性检查

依据 AGENTS.md §2 Canonical 规则：同一概念只能有一个权威页。

检测两类违规：
  (a) 多个**非 stub** 文件同时声明「本文件为 concept/ 权威页」，且中文标题或
      EN 标题高度相似（疑似双权威页 / 重复权威页）。
  (b) 同一目录下存在编号不同但主题（文件名去掉数字前缀后的词干）高度相似的
      双文件（疑似同主题重复编号文件）。

排除：
  - concept/archive/、concept/sources/ 及其任意子路径
  - 文件名含 placeholder 的文件
  - stub 文件（重定向/学习入口 stub，见 STUB_MARKERS）
  - 进阶关系豁免：两文件名词干构成「同一基础词干 + 进阶后缀」（如
    error_handling / error_handling_basics / error_handling_deep_dive），视为合法
    分层（L1 基础 → L2 主页 → 深入专题），不报双权威页（见 PROGRESSION_SUFFIXES）

用法：
  python scripts/check_canonical_uniqueness.py            # 输出报告，exit 0
  python scripts/check_canonical_uniqueness.py --strict   # 有违规时 exit 1
  python scripts/check_canonical_uniqueness.py --json     # JSON 输出
"""

from __future__ import annotations

import argparse
import difflib
import json
import re
import sys
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONCEPT_DIR = ROOT / "concept"

CANONICAL_DECL = re.compile(r"本文件为\s*`?concept/?`?\s*权威页")
TITLE_RE = re.compile(r"^#\s+(.+?)\s*$", re.MULTILINE)
EN_RE = re.compile(r"\*\*EN\*\*\s*[:：]\s*(.+?)\s*$", re.MULTILINE)

# 重定向 / stub 标记：出现任一即视为 stub，不参与“多权威页”判定
STUB_MARKERS = (
    "本主题已合并至",
    "本文件保留为重定向",
    "本文件为重定向",
    "本文件为学习入口 stub",
    "redirect",
)

EXCLUDE_DIR_PARTS = {"archive", "sources"}
# 结构性/元文件：不参与权威页唯一性判定
EXCLUDE_NAME_KEYWORDS = ("template", "atlas", "glossary", "quiz")
EXCLUDE_BASENAMES = {"readme.md", "summary.md", "index.md"}

# 标题相似度阈值（difflib ratio）
TITLE_SIMILARITY = 0.85
# 文件名词干相似度阈值
STEM_SIMILARITY = 0.6
# 词干过短不比较（避免 "01_a.md" vs "02_b.md" 的噪音）
MIN_STEM_LEN = 4

# 进阶关系豁免后缀：词干 = 基础词干 + 后缀 视为合法分层（如 L1 basics → L2 主页 → deep dive）
PROGRESSION_SUFFIXES = ("basics", "basic", "advanced", "deep_dive")


def _strip_progression(s: str) -> str:
    """去掉词干末尾的进阶后缀(仅一层)。"""
    for suffix in PROGRESSION_SUFFIXES:
        tail = f"_{suffix}"
        if s.endswith(tail):
            return s[: -len(tail)]
    return s


def progression_related(s1: str, s2: str) -> bool:
    """两词干是否构成「同一基础主题 + 进阶后缀」的合法分层关系。

    例：error_handling ~ error_handling_basics ~ error_handling_deep_dive、
    lifetimes ~ lifetimes_advanced。此类跨层进阶页不按双权威页处理，
    但应在各自文件中声明层级定位并互链（AGENTS.md §2）。
    """
    b1, b2 = _strip_progression(s1), _strip_progression(s2)
    return b1 == b2 and (b1 != s1 or b2 != s2)


def normalize(text: str) -> str:
    """归一化标题：去标点/空白/常见括号注释，仅用于相似度比较。"""
    text = text.lower()
    text = re.sub(r"[（）()\[\]【】：:，,。·\-—_`'\s]+", "", text)
    return text


def is_stub(text: str, size: int) -> bool:
    if any(marker in text for marker in STUB_MARKERS):
        return True
    # 极短文件（< 1500 字节）且含「权威来源」指引视为 stub
    if size < 1500 and "权威来源" in text:
        return True
    return False


def collect_pages() -> list[dict]:
    pages = []
    for path in sorted(CONCEPT_DIR.rglob("*.md")):
        rel_parts = path.relative_to(CONCEPT_DIR).parts
        if any(part in EXCLUDE_DIR_PARTS for part in rel_parts[:-1]):
            continue
        if "placeholder" in path.name.lower():
            continue
        name = path.name.lower()
        if name in EXCLUDE_BASENAMES or any(k in name for k in EXCLUDE_NAME_KEYWORDS):
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        title_m = TITLE_RE.search(text)
        en_m = EN_RE.search(text)
        pages.append(
            {
                "path": path,
                "rel": path.relative_to(ROOT).as_posix(),
                "title": title_m.group(1) if title_m else "",
                "en": en_m.group(1).strip() if en_m else "",
                "canonical": bool(CANONICAL_DECL.search(text)),
                "stub": is_stub(text, path.stat().st_size),
            }
        )
    return pages


def similar(a: str, b: str, threshold: float) -> bool:
    na, nb = normalize(a), normalize(b)
    if not na or not nb:
        return False
    if na == nb:
        return True
    return difflib.SequenceMatcher(None, na, nb).ratio() >= threshold


def stem_of(filename: str) -> str:
    """去掉前导数字编号，得到主题词干：31_safety_tags_preview.md -> safety_tags_preview"""
    s = re.sub(r"^\d+_", "", Path(filename).stem)
    return s


def check_a(pages: list[dict]) -> list[dict]:
    """(a) 多个非 stub 权威声明文件且标题/EN 高度相似。

    严重级别：
    - error: 文件名词干完全相同且（跨目录时 EN 标题相同或词干为多词）——
      真实双权威页几乎总是同名不同编号，如 30_/18_lifetimes_advanced.md。
    - warn: 标题高度相似且词干相似——可能是合法的跨层主题（如
      'Patterns' vs 'Design Patterns'），需人工确认。
    """
    canonicals = [p for p in pages if p["canonical"] and not p["stub"]]
    findings = []
    for p1, p2 in combinations(canonicals, 2):
        s1, s2 = stem_of(p1["path"].name), stem_of(p2["path"].name)
        if len(s1) < MIN_STEM_LEN or len(s2) < MIN_STEM_LEN:
            continue
        if progression_related(s1, s2):
            continue  # 进阶关系豁免（basics/advanced/deep_dive 合法分层）
        same_dir = p1["path"].parent == p2["path"].parent
        stem_ratio = difflib.SequenceMatcher(None, s1, s2).ratio()
        en_eq = bool(p1["en"] and p2["en"] and normalize(p1["en"]) == normalize(p2["en"]))

        if s1 == s2 and (same_dir or en_eq or "_" in s1):
            findings.append(
                {
                    "type": "dual_canonical",
                    "severity": "error",
                    "files": [p1["rel"], p2["rel"]],
                    "reason": f"文件名词干相同 '{s1}'"
                    + ("（同目录）" if same_dir else "")
                    + (f"，EN 标题相同: '{p1['en']}'" if en_eq else ""),
                }
            )
            continue

        if stem_ratio < STEM_SIMILARITY:
            continue
        hit = None
        if p1["en"] and p2["en"] and similar(p1["en"], p2["en"], TITLE_SIMILARITY):
            hit = f"EN 标题相似: '{p1['en']}' ~ '{p2['en']}'"
        elif p1["title"] and p2["title"] and similar(p1["title"], p2["title"], TITLE_SIMILARITY):
            hit = f"中文标题相似: '{p1['title']}' ~ '{p2['title']}'"
        if hit:
            findings.append(
                {
                    "type": "dual_canonical",
                    "severity": "warn",
                    "files": [p1["rel"], p2["rel"]],
                    "reason": hit + f"（词干 '{s1}' ~ '{s2}'）",
                }
            )
    return findings


def check_b(pages: list[dict]) -> list[dict]:
    """(b) 同目录同主题编号双文件。

    - error: 同目录词干完全相同（如 08_/31_safety_tags_preview.md）。
    - warn: 同目录词干高度相似但不同，需人工确认是否为不同主题。
    """
    by_dir: dict[str, list[dict]] = {}
    for p in pages:
        if p["stub"]:
            continue
        by_dir.setdefault(str(p["path"].parent), []).append(p)
    findings = []
    for group in by_dir.values():
        for p1, p2 in combinations(group, 2):
            s1, s2 = stem_of(p1["path"].name), stem_of(p2["path"].name)
            if len(s1) < MIN_STEM_LEN or len(s2) < MIN_STEM_LEN:
                continue
            if progression_related(s1, s2):
                continue  # 进阶关系豁免（basics/advanced/deep_dive 合法分层）
            if s1 == s2:
                findings.append(
                    {
                        "type": "same_dir_topic_duplicate",
                        "severity": "error",
                        "files": [p1["rel"], p2["rel"]],
                        "reason": f"同目录词干相同: '{s1}'",
                    }
                )
            elif difflib.SequenceMatcher(None, s1, s2).ratio() >= STEM_SIMILARITY:
                findings.append(
                    {
                        "type": "same_dir_topic_duplicate",
                        "severity": "warn",
                        "files": [p1["rel"], p2["rel"]],
                        "reason": f"同目录主题词干相似: '{s1}' ~ '{s2}'",
                    }
                )
    return findings


def main() -> int:
    ap = argparse.ArgumentParser(description="concept/ 权威页唯一性检查（AGENTS.md §2）")
    ap.add_argument("--strict", action="store_true", help="发现违规时 exit 1")
    ap.add_argument("--json", action="store_true", help="JSON 格式输出")
    args = ap.parse_args()

    pages = collect_pages()
    findings = check_a(pages) + check_b(pages)
    errors = [f for f in findings if f.get("severity") == "error"]
    warns = [f for f in findings if f.get("severity") == "warn"]

    if args.json:
        print(
            json.dumps(
                {
                    "total_pages": len(pages),
                    "errors": errors,
                    "warnings": warns,
                },
                ensure_ascii=False,
                indent=2,
            )
        )
    else:
        print("=" * 72)
        print("concept/ 权威页唯一性检查报告（AGENTS.md §2 Canonical 规则）")
        print("=" * 72)
        print(f"扫描页面: {len(pages)}（排除 archive/、sources/、placeholder、模板/图谱/README）")
        if not findings:
            print("✅ 未发现双权威页或同目录同主题重复文件。")
        else:
            if errors:
                print(f"❌ ERROR {len(errors)} 处（疑似双权威页/同主题重复，--strict 时阻断）:\n")
                for i, f in enumerate(errors, 1):
                    label = "双权威页声明" if f["type"] == "dual_canonical" else "同目录同主题重复"
                    print(f"  [E{i}] {label}")
                    for fp in f["files"]:
                        print(f"      - {fp}")
                    print(f"      原因: {f['reason']}\n")
            if warns:
                print(f"⚠️  WARN {len(warns)} 处（疑似跨层同主题，需人工确认，不阻断）:\n")
                for i, f in enumerate(warns, 1):
                    label = "双权威页声明" if f["type"] == "dual_canonical" else "同目录同主题重复"
                    print(f"  [W{i}] {label}")
                    for fp in f["files"]:
                        print(f"      - {fp}")
                    print(f"      原因: {f['reason']}\n")
            print("处理建议: 保留一个权威页，其余改为重定向 stub（模板见 AGENTS.md §4.3）。")

    if args.strict and errors:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
