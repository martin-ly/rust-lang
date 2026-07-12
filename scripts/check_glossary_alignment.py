#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""check_glossary_alignment.py — 术语表对齐检查（语义观察类质量工具）。

以 `concept/00_meta/01_terminology/01_terminology_glossary.md` 为权威术语表，
扫描仓库内其他术语表（文件名含 glossary/术语表），抽取同名术语的定义并比较：

- 关键语义缺失：权威定义的关键 token 在另一术语表定义中的覆盖率 < 阈值；
- 文本相似度低：覆盖率居中时给出 WARNING；
- 译名不一致：纯翻译表（中英对照）中译名与权威译名不同。

豁免：
- 重定向/占位 stub（含「占位 stub」「Quick links」「待补充」或行数过少的 crate 术语表）；
- archive/ .kimi/ book/ tmp/ target/ vendor/ .git/ 目录；
- scripts/templates/ 下的模板文件。

用法：
    python scripts/check_glossary_alignment.py            # 默认 exit 0，打印报告
    python scripts/check_glossary_alignment.py --strict   # 发现 DIVERGENCE 时 exit 1
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AUTHORITY = ROOT / "concept" / "00_meta" / "01_terminology" / "terminology_glossary.md"

EXCLUDE_DIRS = {".git", "archive", ".kimi", "book", "tmp", "target", "vendor", "node_modules"}
STUB_MARKERS = ("占位 stub", "Quick links", "待补充", "Placeholder", "crate 级文档占位")

# 术语级豁免注释：<!-- glossary-waive: <术语> -->（用于领域特指义项，需在注释旁说明理由）
WAIVE_PAT = re.compile(r"<!--\s*glossary-waive:\s*(.+?)(?:\s+—.*)?\s*-->")

# 关键语义覆盖率阈值：权威定义 token 在候选定义中的召回率
RECALL_DIVERGENCE = 0.5   # 低于此值 ⟹ DIVERGENCE（关键语义缺失）
RECALL_WARNING = 0.8      # 低于此值 ⟹ WARNING（部分一致）


@dataclass
class Entry:
    zh: str
    en: str
    definition: str
    file: Path
    line: int
    kind: str = "definition"  # definition | translation


@dataclass
class Finding:
    level: str  # DIVERGENCE | WARNING | TRANSLATION
    term: str
    file: Path
    line: int
    detail: str


def norm_key(s: str) -> str:
    """归一化术语键：小写、去反引号/标点/空白、去复数 s。"""
    s = s.strip().strip("`").lower()
    s = re.sub(r"[\s\-_/!.()]+", "", s)
    if s.endswith("s") and len(s) > 3:
        s = s[:-1]
    return s


def en_keys(en: str) -> set[str]:
    keys = set()
    for part in re.split(r"[/|]", en):
        k = norm_key(part)
        if k:
            keys.add(k)
    return keys


def tokens(text: str) -> set[str]:
    """把定义文本切成关键 token：中文 bigram + 英文/代码词。"""
    text = re.sub(r"[`*_#>\[\]()：:，,。.；;（）\"'“”‘’、/|—–-]+", " ", text)
    toks: set[str] = set()
    for word in text.split():
        if re.fullmatch(r"[a-zA-Z0-9_+]+", word):
            if len(word) >= 2:
                toks.add(word.lower())
        else:
            # 中文（可能混排）：按 2-gram 切
            han = re.findall(r"[\u4e00-\u9fff]+", word)
            for seg in han:
                if len(seg) == 1:
                    toks.add(seg)
                else:
                    for i in range(len(seg) - 1):
                        toks.add(seg[i : i + 2])
    return toks


def parse_authority(path: Path) -> list[Entry]:
    """权威表格式：- **中文** (English) [Lx] — 定义 — [来源](url)"""
    entries: list[Entry] = []
    pat = re.compile(r"^- \*\*(.+?)\*\*\s*\((.+?)\)\s*\[[^\]]*\]\s*—\s*(.+?)\s*—\s*\[")
    for i, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        m = pat.match(line)
        if m:
            entries.append(Entry(zh=m.group(1), en=m.group(2), definition=m.group(3),
                                 file=path, line=i))
    return entries


def is_stub(path: Path, text: str) -> bool:
    if any(marker in text for marker in STUB_MARKERS):
        return True
    body_lines = [ln for ln in text.splitlines() if ln.strip()]
    return len(body_lines) < 12


def parse_glossary(path: Path) -> list[Entry]:
    """从非权威术语表抽取术语条目（多格式兼容）。"""
    lines = path.read_text(encoding="utf-8").splitlines()
    entries: list[Entry] = []

    bullet_pat = re.compile(r"^- \*\*(.+?)\*\*\s*\((.+?)\)[^—\n]*—\s*(.+?)(?:\s*—\s*\[|$)")
    term_hdr_pat = re.compile(r"^\*\*(.+?)\*\*[:：]\s*$")           # **Term (中文)**:
    term_hdr2_pat = re.compile(r"^\*\*(.+?)\s*\((.+?)\)\*\*[:：]?\s*$")
    def_pat = re.compile(r"^- \*\*定义\*\*[:：]\s*(.+)$")
    heading_pat = re.compile(r"^#{3,4}\s+(.+?)(?:\s*\((.+?)\))?\s*(?:\{#[^}]*\})?\s*$")
    table2_pat = re.compile(r"^\|\s*([^|]+?)\s*\|\s*([^|]+?)\s*\|\s*$")  # | en | zh |

    i = 0
    n = len(lines)
    while i < n:
        line = lines[i]
        stripped = line.strip()

        m = bullet_pat.match(stripped)
        if m:
            entries.append(Entry(zh=m.group(1), en=m.group(2), definition=m.group(3),
                                 file=path, line=i + 1))
            i += 1
            continue

        # **Term**: 或 **Term (中文)**: 起始的多行条目
        m = term_hdr2_pat.match(stripped) or term_hdr_pat.match(stripped)
        if m and "**" not in m.group(1):
            en, zh = (m.group(1), m.group(2)) if m.lastindex == 2 else (m.group(1), "")
            # 若 group(1) 形如 "中文 (English)"，拆分
            mm = re.match(r"^(.+?)\s*\((.+?)\)$", en)
            if mm:
                zh, en = mm.group(1), mm.group(2)
            buf: list[str] = []
            j = i + 1
            while j < n and lines[j].strip().startswith("- **"):
                dm = def_pat.match(lines[j].strip())
                if dm:
                    buf.append(dm.group(1))
                else:
                    mm2 = re.match(r"^- \*\*(.+?)\*\*[:：]\s*(.+)$", lines[j].strip())
                    if mm2:
                        buf.append(f"{mm2.group(1)}: {mm2.group(2)}")
                j += 1
            if buf:
                entries.append(Entry(zh=zh, en=en, definition=" ".join(buf),
                                     file=path, line=i + 1))
            i = max(j, i + 1)
            continue

        m = heading_pat.match(stripped)
        if m and m.group(2) and len(m.group(1)) < 60 and "目录" not in m.group(1):
            # ### English (中文) — 取随后首个普通段落作为定义
            j = i + 1
            definition = ""
            while j < n:
                s = lines[j].strip()
                if s.startswith("#"):
                    break
                if s and not s.startswith((">", "-", "*", "|", "```", "<!--", "1.", "2.", "3.")):
                    definition = s
                    break
                j += 1
            if definition:
                entries.append(Entry(zh=m.group(2), en=m.group(1), definition=definition,
                                     file=path, line=i + 1))
            i += 1
            continue

        m = table2_pat.match(stripped)
        if m:
            col1, col2 = m.group(1).strip(), m.group(2).strip()
            if col1 and col2 and not col1.startswith(("-", "英文", "缩略语")) \
                    and re.search(r"[A-Za-z]", col1) and re.search(r"[\u4e00-\u9fff]", col2) \
                    and not re.search(r"[\u4e00-\u9fff]", col1):
                entries.append(Entry(zh=col2, en=col1, definition=col2, file=path,
                                     line=i + 1, kind="translation"))
            i += 1
            continue

        i += 1
    return entries


def discover_glossaries() -> list[Path]:
    found: list[Path] = []
    for p in ROOT.rglob("*"):
        if not p.is_file() or p.suffix != ".md":
            continue
        rel = p.relative_to(ROOT)
        if any(part in EXCLUDE_DIRS for part in rel.parts):
            continue
        if "templates" in rel.parts:
            continue
        name = p.name.lower()
        if "glossary" in name or "术语表" in p.name:
            found.append(p)
    return sorted(found)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--strict", action="store_true",
                    help="发现 DIVERGENCE/TRANSLATION 差异时 exit 1")
    args = ap.parse_args()

    if not AUTHORITY.exists():
        print(f"ERROR: 权威术语表不存在: {AUTHORITY}", file=sys.stderr)
        return 2

    authority = parse_authority(AUTHORITY)
    index: dict[str, Entry] = {}
    for e in authority:
        index.setdefault(norm_key(e.zh), e)
        for k in en_keys(e.en):
            index.setdefault(k, e)

    findings: list[Finding] = []
    scanned: list[str] = []
    stubs: list[str] = []

    for path in discover_glossaries():
        rel = path.relative_to(ROOT)
        if path == AUTHORITY:
            continue
        text = path.read_text(encoding="utf-8")
        if is_stub(path, text):
            stubs.append(str(rel))
            continue
        scanned.append(str(rel))
        waived = {norm_key(w) for w in WAIVE_PAT.findall(text)}
        for entry in parse_glossary(path):
            keys = en_keys(entry.en) | ({norm_key(entry.zh)} if entry.zh else set())
            if keys & waived:
                continue  # 术语级豁免（领域特指义项，文件内已注明）
            auth = next((index[k] for k in keys if k in index), None)
            if auth is None:
                continue  # 权威表未收录该术语，跳过

            if entry.kind == "translation":
                if entry.zh != auth.zh and auth.zh not in entry.zh and entry.zh not in auth.zh:
                    findings.append(Finding(
                        "TRANSLATION", entry.en, path, entry.line,
                        f"译名 `{entry.zh}` ≠ 权威译名 `{auth.zh}`"))
                continue

            auth_toks = tokens(auth.definition)
            other_toks = tokens(entry.definition)
            if not auth_toks or not other_toks:
                continue
            recall = len(auth_toks & other_toks) / len(auth_toks)
            if recall < RECALL_DIVERGENCE:
                findings.append(Finding(
                    "DIVERGENCE", entry.en or entry.zh, path, entry.line,
                    f"关键语义覆盖率 {recall:.2f} < {RECALL_DIVERGENCE}；"
                    f"权威定义: {auth.definition[:60]}… | 本处: {entry.definition[:60]}…"))
            elif recall < RECALL_WARNING:
                findings.append(Finding(
                    "WARNING", entry.en or entry.zh, path, entry.line,
                    f"关键语义覆盖率 {recall:.2f} < {RECALL_WARNING}（部分一致）"))

    print("=" * 72)
    print("术语表对齐检查报告 (check_glossary_alignment.py)")
    print("=" * 72)
    print(f"权威术语表: {AUTHORITY.relative_to(ROOT)}（{len(authority)} 条术语）")
    print(f"扫描术语表: {len(scanned)} 个；豁免 stub: {len(stubs)} 个")
    for s in stubs:
        print(f"  [STUB 豁免] {s}")
    print()

    div = [f for f in findings if f.level == "DIVERGENCE"]
    warn = [f for f in findings if f.level == "WARNING"]
    trans = [f for f in findings if f.level == "TRANSLATION"]

    for f in findings:
        print(f"[{f.level}] {f.file.relative_to(ROOT)}:{f.line} 术语 `{f.term}`")
        print(f"    {f.detail}")
    print()
    print(f"合计: DIVERGENCE={len(div)}  WARNING={len(warn)}  TRANSLATION={len(trans)}")

    if args.strict and (div or trans):
        print("--strict: 存在定义/译名差异，exit 1")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
