#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""concept/ 权威层「国际化权威来源」覆盖率审计（P0 对齐网络的国际化权威相关内容）。

复用 scripts/maintenance/authority_coverage_dashboard.py 的 P0/P1/P2 权威域分级，
把扫描域从 docs/12_research_notes 扩展到 concept/ 权威层（AGENTS.md §2：concept/ 为单一权威来源）。
只审计、不改正文（无副作用）。输出覆盖率基线 + 缺口页清单（核心 L1-L4 且无 P0 国际权威）。

P0 官方: doc.rust-lang.org / rust-lang.github.io / github.com/rust-lang / rustc-dev-guide / ferrocene
P1 学术/形式化: plv.mpi-sws(RustBelt/Jung) / arxiv / acm / ieee / springer / plf.inf.ethz / aeneas
P2 社区/生态: verus / creusot / formal-land / AeneasVerif / docs.rs / crates.io / sea-ql / blog.rust-lang.org ...

输出 reports/CONCEPT_AUTHORITY_COVERAGE_<date>.{md,json}。永远 exit 0（informational）。
"""
from __future__ import annotations

import argparse
import datetime as _dt
import glob
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
sys.path.insert(0, os.path.join(ROOT, "scripts", "maintenance"))
CONCEPT = os.path.join(ROOT, "concept")
TODAY = _dt.date.today().isoformat()

# 复用 maintenance 的权威域分级（单一来源）；import 失败则用内置 fallback
try:
    from authority_coverage_dashboard import P0_DOMAINS, P1_DOMAINS, P2_DOMAINS  # type: ignore
except Exception:  # pragma: no cover
    P0_DOMAINS = [r"doc\.rust-lang\.org", r"rust-lang\.github\.io", r"github\.com/rust-lang",
                  r"rustc-dev-guide\.rust-lang\.org", r"spec\.ferrocene\.dev"]
    P1_DOMAINS = [r"plv\.mpi-sws\.org", r"arxiv\.org", r"acm\.org", r"dl\.acm\.org",
                  r"ieee\.org", r"springer\.com", r"plf\.inf\.ethz\.ch", r"aeneas"]
    P2_DOMAINS = [r"github\.com/verus-lang", r"github\.com/creusot-rs", r"github\.com/formal-land",
                  r"docs\.rs", r"crates\.io", r"blog\.rust-lang\.org"]

try:
    import concept_config
    def layer_of(p):
        parts = os.path.relpath(p, CONCEPT).replace("\\", "/").split("/")
        for seg in parts:
            if seg in concept_config.LAYER_DIRS:
                return concept_config.LAYER_DIRS[seg]
        return "L?"
except Exception:
    def layer_of(p):
        return "L?"

P0_RE = re.compile("|".join(P0_DOMAINS))
P1_RE = re.compile("|".join(P1_DOMAINS))
P2_RE = re.compile("|".join(P2_DOMAINS))

# crates/*/docs 扩展域（--include-crates）：P0/P1/P2 超集 + 生态权威
# （tokio.rs / rustwasm / rust-embedded / webassembly.org / w3.org / egui /
#  kani / aeneas 等，与 tmp/crates_docs_authority_full.py 的 AUTH 口径一致）
CRATES_AUTH_RE = re.compile(
    r"doc\.rust-lang\.org|rust-lang\.github\.io|rustc-dev-guide|docs\.rs|crates\.io|"
    r"arxiv\.org|acm\.org|ieee\.org|springer\.com|usenix\.org|"
    r"github\.com/rust-lang|rust-lang\.org/rfcs|spec\.ferrocene\.dev|ferrocene\.dev|"
    r"tokio\.rs|rustwasm\.github\.io|rust-embedded|w3\.org|webassembly\.org|"
    r"github\.com/verus-lang|github\.com/AeneasVerif|aeneasverif\.github\.io|"
    r"model-checking\.github\.io|blog\.rust-lang\.org|foundation\.rust-lang\.org|"
    r"egui\.rs|areweguiyet\.com|lukaswirth\.dev",
    re.I)

CRATES_STUB_MARKERS = [
    "Stub redirecting to the canonical", "Stub pointing to the canonical",
    "本文件为 crate 文档占位页", "本文件原为对应 crate", "本 stub 按",
    "占位 stub", "This file previously contained", "通用 Rust 概念解释已迁移",
    "此处仅保留索引与 canonical", "合规整改迁移", "本页仅保留主题索引与入口链接",
    "导航 stub", "重定向 stub", "迁移至 `concept/` 权威页", "已迁移/整合至上方",
    "请参见上方权威页",
]
CRATES_STUB_MARKERS_CI = [
    "(redirect)", "orientation stub", "redirect to the canonical",
    "has been migrated to the concept authority page",
]


def crates_classify(path, text):
    """crates docs 文件分类：stub / quiz / index_readme / code_listing / content。
    口径与 tmp/crates_docs_authority_full.py 一致（2026-07-12 全量基线）。"""
    lines = text.strip().splitlines()
    low = text.lower()
    if (any(m in text for m in CRATES_STUB_MARKERS)
            or any(m in low for m in CRATES_STUB_MARKERS_CI)
            or (len(lines) <= 15 and "> **权威来源**" in text)):
        return "stub"
    rel = path.replace("\\", "/").lower()
    if "quiz" in rel:
        return "quiz"
    if "/snippets/readme.md" in rel:
        return "code_listing"  # 纯代码片段目录豁免页（AGENTS.md §4.0）
    if os.path.basename(path) == "README.md":
        stripped = re.sub(r"\n*## 国际权威来源\n.*\Z", "", text, flags=re.S)
        body = [l for l in stripped.splitlines()
                if l.strip() and not l.startswith(("#", ">", "**"))]
        if not body:
            return "index_readme"
        linkish = sum(1 for l in body if l.lstrip().startswith(("- [", "* [", "|", "[")))
        if len(body) <= 30 and linkish / len(body) > 0.6:
            return "index_readme"
    return "content"


def scan_crates_docs():
    """扫描 crates/*/docs（含嵌套子 crate），返回统计 dict。"""
    pats = [os.path.join(ROOT, "crates", "*", "docs", "**", "*.md"),
            os.path.join(ROOT, "crates", "*", "*", "docs", "**", "*.md")]
    files = sorted({p for pat in pats for p in glob.glob(pat, recursive=True)})
    rows = []
    for p in files:
        try:
            text = open(p, encoding="utf-8", errors="ignore").read()
        except Exception:
            continue
        rel = os.path.relpath(p, ROOT).replace("\\", "/")
        crate = rel.split("/")[1]
        kind = crates_classify(rel, text)
        rows.append({"path": rel, "crate": crate, "kind": kind,
                     "authority": bool(CRATES_AUTH_RE.search(text))})
    content = [r for r in rows if r["kind"] == "content"]
    covered = [r for r in content if r["authority"]]
    per = {}
    for r in content:
        d = per.setdefault(r["crate"], [0, 0])
        d[0] += 1
        d[1] += 1 if r["authority"] else 0
    kinds = {}
    for r in rows:
        kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    return {
        "total": len(rows), "kinds": kinds,
        "content": len(content), "covered": len(covered),
        "pct": round(100 * len(covered) / len(content), 1) if content else 0.0,
        "gaps": [r["path"] for r in content if not r["authority"]],
        "per_crate": {c: {"content": v[0], "covered": v[1]} for c, v in sorted(per.items())},
        "skipped": {k: [r["path"] for r in rows if r["kind"] == k]
                    for k in ("index_readme", "code_listing", "quiz")},
    }

SKIP_NAMES = {"SUMMARY.md", "README.md"}


def active_md():
    out = []
    for p in glob.glob(os.path.join(CONCEPT, "**", "*.md"), recursive=True):
        rel = os.path.relpath(p, CONCEPT).replace("\\", "/")
        if rel.startswith("archive/") or "/archive/" in rel:
            continue
        if os.path.basename(p) in SKIP_NAMES:
            continue
        # 排除重定向 stub（Summary 含 'Redirect stub' 或 'Merged Redirect' 且短页）：
        # 权威内容在目标页，stub 本身不应刷 URL；两种措辞均为 AGENTS.md §2 允许的重定向形式
        try:
            head = open(p, encoding="utf-8", errors="ignore").read(2048)
        except Exception:
            head = ""
        if ("Redirect stub" in head or "Merged Redirect" in head) and head.count(chr(10)) < 30:
            continue
        out.append(p)
    return out


def main():
    ap = argparse.ArgumentParser(description="concept/ 权威层国际化权威来源覆盖率审计")
    ap.add_argument("--strict", action="store_true",
                    help="阻断模式：内容页 any<100%% / none>0 / 核心 L1-L4 无 P0 缺口>0 时 exit 1")
    ap.add_argument("--include-crates", action="store_true",
                    help="附加 crates/*/docs 权威覆盖小节（默认观察 exit 0；--strict 时内容页覆盖<100%% 亦阻断）")
    args = ap.parse_args()

    files = active_md()
    rows = []
    for p in files:
        try:
            t = open(p, encoding="utf-8", errors="ignore").read()
        except Exception:
            continue
        p0 = bool(P0_RE.search(t)); p1 = bool(P1_RE.search(t)); p2 = bool(P2_RE.search(t))
        rows.append({"path": os.path.relpath(p, ROOT).replace("\\", "/"),
                     "layer": layer_of(p), "P0": p0, "P1": p1, "P2": p2,
                     "any": p0 or p1 or p2, "lines": t.count("\n") + 1})
    n = len(rows)
    cov = lambda k: (sum(1 for r in rows if r[k]), round(100 * sum(1 for r in rows if r[k]) / n, 1)) if n else (0, 0.0)
    p0c, p0p = cov("P0"); p1c, p1p = cov("P1"); p2c, p2p = cov("P2"); anyc, anyp = cov("any")
    none = [r for r in rows if not r["any"]]
    # 内容页口径: 排除 00_meta 内部工具页 / quiz 测验页 / placeholders / sources 索引页
    # (这些页不是 Rust 概念内容, 不存在合适的国际学术/生态来源, 其权威基线为 P0 官方文档)
    def is_content(r):
        p = r["path"]
        return not (p.startswith("concept/00_meta/") or p.startswith("concept/sources/")
                    or "quiz" in p or "placeholders/" in p)
    crows = [r for r in rows if is_content(r)]
    cn = len(crows)
    ccov = lambda k: (sum(1 for r in crows if r[k]), round(100 * sum(1 for r in crows if r[k]) / cn, 1)) if cn else (0, 0.0)
    cp0c, cp0p = ccov("P0"); cp1c, cp1p = ccov("P1"); cp2c, cp2p = ccov("P2"); canyc, canyp = ccov("any")
    c_gaps_p1 = [r["path"] for r in crows if not r["P1"]]
    c_gaps_p2 = [r["path"] for r in crows if not r["P2"]]
    # 按层级分组
    layers = {}
    for r in rows:
        layers.setdefault(r["layer"], {"n": 0, "P0": 0, "any": 0})
        layers[r["layer"]]["n"] += 1
        layers[r["layer"]]["P0"] += 1 if r["P0"] else 0
        layers[r["layer"]]["any"] += 1 if r["any"] else 0
    # 核心缺口：L1-L4 且无 P0（官方国际权威）的页
    core_gaps = [r for r in rows if r["layer"] in ("L1", "L2", "L3", "L4") and not r["P0"]]
    core_gaps.sort(key=lambda r: (r["layer"], -r["lines"]))

    md = []
    md.append("# concept/ 权威层 · 国际化权威来源覆盖率（2026-07-11）\n")
    md.append("**EN**: Concept-layer International Authority Coverage")
    md.append("**Summary**: 复用 maintenance P0/P1/P2 权威域分级，把审计扩展到 concept/ 权威层；量化覆盖率与缺口，"
              "为『对齐网络上的国际化权威相关内容』提供机器可复核基线。仅审计，不改正文。\n")
    md.append(f"> 生成: {TODAY} · 扫描 concept/ 活跃 md: **{n}**（排除 archive/SUMMARY/README）")
    md.append("> P0 官方 / P1 学术形式化 / P2 社区生态，域定义复用 `scripts/maintenance/authority_coverage_dashboard.py`\n")
    md.append("## 总体覆盖率\n")
    md.append("| 维度 | 命中页 | 覆盖率 |")
    md.append("|:---|---:|---:|")
    md.append(f"| P0 官方（doc.rust-lang.org / rust-lang.github.io / rustc-dev-guide / ferrocene） | {p0c} | {p0p}% |")
    md.append(f"| P1 学术/形式化（RustBelt/arxiv/acm/ieee/springer/aeneas …） | {p1c} | {p1p}% |")
    md.append(f"| P2 社区/生态（verus/creusot/docs.rs/crates.io/blog.rust-lang.org …） | {p2c} | {p2p}% |")
    md.append(f"| **任一权威（P0∪P1∪P2）** | **{anyc}** | **{anyp}%** |")
    md.append(f"| 无任何国际权威引用（缺口） | {len(none)} | {round(100*len(none)/n,1) if n else 0}% |\n")
    md.append("## 内容页口径覆盖率（排除 00_meta 工具页 / quiz / placeholders / sources 索引）\n")
    md.append(f"> 内容页 **{cn}** 页。00_meta 为知识库内部工具/导航/审计页，非 Rust 概念内容，"
              "其权威基线为 P0 官方文档；P1/P2 学术生态来源对其不适用，故单列口径。\n")
    md.append("| 维度 | 命中页 | 覆盖率 |")
    md.append("|:---|---:|---:|")
    md.append(f"| P0 官方 | {cp0c} | {cp0p}% |")
    md.append(f"| P1 学术/形式化 | {cp1c} | {cp1p}% |")
    md.append(f"| P2 社区/生态 | {cp2c} | {cp2p}% |")
    md.append(f"| **任一权威** | **{canyc}** | **{canyp}%** |\n")
    if c_gaps_p1:
        md.append(f"内容页 P1 缺口（{len(c_gaps_p1)}）: " + " · ".join(f"`{g}`" for g in c_gaps_p1[:30]) + "\n")
    if c_gaps_p2:
        md.append(f"内容页 P2 缺口（{len(c_gaps_p2)}）: " + " · ".join(f"`{g}`" for g in c_gaps_p2[:30]) + "\n")
    md.append("## 按层级覆盖率\n")
    md.append("| 层级 | 页数 | P0 命中 | P0% | 任一权威 | 任一% |")
    md.append("|:---|---:|---:|---:|---:|---:|")
    for lv in ["L0", "L1", "L2", "L3", "L4", "L5", "L6", "L7", "L?"]:
        if lv in layers:
            d = layers[lv]
            md.append(f"| {lv} | {d['n']} | {d['P0']} | {round(100*d['P0']/d['n'],1)}% | {d['any']} | {round(100*d['any']/d['n'],1)}% |")
    md.append("\n## 核心缺口（L1-L4 且 无 P0 官方国际权威）\n")
    md.append(f"共 **{len(core_gaps)}** 页。下表为前 60（按层级、页长降序，优先补权威来源小节）。\n")
    md.append("| 层级 | 文件 | 行数 |")
    md.append("|:---|:---|---:|")
    for r in core_gaps[:60]:
        md.append(f"| {r['layer']} | `{r['path']}` | {r['lines']} |")
    if len(core_gaps) > 60:
        md.append(f"\n> … 另有 {len(core_gaps)-60} 页，见 JSON `core_gaps_l1_l4_no_p0`。")
    md.append("\n## 方法学与诚信\n")
    md.append("- 域分级来自现有 `maintenance/authority_coverage_dashboard.py`（单一来源），未新造口径。")
    md.append("- 『命中』= 正文含对应域的 URL 子串（`re.search`）；不区分链接/正文引用，偏宽松（覆盖率可能略高估，缺口清单偏保守可信）。")
    md.append("- 本审计只读，不修改任何文件；补缺口应基于 `concept/00_meta/02_sources/01_authority_source_map.md` 已核验映射 + 官方 URL，仅追加 References，不改正文事实。")
    md.append("\n---\n*由 `scripts/check_concept_authority_coverage.py` 生成*")

    crates = None
    if args.include_crates:
        crates = scan_crates_docs()
        md.append("\n## 附：crates/*/docs 权威覆盖（--include-crates 扩展）\n")
        md.append(f"> 扫描 crates docs md **{crates['total']}**（含嵌套子 crate）；"
                  f"stub/重定向 {crates['kinds'].get('stub', 0)}，"
                  f"纯索引 README {crates['kinds'].get('index_readme', 0)}，"
                  f"代码清单页 {crates['kinds'].get('code_listing', 0)}，quiz {crates['kinds'].get('quiz', 0)}。\n")
        md.append(f"- 非 stub 内容页 **{crates['content']}** 个，有国际权威来源引用 "
                  f"**{crates['covered']}** 个（**{crates['pct']}%**）。")
        md.append("- 权威域口径为 crates 扩展集（P0/P1/P2 超集 + tokio.rs/rustwasm/rust-embedded/"
                  "webassembly.org/w3.org/egui/kani/aeneas 等生态权威），见脚本 `CRATES_AUTH_RE`。")
        md.append("- 分类口径（stub 标记/纯索引 README/代码清单豁免）与 `tmp/crates_docs_authority_full.py` 一致。\n")
        md.append("| crate | 内容页 | 已覆盖 |")
        md.append("|:---|---:|---:|")
        for c, v in crates["per_crate"].items():
            md.append(f"| {c} | {v['content']} | {v['covered']} |")
        md.append("")
        if crates["gaps"]:
            md.append("crates 内容页缺口: " + " · ".join(f"`{g}`" for g in crates["gaps"][:40]) + "\n")
        skips = crates["skipped"]
        reg = []
        for k in ("index_readme", "code_listing", "quiz"):
            for p in skips.get(k, []):
                reg.append(f"`{p}`（{k}）")
        if reg:
            md.append("登记跳过（非 stub 但不计入内容页分母）: " + " · ".join(reg) + "\n")
        print(f"[crates-authority] total={crates['total']} content={crates['content']} "
              f"covered={crates['covered']} ({crates['pct']}%) gaps={len(crates['gaps'])}")

    os.makedirs(os.path.join(ROOT, "reports"), exist_ok=True)
    md_path = os.path.join(ROOT, "reports", f"CONCEPT_AUTHORITY_COVERAGE_{TODAY}.md")
    json_path = os.path.join(ROOT, "reports", f"CONCEPT_AUTHORITY_COVERAGE_{TODAY}.json")
    open(md_path, "w", encoding="utf-8", newline="\n").write("\n".join(md))
    payload = {"date": TODAY, "scanned": n,
               "coverage": {"P0": [p0c, p0p], "P1": [p1c, p1p], "P2": [p2c, p2p], "any": [anyc, anyp],
                            "none": len(none)},
               "content_scope": {"scanned": cn, "P0": [cp0c, cp0p], "P1": [cp1c, cp1p],
                                 "P2": [cp2c, cp2p], "any": [canyc, canyp],
                                 "gaps_p1": c_gaps_p1, "gaps_p2": c_gaps_p2},
               "by_layer": layers, "core_gaps_l1_l4_no_p0": [r["path"] for r in core_gaps],
               "none_any": [r["path"] for r in none]}
    if crates is not None:
        payload["crates_docs"] = crates
    open(json_path, "w", encoding="utf-8").write(json.dumps(payload, ensure_ascii=False, indent=2))
    print(f"[concept-authority] scanned={n}  P0={p0p}%  P1={p1p}%  P2={p2p}%  any={anyp}%  none={len(none)}")
    print(f"[concept-authority] content-scope n={cn}  P0={cp0p}%  P1={cp1p}%  P2={cp2p}%  any={canyp}%")
    print(f"[concept-authority] core L1-L4 gaps (no P0): {len(core_gaps)}")
    print(f"[concept-authority] report: {os.path.relpath(md_path, ROOT)}")
    if args.strict:
        fails = []
        if canyp < 100.0:
            fails.append(f"内容页 any 覆盖率 {canyp}% < 100%")
        if len(none) > 0:
            fails.append(f"无任何权威引用页 {len(none)} > 0")
        if len(core_gaps) > 0:
            fails.append(f"核心 L1-L4 无 P0 缺口 {len(core_gaps)} > 0")
        if crates is not None and crates["gaps"]:
            fails.append(f"crates docs 内容页权威缺口 {len(crates['gaps'])} > 0 "
                         f"（覆盖率 {crates['pct']}%）")
        if fails:
            print("[concept-authority] FAIL (--strict): " + "; ".join(fails))
            return 1
        print("[concept-authority] PASS (--strict): any=100% none=0 core_gaps=0")
    return 0


if __name__ == "__main__":
    sys.exit(main())
