#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""P0-1 语义质量门：concept/ 元数据一致性检查器。

目标：把"全局语义不一致"从形容词变成可机器复核的数字基线，并可接入 CI。
检测（均只读 concept/，排除 archive）：
  D1 Bloom 层级 ↔ 层次定位/层级 同文件互斥（含 Bloom 重复声明互相冲突）
  D2 A/S/P 标记与 Bloom 层级脱节（A->L1-2, S->L2-4, P->L4-7）
  D3 关键字段同文件重声明（Bloom/Rust版本/层次定位/A-S-P/内容分级）
  D4 文首块内 Rust 版本号自矛盾（distinct minor >= 2）
  D5 稳定层(非07_future)正文残留 nightly/preview/unstable/feature(
     （排除：WASI Preview N 专名、URL 路径中的 nightly、D5_WHITELIST_FILES 显式登记项）
  D6 Summary 低信息量模板套话（P0-2 的一部分，顺手输出）

白名单机制（2026-07-12 建立，消除“例外未登记”状态）：
  D2_WHITELIST_FILES / D5_WHITELIST_FILES：逐文件人工复核后显式登记，附理由注释；
  登记项不计入 counts/flagged，但在报告“已登记白名单”小节中公示，保持透明。

退出码：
  默认（warning 模式）：始终 0，但 stdout 标注 WOULD-FAIL 项，便于观察不阻断。
  --strict：超阈值时退出 1（供 CI 使用）。
阈值（strict）：D1>0；D2>=5%；D3>0；D4>0；D5>0（剔除白名单）；D6>=3%。

输出：
  reports/METADATA_CONSISTENCY_BASELINE_<date>.md   人可读汇总 + Top 样例
  reports/METADATA_CONSISTENCY_BASELINE_<date>.json 机器可读全量
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
CONCEPT = os.path.join(ROOT, "concept")

FIELD_RE = re.compile(r"^>\s*\*\*(.+?)\*\*\s*[:：]\s*(.*?)\s*$")
BLOOM_RANGE_RE = re.compile(r"L\s*(\d+)\s*[-–—~]\s*L?\s*(\d+)")
BLOOM_SINGLE_RE = re.compile(r"L\s*(\d+)")
LEVEL_RE = re.compile(r"L\s*(\d+)")
ASP_RE = re.compile(r"\b([ASP])\b")
VER_RE = re.compile(r"\b1\.(\d{2,3})(?:\.\d+)?\b")
NIGHTLY_RE = re.compile(r"\b(nightly|preview|unstable)\b|feature\s*\(", re.IGNORECASE)

SUMMARY_LOW_PATTERNS = [
    re.compile(r"^\s*(a|an)\s+(guide|overview|introduction)\s+(to|of|on|about|for)\b", re.IGNORECASE),
    re.compile(r"core rust concept", re.IGNORECASE),
    re.compile(r"^\s*(this\s+(document|file|page|note))\s+(covers?|describes?|explains?)\b", re.IGNORECASE),
    re.compile(r"^\s*(comprehensive|an?\s+in-depth)\s+(analysis|review|look|overview)\s+(of|on|into)\b", re.IGNORECASE),
    re.compile(r"^\s*(a|an)?\s*(comprehensive|complete)\s+guide\s+to\b", re.IGNORECASE),
]
ASP_MAP = {"A": {1, 2}, "S": {2, 3, 4}, "P": {4, 5, 6, 7}}
KEY_FIELDS = ["Bloom 层级", "Rust 版本", "对应 Rust 版本", "层次定位", "层级", "A/S/P 标记", "内容分级"]
# 这些文件以讨论 nightly/preview 为内容，D5 豁免
# （knowledge_topology 为跨层生成的元层索引，nightly/preview 仅作为概念名引用出现，非稳定层正文残留）
D5_WHITELIST_SUBSTR = ("07_future", "nightly_rust", "version_tracking", "preview_features", "knowledge_topology")

# D2 显式登记白名单（2026-07-12 复核登记，消除“例外未登记”状态）：
# A/S/P 内容分级（A->L1-2, S->L2-4, P->L4-7）只适用于概念内容页；
# 以下页面经人工复核确认为合法特例，A/S/P 与 Bloom 不交集属页面性质使然，非元数据错误。
D2_WHITELIST_FILES = {
    # L0 纯导航索引页：内容为跨层文件清单，无概念正文；A/S/P=S 仅表示其索引的结构化属性，
    # Bloom L0（元信息层）天然不在 S 的 L2-4 区间内。
    "concept/00_meta/04_navigation/13_foundations_gap_closure_index.md":
        "L0 导航索引页，无概念正文，A/S/P 内容分级不适用",
    # L7 版本/生态跟踪页：文件头已声明“非概念权威页”，A/S/P=S+A 描述其跟踪对象（L4 权威页）
    # 的内容属性而非自身层级；跟踪页不按概念页分级。
    "concept/07_future/03_preview_features/33_autoverus_preview.md":
        "L7 预览跟踪页（非概念权威页），A/S/P 描述被跟踪对象属性",
}

# D5 显式登记白名单（2026-07-12 逐文件复核）：以下稳定层页面的 nightly/preview/unstable
# 提及均为页面主题本身或工具链事实（如 Miri 仅 nightly 可用），非“稳定层残留不稳定依赖”。
# 登记前已逐项核对：所涉特性（min_specialization / negative_impls / const_trait_impl /
# generic_const_exprs / -Zbuild-std / -Zscript / -Zpublic-dependency / panic_handler /
# RUSTC_BOOTSTRAP / rustc -Z flags / Miri nightly toolchain）截至 Rust 1.97.0 stable 仍属
# nightly-only，声明准确，保留白名单。
D5_WHITELIST_FILES = {
    "concept/00_meta/01_terminology/01_terminology_glossary.md":
        "术语表：『特性门控(Feature Gate)』词条本身描述 nightly 机制；另含 1.97 新特性 nightly 状态跟踪小节",
    "concept/02_intermediate/00_traits/01_traits.md":
        "文首已显式声明不稳定特性警告；negative_impls/min_specialization/const_trait_impl 仍为 nightly-only",
    "concept/02_intermediate/00_traits/04_advanced_traits.md":
        "文首已显式声明不稳定特性警告；specialization/negative_impls/trait alias 仍为 nightly-only",
    "concept/02_intermediate/01_generics/01_generics.md":
        "文首已显式声明不稳定特性警告；generic_const_exprs/min_specialization/-Zshare-generics 仍为 nightly-only",
    "concept/04_formal/04_model_checking/08_miri.md":
        "Miri 解释器上游仅发布 nightly 组件，工具链事实",
    "concept/04_formal/05_rustc_internals/01_rustc_query_system.md":
        "rustc 内部 API/-Z 调试标志仅 nightly 可用，页面主题为 rustc 内部机制",
    "concept/04_formal/05_rustc_internals/03_trait_solver_in_rustc.md":
        "新 trait solver -Znext-solver 仅 nightly 可用，页面主题为 rustc 内部机制",
    "concept/06_ecosystem/00_toolchain/05_compiler_infrastructure.md":
        "并行前端/Cranelift 后端/build-std 均为 nightly-only 工具链能力",
    "concept/06_ecosystem/00_toolchain/12_rustc_bootstrap.md":
        "RUSTC_BOOTSTRAP 主题本身就是“在非 nightly 编译器上启用 unstable feature”",
    "concept/06_ecosystem/01_cargo/01_cargo_script.md":
        "cargo script (-Zscript) 截至 1.97 仍为 nightly 特性，页面主题即该特性",
    "concept/06_ecosystem/01_cargo/02_public_private_deps.md":
        "public 依赖完整语义 (-Zpublic-dependency) 截至 1.97 仍为 nightly 特性，页面主题即该特性",
    "concept/06_ecosystem/01_cargo/03_resolver_v3_public_feature_unification.md":
        "public-dependency 实验特性完整检查需 nightly，页面主题即该特性",
    "concept/06_ecosystem/01_cargo/22_build_std.md":
        "-Zbuild-std 截至 1.97 仍为 nightly 特性，页面主题即该特性",
    "concept/06_ecosystem/11_domain_applications/03_webassembly.md":
        "#![feature(panic_handler)] 自定义 panic handler 截至 1.97 仍为 nightly-only（wasm32-unknown-unknown 场景）",
    "concept/sources/INDEX.md":
        "来源索引：Unstable Book(UNB) 作为权威来源条目及其 nightly 状态标注即索引内容本身",
}


def expand_bloom(text: str):
    """从字段值里提取 Bloom 层级集合（区间展开）。可能多个区间，取并集。"""
    s = set()
    for a, b in BLOOM_RANGE_RE.findall(text):
        lo, hi = int(a), int(b)
        if lo > hi:
            lo, hi = hi, lo
        for x in range(lo, hi + 1):
            if 0 <= x <= 7:
                s.add(x)
    # 仅当没有区间时才采信单个 Lx（避免把 "L0-L7" 里的端点重复加入无所谓）
    if not s:
        for m in BLOOM_SINGLE_RE.findall(text):
            x = int(m)
            if 0 <= x <= 7:
                s.add(x)
    return s


def parse_file(path: str):
    try:
        text = open(path, encoding="utf-8", errors="ignore").read()
    except Exception:
        return None
    lines = text.splitlines()

    # 收集所有 ">**K**: V" 字段（跨多个引用块）
    fields = {}  # key -> list[value]
    for ln in lines:
        m = FIELD_RE.match(ln)
        if m:
            k = m.group(1).strip()
            v = m.group(2).strip()
            fields.setdefault(k, []).append(v)

    # 文首块：第一个 '---' 之前（用于 D4 版本自矛盾，限定在头部元数据区）
    head = []
    for ln in lines:
        if ln.strip() == "---":
            break
        head.append(ln)
    head_text = "\n".join(head)

    def first(key):
        return fields.get(key, [None])[0]

    bloom_vals = fields.get("Bloom 层级", [])
    bloom_set = set()
    for v in bloom_vals:
        bloom_set |= expand_bloom(v)

    # 层次定位/层级：只取主层级（避免把“跨层映射 L1→L4”误抓成 {1,4}）
    level_nums = set()
    for key in ("层次定位", "层级"):
        for v in fields.get(key, []):
            first_seg = re.split(r"[→⟹]|->|跨层|映射|embed|extension", v, flags=re.IGNORECASE)[0]
            m = LEVEL_RE.search(first_seg)
            if m and 0 <= int(m.group(1)) <= 7:
                level_nums.add(int(m.group(1)))
                break  # 该字段只取主层级

    asp_text = " ".join(fields.get("A/S/P 标记", []))
    asp = None
    m_asp = re.search(r"\*\*\s*([ASP])\s*\*\*", asp_text) or ASP_RE.search(asp_text)
    if m_asp:
        asp = m_asp.group(1)

    rel = os.path.relpath(path, ROOT).replace("\\", "/")
    return {
        "rel": rel,
        "fields": fields,
        "bloom_set": bloom_set,
        "bloom_vals": bloom_vals,
        "level_nums": level_nums,
        "asp": asp,
        "head_text": head_text,
        "text": text,
        "summary": first("Summary") or "",
    }


def check(rec):
    issues = {f"D{i}": [] for i in range(1, 7)}
    b = rec["bloom_set"]
    lvl = rec["level_nums"]
    asp = rec["asp"]
    fields = rec["fields"]

    # D1 Bloom 互斥：Bloom 区间互相冲突，或 Bloom 与 层次定位/层级 主值不一致
    bloom_intervals = []
    for v in rec["bloom_vals"]:
        for a, bb in BLOOM_RANGE_RE.findall(v):
            bloom_intervals.append((int(a), int(bb)))
    if len(bloom_intervals) >= 2:
        # 多个区间且不相同 -> 自冲突
        if len({(min(a, bb), max(a, bb)) for a, bb in bloom_intervals}) > 1:
            issues["D1"].append(f"Bloom 多区间冲突: {rec['bloom_vals']}")
    if b and lvl:
        # 若层次定位给出的层级都不落在 Bloom 集合内 -> 互斥
        if not (b & lvl):
            issues["D1"].append(f"Bloom {sorted(b)} 与 层次定位/层级 {sorted(lvl)} 无交集")

    # D2 A/S/P 与 Bloom 脱节（显式登记白名单豁免，见 D2_WHITELIST_FILES 理由注释）
    if rec["rel"] in D2_WHITELIST_FILES:
        asp = None
    if asp and b:
        allowed = ASP_MAP.get(asp, set())
        if allowed and not (b & allowed):
            issues["D2"].append(f"A/S/P={asp} 允许 {sorted(allowed)} 与 Bloom {sorted(b)} 无交集")

    # D3 关键字段重声明
    for k in KEY_FIELDS:
        if len(fields.get(k, [])) >= 2:
            issues["D3"].append(f"{k} 声明 {len(fields[k])} 次: {fields[k]}")

    # D4 文首块 Rust 版本自矛盾（仅看版本字段值，不看前置/后置链接里的版本号）
    ver_text = " ".join(fields.get("Rust 版本", []) + fields.get("对应 Rust 版本", []))
    minors = {int(m) for m in VER_RE.findall(ver_text)}
    if len(minors) >= 2:
        issues["D4"].append(f"版本字段 distinct minor {sorted(minors)}: {ver_text[:80]}")

    # D5 稳定层 nightly/preview 残留（路径子串豁免 + 显式登记白名单豁免）
    if (not any(w in rec["rel"] for w in D5_WHITELIST_SUBSTR)
            and rec["rel"] not in D5_WHITELIST_FILES):
        # 仅统计正文（去掉头部元数据块，粗略取第一个 '---' 之后）
        body = rec["text"]
        sep = body.find("\n---")
        if sep != -1:
            body = body[sep:]
        cnt = 0
        for m in NIGHTLY_RE.finditer(body):
            w = m.group(0).lower()
            # 排除 1：WASI Preview 1/2/3 为 WebAssembly 系统接口规范的版本专名，
            # 与 Rust nightly/preview 无关（“preview”后接数字，或上下文含 WASI）
            if w == "preview":
                ctx = body[max(0, m.start() - 25): m.end() + 8]
                if re.search(r"wasi", ctx, re.IGNORECASE) or re.match(r"\s*\d", body[m.end(): m.end() + 4]):
                    continue
            # 排除 2：URL 路径中的 nightly（如 doc.rust-lang.org/nightly/... 官方文档
            # 固定托管路径，platform-support/unstable-book 仅在 nightly 路径下发布），
            # 属权威来源引用而非正文残留
            if w == "nightly" and m.start() > 0 and body[m.start() - 1] == "/":
                continue
            cnt += 1
        if cnt > 0:
            issues["D5"].append(f"稳定层 nightly/preview 关键词 {cnt} 处")

    # D6 Summary 套话
    summ = rec["summary"].strip()
    if not summ:
        issues["D6"].append("Summary 为空")
    else:
        en_part = summ.split("  ")[0]  # 中文 Summary 常为中英双语，取首段
        if len(en_part) < 15 or any(p.search(en_part) for p in SUMMARY_LOW_PATTERNS):
            issues["D6"].append(f"套话: {en_part[:60]}")

    return issues


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", action="store_true", help="超阈值退出 1（CI 用）")
    ap.add_argument("--out-date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    files = [
        p for p in glob.glob(os.path.join(CONCEPT, "**", "*.md"), recursive=True)
        if os.sep + "archive" + os.sep not in p and "/archive/" not in p.replace("\\", "/")
    ]
    recs = [r for r in (parse_file(p) for p in files) if r]
    n = len(recs)

    per_file = {}
    counts = {f"D{i}": 0 for i in range(1, 7)}
    examples = {f"D{i}": [] for i in range(1, 7)}
    for r in recs:
        issues = check(r)
        flagged = {k: v for k, v in issues.items() if v}
        if flagged:
            per_file[r["rel"]] = flagged
        for k, v in issues.items():
            if v:
                counts[k] += 1
                if len(examples[k]) < 12:
                    examples[k].append((r["rel"], v[0]))

    pct = lambda k: round(counts[k] / n * 100, 1) if n else 0
    d2_base = sum(1 for r in recs if r["asp"] and r["bloom_set"])
    summary = {
        "date": args.out_date,
        "scanned": n,
        "counts": counts,
        "pct": {k: pct(k) for k in counts},
        "D2_base_files_with_asp_and_bloom": d2_base,
        "flagged_files": len(per_file),
    }

    # 阈值判定（strict）
    would_fail = []
    if counts["D1"] > 0:
        would_fail.append(f"D1 Bloom互斥 {counts['D1']} (>0)")
    if d2_base and counts["D2"] / d2_base >= 0.05:
        would_fail.append(f"D2 A/S/P脱节 {counts['D2']}/{d2_base} (>=5%)")
    if counts["D3"] > 0:
        would_fail.append(f"D3 字段重声明 {counts['D3']} (>0)")
    if counts["D4"] > 0:
        would_fail.append(f"D4 版本自矛盾 {counts['D4']} (>0)")
    if counts["D5"] > 0:
        would_fail.append(f"D5 稳定层nightly残留 {counts['D5']} (>0)")
    if counts["D6"] / n >= 0.03:
        would_fail.append(f"D6 Summary套话 {counts['D6']} ({pct('D6')}%>=3%)")

    # 写 JSON
    out_json = os.path.join(ROOT, "reports", f"METADATA_CONSISTENCY_BASELINE_{args.out_date}.json")
    with open(out_json, "w", encoding="utf-8") as f:
        json.dump({"summary": summary, "examples": examples, "per_file": per_file}, f, ensure_ascii=False, indent=2)

    # 写 Markdown
    out_md = os.path.join(ROOT, "reports", f"METADATA_CONSISTENCY_BASELINE_{args.out_date}.md")
    names = {
        "D1": "Bloom 层级 ↔ 层次定位/层级 同文件互斥",
        "D2": "A/S/P 标记与 Bloom 脱节（A->L1-2,S->L2-4,P->L4-7）",
        "D3": "关键字段同文件重声明",
        "D4": "文首块 Rust 版本号自矛盾",
        "D5": "稳定层正文残留 nightly/preview/unstable",
        "D6": "Summary 低信息量模板套话",
    }
    with open(out_md, "w", encoding="utf-8") as f:
        f.write(f"# 元数据一致性基线（语义质量门 P0-1）\n\n")
        f.write(f"**日期**: {args.out_date}  **扫描**: {n} concept 活跃文件（排除 archive）  **模式**: {'strict' if args.strict else 'warning（不阻断）'}\n\n")
        f.write("| 规则 | 命中文件 | 占比 | 阈值 | 判定 |\n|---|:---:|:---:|:---:|:---:|\n")
        thr = {"D1": ">0", "D2": ">=5%", "D3": ">0", "D4": ">0", "D5": ">0", "D6": ">=3%"}
        for k in ["D1", "D2", "D3", "D4", "D5", "D6"]:
            verdict = "FAIL" if any(w.startswith(k) for w in would_fail) else "pass"
            extra = f" (基={d2_base})" if k == "D2" else ""
            f.write(f"| {k} {names[k]} | {counts[k]}{extra} | {pct(k)}% | {thr[k]} | {verdict} |\n")
        f.write(f"\n**受影响文件总数**: {len(per_file)} / {n}\n\n")
        f.write("## 已登记白名单（人工复核确认的合法特例，不计入命中）\n\n")
        f.write("### D2 A/S/P ↔ Bloom 脱节豁免\n\n")
        for rel, reason in D2_WHITELIST_FILES.items():
            f.write(f"- `{rel}` — {reason}\n")
        f.write("\n### D5 稳定层 nightly/preview 豁免\n\n")
        for rel, reason in D5_WHITELIST_FILES.items():
            f.write(f"- `{rel}` — {reason}\n")
        f.write("\n另有两类规则级排除：WASI Preview 1/2/3（WASM 规范版本专名）与 "
                "URL 路径中的 nightly（官方文档固定托管路径）。\n\n")
        f.write("## 各类 Top 样例\n\n")
        for k in ["D1", "D2", "D3", "D4", "D5", "D6"]:
            f.write(f"### {k} {names[k]}（{counts[k]}）\n\n")
            for rel, msg in examples[k]:
                f.write(f"- `{rel}` — {msg}\n")
            f.write("\n")
        f.write("## WOULD-FAIL（接入 CI strict 时将阻断）\n\n")
        if would_fail:
            for w in would_fail:
                f.write(f"- {w}\n")
        else:
            f.write("- 无（全部通过）\n")
        f.write(f"\n## 机器可读\n\n- JSON: `reports/METADATA_CONSISTENCY_BASELINE_{args.out_date}.json`\n")

    # stdout 仅 ASCII
    print(f"[P0-1] scanned={n} flagged_files={len(per_file)}")
    for k in ["D1", "D2", "D3", "D4", "D5", "D6"]:
        print(f"  {k} count={counts[k]} pct={pct(k)}%  ({names[k]})")
    print(f"  D2 base(asp&bloom)={d2_base}")
    print(f"[P0-1] report: {os.path.relpath(out_md, ROOT).replace(chr(92),'/')}")
    if would_fail:
        print("[P0-1] WOULD-FAIL under --strict:")
        for w in would_fail:
            print(f"   - {w}")
    if args.strict and would_fail:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
