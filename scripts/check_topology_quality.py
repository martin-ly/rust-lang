#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""P0-2/P0-4 语义质量门：knowledge_topology/ atlas 实质质量检查。

把 atlas 系列从"看起来有图"变成可机器验证的实质结构。检测：
  T1 01 概念定义图"定义"列套话率（Core Rust concept / — / 空 / <15字 / Guide to）
  T2 07 层内映射关系类型单一化（⟹ 等符号分布，最高频>=95% 记关系塌缩）
  T3 03/09 决策/判定树 mermaid：[[...]] 跳出叶子数、根因 R 无修复的死端数
  T4 03/09 判定节点（菱形 {..?}）定量/边界占比
  T5 02 atlas 抽取 bug（单元格泄漏 `> > [` / `> **`）
  T6 atlas 占位字样（TODO/TBD/占位/待补/XXX）

默认 warning（退出 0），--strict 超阈值退出 1。
阈值（strict）：T1 套话率>=10%；T2 最高频关系>=95%；T3 跳出率>=20% 或 死端>0；
T4 定量占比<50%（03/09）；T5>0；T6>0。
输出 reports/TOPOLOGY_QUALITY_<date>.{md,json}
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
TOPO = os.path.join(ROOT, "concept", "00_meta", "knowledge_topology")

DEF_LOW = [
    re.compile(r"core rust concept", re.IGNORECASE),
    re.compile(r"^—?\s*$"),
    re.compile(r"^\s*(a|an)\s+(guide|overview|introduction)\s+(to|of)\b", re.IGNORECASE),
    re.compile(r"^\s*(comprehensive|complete)\s+(analysis|guide|overview)\b", re.IGNORECASE),
]
REL_RE = re.compile(r"[⟹⟸⇒⇐≡⊥↔→⇔⟶⟵]")
MERMAID_RE = re.compile(r"```mermaid\s*\n(.*?)\n```", re.S)
JUMP_RE = re.compile(r"\[\[[^\]]*\]\]")
DIAMOND_RE = re.compile(r"(\w+)\{([^}]*)\}")
EDGE_RE = re.compile(r"(\w+)\s*(?:-->|-.->|==>|--\s*[^-\s].*?-->|-+)")
ROOTCAUSE_RE = re.compile(r"(R\d+)\s*\[([^\]]*根因[^\]]*)\]")
PLACEHOLDER_RE = re.compile(r"\b(TODO|TBD|XXX|FIXME)\b|占位|待补|待完善|填写")
LEAK_RE = re.compile(r">\s*>\s*\[")  # 仅匹配嵌套引用+链接的抽取泄漏，勿匹配正常 '> **字段**'
QUANT_RE = re.compile(r"\d|阈值|边界|>=|<=|≥|≤|>|<|ms|us|ns|倍|%|个|次|层")


def read(p):
    try:
        return open(p, encoding="utf-8", errors="ignore").read()
    except Exception:
        return ""


def t1_definition_atlas(text):
    """01 atlas：找'定义'列（精确匹配表头单元格），统计套话率。"""
    lines = text.splitlines()
    total = 0
    low = 0
    def_col = None
    samples = []
    for ln in lines:
        if not ln.strip().startswith("|"):
            continue
        cells = [c.strip() for c in ln.strip().strip("|").split("|")]
        # 表头识别必须精确匹配“定义”列：子串匹配会把中文名列含“定义”二字的数据行
        # （如 [Rust 知识体系概念定义判定森林](...)）误判为表头，导致 def_col 错位、
        # 后续所有行按错误列统计（T1 曾因此把 A/S/P 统计表的“数量”列当定义列）。
        if any(c == "定义" for c in cells):
            for i, c in enumerate(cells):
                if c == "定义":
                    def_col = i
                    break
            continue
        if set("".join(cells)) <= set("-: ") or def_col is None:
            continue
        if len(cells) <= def_col:
            continue
        val = cells[def_col]
        # 跳过表头/分组行（编号列通常形如 `xxx` 或为空）
        total += 1
        is_low = (len(val) < 15) or any(p.search(val) for p in DEF_LOW)
        if is_low:
            low += 1
            if len(samples) < 12:
                # 取中文名/EN 列辅助定位
                name = cells[1] if len(cells) > 1 else ""
                samples.append((name[:40], val[:50]))
    rate = (low / total) if total else 0.0
    return {"total_rows": total, "low": low, "rate": round(rate, 3), "samples": samples}


def t2_relation_collapse(text):
    counts = {}
    for m in REL_RE.findall(text):
        counts[m] = counts.get(m, 0) + 1
    total = sum(counts.values())
    top = max(counts.values()) if counts else 0
    top_rate = (top / total) if total else 0.0
    top_sym = max(counts, key=counts.get) if counts else None
    return {"total": total, "counts": counts, "top_symbol": top_sym,
            "top_rate": round(top_rate, 3), "collapsed": top_rate >= 0.95}


def t3_t4_graphs(text):
    blocks = MERMAID_RE.findall(text)
    jump_nodes = 0
    total_nodes = 0
    dead_ends = []
    diamonds = 0
    quant_diamonds = 0
    for b in blocks:
        # 节点：任何位置出现的 id 后接形状括号（含边里隐式定义的节点）
        node_ids = set(re.findall(r"\b(\w+)\s*(?:\[\[|\[|\{|\(|>)", b))
        total_nodes += len(node_ids)
        jump_ids = set(re.findall(r"\b(\w+)\s*\[\[[^\]]*\]\]", b))
        jump_nodes += len(jump_ids)
        # 根因死端
        out_edges = set(EDGE_RE.findall(b))
        for rid, label in ROOTCAUSE_RE.findall(b):
            if rid not in out_edges:
                dead_ends.append((rid, label[:40]))
        # 判定节点定量占比
        for did, label in DIAMOND_RE.findall(b):
            diamonds += 1
            if QUANT_RE.search(label):
                quant_diamonds += 1
    jump_rate = (jump_nodes / total_nodes) if total_nodes else 0.0
    quant_rate = (quant_diamonds / diamonds) if diamonds else 1.0
    return {
        "blocks": len(blocks), "nodes": total_nodes, "jump_nodes": jump_nodes,
        "jump_rate": round(jump_rate, 3), "dead_ends": dead_ends, "dead_end_count": len(dead_ends),
        "diamonds": diamonds, "quant_diamonds": quant_diamonds, "quant_rate": round(quant_rate, 3),
    }


def check_file(path):
    text = read(path)
    rel = os.path.relpath(path, ROOT).replace("\\", "/")
    name = os.path.basename(path)
    res = {"rel": rel, "lines": text.count("\n") + 1}
    issues = {}
    if name.startswith("01_"):
        r = t1_definition_atlas(text)
        res["T1"] = r
        if r["rate"] >= 0.10:
            issues["T1"] = f"定义列套话率 {r['rate']*100:.1f}% ({r['low']}/{r['total_rows']})"
    if name.startswith("07_"):
        r = t2_relation_collapse(text)
        res["T2"] = r
        if r["collapsed"]:
            issues["T2"] = f"关系塌缩: {r['top_symbol']} 占 {r['top_rate']*100:.1f}% ({r['counts']})"
    if name.startswith(("03_", "09_")):
        r = t3_t4_graphs(text)
        res["T3T4"] = r
        if r["jump_rate"] >= 0.20:
            issues["T3"] = f"跳出叶子率 {r['jump_rate']*100:.1f}% ({r['jump_nodes']}/{r['nodes']})"
        if r["dead_end_count"] > 0:
            issues["T3d"] = f"死端 {r['dead_end_count']}: {r['dead_ends'][:3]}"
        if r["diamonds"] >= 3 and r["quant_rate"] < 0.50:
            issues["T4"] = f"判定定量占比 {r['quant_rate']*100:.1f}% ({r['quant_diamonds']}/{r['diamonds']})"
    # T5 抽取 bug（02 atlas 为主，但全扫）
    leaks = LEAK_RE.findall(text)
    if leaks:
        res["T5"] = len(leaks)
        issues["T5"] = f"单元格泄漏 {len(leaks)} 处"
    # T6 占位
    ph = PLACEHOLDER_RE.findall(text)
    if ph:
        res["T6"] = len(ph)
        issues["T6"] = f"占位字样 {len(ph)} 处"
    res["issues"] = issues
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--out-date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    files = sorted(glob.glob(os.path.join(TOPO, "*.md")))
    results = [check_file(p) for p in files]
    flagged = [r for r in results if r["issues"]]

    # 汇总指标
    t1 = next((r["T1"] for r in results if "T1" in r), None)
    t2 = next((r["T2"] for r in results if "T2" in r), None)
    graph_files = [r["T3T4"] for r in results if "T3T4" in r]
    total_jump = sum(g["jump_nodes"] for g in graph_files)
    total_nodes = sum(g["nodes"] for g in graph_files)
    total_dead = sum(g["dead_end_count"] for g in graph_files)
    total_dia = sum(g["diamonds"] for g in graph_files)
    total_qdia = sum(g["quant_diamonds"] for g in graph_files)
    total_leaks = sum(r.get("T5", 0) for r in results)
    total_ph = sum(r.get("T6", 0) for r in results)

    summary = {
        "date": args.out_date, "files": len(results), "flagged": len(flagged),
        "T1_def_low_rate": t1["rate"] if t1 else None,
        "T1_def_low": (t1["low"], t1["total_rows"]) if t1 else None,
        "T2_top_rate": t2["top_rate"] if t2 else None,
        "T2_top_symbol": t2["top_symbol"] if t2 else None,
        "T3_jump": (total_jump, total_nodes),
        "T3_jump_rate": round(total_jump / total_nodes, 3) if total_nodes else 0,
        "T3_dead_ends": total_dead,
        "T4_quant_rate": round(total_qdia / total_dia, 3) if total_dia else 1.0,
        "T5_leaks": total_leaks, "T6_placeholders": total_ph,
    }
    would_fail = []
    if t1 and t1["rate"] >= 0.10:
        would_fail.append(f"T1 定义套话率 {t1['rate']*100:.1f}% >=10%")
    if t2 and t2["collapsed"]:
        would_fail.append(f"T2 关系塌缩 {t2['top_symbol']} {t2['top_rate']*100:.1f}% >=95%")
    if total_nodes and total_jump / total_nodes >= 0.20:
        would_fail.append(f"T3 跳出率 {total_jump}/{total_nodes} >=20%")
    if total_dead > 0:
        would_fail.append(f"T3 死端 {total_dead} >0")
    if total_dia >= 3 and total_qdia / total_dia < 0.50:
        would_fail.append(f"T4 判定定量占比 {total_qdia}/{total_dia} <50%")
    if total_leaks > 0:
        would_fail.append(f"T5 抽取泄漏 {total_leaks} >0")
    if total_ph > 0:
        would_fail.append(f"T6 占位字样 {total_ph} >0")

    out_md = os.path.join(ROOT, "reports", f"TOPOLOGY_QUALITY_{args.out_date}.md")
    out_json = os.path.join(ROOT, "reports", f"TOPOLOGY_QUALITY_{args.out_date}.json")
    with open(out_json, "w", encoding="utf-8") as f:
        json.dump({"summary": summary, "results": results}, f, ensure_ascii=False, indent=2)
    with open(out_md, "w", encoding="utf-8") as f:
        f.write(f"# 拓扑图谱实质质量（语义质量门 P0-2/P0-4）\n\n")
        f.write(f"**日期**: {args.out_date}  **扫描**: {len(results)} atlas 文件  **有问题**: {len(flagged)}\n\n")
        f.write("| 指标 | 值 | 阈值 | 判定 |\n|---|:---:|:---:|:---:|\n")
        def row(k, v, thr, fail):
            f.write(f"| {k} | {v} | {thr} | {'FAIL' if fail else 'pass'} |\n")
        row("T1 定义列套话率", f"{t1['rate']*100:.1f}% ({t1['low']}/{t1['total_rows']})" if t1 else "n/a", "<10%", t1 and t1["rate"] >= 0.10)
        row("T2 关系最高频占比", f"{t2['top_symbol']} {t2['top_rate']*100:.1f}%" if t2 else "n/a", "<95%", t2 and t2["collapsed"])
        row("T3 跳出叶子率", f"{(total_jump/total_nodes*100) if total_nodes else 0:.1f}% ({total_jump}/{total_nodes})", "<20%", total_nodes and total_jump/total_nodes >= 0.20)
        row("T3 根因死端", total_dead, "0", total_dead > 0)
        row("T4 判定定量占比", f"{(total_qdia/total_dia*100) if total_dia else 100:.1f}% ({total_qdia}/{total_dia})", ">=50%", total_dia >= 3 and total_qdia/total_dia < 0.50)
        row("T5 单元格泄漏", total_leaks, "0", total_leaks > 0)
        row("T6 占位字样", total_ph, "0", total_ph > 0)
        f.write("\n## 各文件问题\n\n")
        for r in flagged:
            f.write(f"- `{r['rel']}`\n")
            for k, v in r["issues"].items():
                f.write(f"  - {k}: {v}\n")
        if t1 and t1.get("samples"):
            f.write("\n## T1 定义列套话样例\n\n")
            for nm, val in t1["samples"]:
                f.write(f"- `{nm}` → 「{val}」\n")
        f.write("\n## WOULD-FAIL（--strict 阻断）\n\n")
        for w in would_fail:
            f.write(f"- {w}\n")
        if not would_fail:
            f.write("- 无\n")
        f.write(f"\n## 机器可读\n\n- JSON: `reports/TOPOLOGY_QUALITY_{args.out_date}.json`\n")

    print(f"[P0-2/4] files={len(results)} flagged={len(flagged)}")
    print(f"  T1 def_low_rate={summary['T1_def_low_rate']}  T2 top={t2['top_symbol'] if t2 else None} {summary['T2_top_rate']}")
    print(f"  T3 jump={total_jump}/{total_nodes} dead_ends={total_dead}  T4 quant_rate={summary['T4_quant_rate']}")
    print(f"  T5 leaks={total_leaks}  T6 placeholders={total_ph}")
    print(f"[P0-2/4] report: {os.path.relpath(out_md, ROOT).replace(chr(92),'/')}")
    for w in would_fail:
        print(f"   WOULD-FAIL: {w}")
    if args.strict and would_fail:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
