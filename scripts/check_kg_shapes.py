#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""P3-4 语义质量门：KG SHACL 子集校验（把 kg_shapes.ttl 的约束落到可运行校验）。

校验 concept/00_meta/kg_data_v3.json（474 entities / 5799 relations）：
  K1  实体必填字段：@id / @type / skos:prefLabel / skos:scopeNote / ex:path
  K1b 实体缺 ex:bloomLevel（信息缺失，记录但不 fail）
  K2  ex:path 指向文件存在（相对 concept/ 或项目根）
  K3  skos:prefLabel 须含 zh 与 en 双语
  K4  @id 唯一
  K5  relations 无悬空引用（object 端 @id 不在实体集）
  K6  decision_trees / fault_trees 节点完整性（若存在）
  K7  实体须有 ex:layer 与 ex:domain（taxonomy.yaml 分类模型；缺失即报告）

默认 warning（退出 0）；--strict 超阈值退出 1。
阈值：K1>0；K2>0；K3>0；K4>0；K5>0；K6>0；K7>0。K1b 仅记录。
输出 reports/KG_SHAPES_VALIDATION_<date>.{md,json}
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CONCEPT = os.path.join(ROOT, "concept")
KG = os.path.join(CONCEPT, "00_meta", "kg_data_v3.json")


def langs(node):
    out = set()
    for item in node or []:
        if isinstance(item, dict) and "@language" in item:
            out.add(item["@language"])
    return out


def path_exists(p):
    if not p:
        return False
    return os.path.exists(os.path.join(CONCEPT, p)) or os.path.exists(os.path.join(ROOT, p))


def rel_endpoints(r):
    """兼容多种关系结构：{source,target} / {from,to} / {subject,object} / {subject,predicate,object}。"""
    src = r.get("source") or r.get("from") or r.get("subject") or r.get("s")
    tgt = r.get("target") or r.get("to") or r.get("object") or r.get("o")
    pred = r.get("predicate") or r.get("type") or r.get("relation") or r.get("p") or r.get("@type")
    return src, tgt, pred


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--out-date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    d = json.load(open(KG, encoding="utf-8"))
    entities = d.get("entities", [])
    relations = d.get("relations", [])
    decision_trees = d.get("decision_trees", [])
    fault_trees = d.get("fault_trees", [])

    id_set = set()
    k1_missing = []   # 缺必填
    k1b_bloom = []    # 缺 bloomLevel
    k2_badpath = []
    k3_bilingual = []
    k4_dup = []
    k7_missing = []   # 缺 ex:layer / ex:domain
    required = ["@id", "@type", "skos:prefLabel", "skos:scopeNote", "ex:path"]

    for e in entities:
        eid = e.get("@id")
        if eid in id_set:
            k4_dup.append(eid)
        id_set.add(eid)
        miss = [f for f in required if f not in e or e[f] in (None, "", [])]
        if miss:
            k1_missing.append((eid, miss))
        if "ex:bloomLevel" not in e:
            k1b_bloom.append(eid)
        if not path_exists(e.get("ex:path")):
            k2_badpath.append((eid, e.get("ex:path")))
        ls = langs(e.get("skos:prefLabel"))
        if not ({"zh", "en"} <= ls):
            k3_bilingual.append((eid, sorted(ls)))
        miss_ld = [f for f in ("ex:layer", "ex:domain") if not e.get(f)]
        if miss_ld:
            k7_missing.append((eid, miss_ld))

    # K5 悬空引用
    k5_dangling = []
    rel_sample = relations[0] if relations else None
    for r in relations:
        if not isinstance(r, dict):
            continue
        src, tgt, pred = rel_endpoints(r)
        for end in (src, tgt):
            if isinstance(end, str) and end.startswith("ex:") and end not in id_set:
                k5_dangling.append((src, pred, tgt))
                break

    # K6 决策树/故障树节点完整性
    k6_bad = []
    for name, trees in [("decision_trees", decision_trees), ("fault_trees", fault_trees)]:
        if isinstance(trees, list):
            for t in trees:
                if isinstance(t, dict) and not (t.get("nodes") or t.get("tree") or t.get("root")):
                    k6_bad.append((name, t.get("@id") or t.get("id") or "?"))

    summary = {
        "date": args.out_date,
        "entities": len(entities), "relations": len(relations),
        "decision_trees": len(decision_trees) if isinstance(decision_trees, list) else 0,
        "fault_trees": len(fault_trees) if isinstance(fault_trees, list) else 0,
        "K1_missing_required": len(k1_missing),
        "K1b_missing_bloomLevel": len(k1b_bloom),
        "K2_bad_path": len(k2_badpath),
        "K3_not_bilingual": len(k3_bilingual),
        "K4_duplicate_id": len(k4_dup),
        "K5_dangling_relations": len(k5_dangling),
        "K6_bad_tree_nodes": len(k6_bad),
        "K7_missing_layer_domain": len(k7_missing),
    }
    would_fail = []
    if summary["K1_missing_required"] > 0:
        would_fail.append(f"K1 缺必填 {summary['K1_missing_required']}")
    if summary["K2_bad_path"] > 0:
        would_fail.append(f"K2 路径不存在 {summary['K2_bad_path']}")
    if summary["K3_not_bilingual"] > 0:
        would_fail.append(f"K3 非双语 {summary['K3_not_bilingual']}")
    if summary["K4_duplicate_id"] > 0:
        would_fail.append(f"K4 重复id {summary['K4_duplicate_id']}")
    if summary["K5_dangling_relations"] > 0:
        would_fail.append(f"K5 悬空引用 {summary['K5_dangling_relations']}")
    if summary["K6_bad_tree_nodes"] > 0:
        would_fail.append(f"K6 树节点缺 {summary['K6_bad_tree_nodes']}")
    if summary["K7_missing_layer_domain"] > 0:
        would_fail.append(f"K7 缺 layer/domain {summary['K7_missing_layer_domain']}")

    out_md = os.path.join(ROOT, "reports", f"KG_SHAPES_VALIDATION_{args.out_date}.md")
    out_json = os.path.join(ROOT, "reports", f"KG_SHAPES_VALIDATION_{args.out_date}.json")
    with open(out_json, "w", encoding="utf-8") as f:
        json.dump({"summary": summary, "relation_sample": rel_sample,
                   "K1_missing": k1_missing[:30], "K1b_bloom_missing_sample": k1b_bloom[:10],
                   "K2_bad_path": k2_badpath[:30], "K3_not_bilingual": k3_bilingual[:30],
                   "K4_dup": k4_dup[:30], "K5_dangling": k5_dangling[:30], "K6_bad": k6_bad[:30],
                   "K7_missing_layer_domain": k7_missing[:30]},
                  f, ensure_ascii=False, indent=2)
    with open(out_md, "w", encoding="utf-8") as f:
        f.write(f"# KG SHACL 子集校验（语义质量门 P3-4）\n\n")
        f.write(f"**日期**: {args.out_date}  **实体**: {len(entities)}  **关系**: {len(relations)}  "
                f"**决策树**: {summary['decision_trees']}  **故障树**: {summary['fault_trees']}\n\n")
        f.write("| 规则 | 命中 | 阈值 | 判定 |\n|---|:---:|:---:|:---:|\n")
        rows = [("K1 缺必填字段", summary["K1_missing_required"], "0"),
                ("K1b 缺 ex:bloomLevel", summary["K1b_missing_bloomLevel"], "记录"),
                ("K2 path 文件不存在", summary["K2_bad_path"], "0"),
                ("K3 prefLabel 非双语", summary["K3_not_bilingual"], "0"),
                ("K4 @id 重复", summary["K4_duplicate_id"], "0"),
                ("K5 关系悬空引用", summary["K5_dangling_relations"], "0"),
                ("K6 树节点不完整", summary["K6_bad_tree_nodes"], "0"),
                ("K7 缺 ex:layer/ex:domain", summary["K7_missing_layer_domain"], "0")]
        for nm, v, thr in rows:
            fail = (thr == "0" and v > 0)
            f.write(f"| {nm} | {v} | {thr} | {'FAIL' if fail else ('记录' if thr == '记录' else 'pass')} |\n")
        f.write(f"\n关系结构样例: `{json.dumps(rel_sample, ensure_ascii=False)[:300]}`\n")
        f.write("\n## WOULD-FAIL（--strict 阻断）\n\n")
        for w in would_fail:
            f.write(f"- {w}\n")
        if not would_fail:
            f.write("- 无\n")
        f.write(f"\n## 机器可读\n\n- JSON: `reports/KG_SHAPES_VALIDATION_{args.out_date}.json`\n")

    print(f"[P3-4] entities={len(entities)} relations={len(relations)}")
    print(f"  K1={summary['K1_missing_required']} K1b(no_bloom)={summary['K1b_missing_bloomLevel']} "
          f"K2={summary['K2_bad_path']} K3={summary['K3_not_bilingual']} K4={summary['K4_duplicate_id']} "
          f"K5={summary['K5_dangling_relations']} K6={summary['K6_bad_tree_nodes']} "
          f"K7={summary['K7_missing_layer_domain']}")
    print(f"[P3-4] report: {os.path.relpath(out_md, ROOT).replace(chr(92),'/')}")
    for w in would_fail:
        print(f"   WOULD-FAIL: {w}")
    if args.strict and would_fail:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
