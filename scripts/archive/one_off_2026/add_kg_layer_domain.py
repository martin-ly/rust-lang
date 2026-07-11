#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""P3-x KG 增强：按 taxonomy.yaml 为 kg_data_v3.json 实体补 ex:layer / ex:domain。

输入：
  - concept/00_meta/taxonomy.yaml   （机器可读领域/层级模型，唯一配置源）
  - concept/00_meta/kg_data_v3.json （KG 唯一真相源）

推断规则（与 taxonomy.yaml matrix_rules 一致）：
  - layer  = path 第一段命中 layers[*].directory；根目录散落文件按 extra_prefixes，默认 L0
  - domain = 所有 domain.path_prefixes 中最长前缀匹配；无匹配 => fallback_domain

行为：
  - 写回前备份原文件为 kg_data_v3.json.bak（已存在则不覆盖，保留最原始备份）
  - 幂等：重复运行结果相同（ex:layer/ex:domain 按规则重算覆盖）
  - 输出覆盖率统计；未归类实体列入报告
  - --report 写出 reports/KG_LAYER_DOMAIN_<date>.{md,json}

用法：
  python scripts/add_kg_layer_domain.py [--strict] [--report] [--date YYYY-MM-DD]
  --strict: 存在未归类实体时 exit 1
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import shutil
import sys

import yaml

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
META = os.path.join(ROOT, "concept", "00_meta")
TAXONOMY = os.path.join(META, "taxonomy.yaml")
KG = os.path.join(META, "kg_data_v3.json")
BACKUP = KG + ".bak"


def load_taxonomy():
    with open(TAXONOMY, encoding="utf-8") as f:
        return yaml.safe_load(f)


def build_layer_map(tax):
    """directory -> layer id；extra_prefixes -> layer id。"""
    by_dir = {}
    extra = []
    default = "L0"
    for layer in tax.get("layers", []):
        by_dir[layer["directory"]] = layer["id"]
        for p in layer.get("extra_prefixes", []) or []:
            extra.append((p, layer["id"]))
    extra.sort(key=lambda x: len(x[0]), reverse=True)
    return by_dir, extra, default


def build_domain_prefixes(tax):
    """[(prefix, domain_id)] 按前缀长度降序（最长前缀匹配）。"""
    pairs = []
    for d in tax.get("domains", []):
        for p in d.get("path_prefixes", []) or []:
            pairs.append((p, d["id"]))
    pairs.sort(key=lambda x: len(x[0]), reverse=True)
    return pairs, tax.get("fallback_domain", "uncategorized")


def infer_layer(path, by_dir, extra, default):
    if not path:
        return default
    for p, lid in extra:
        if path.startswith(p):
            return lid
    first = path.split("/", 1)[0]
    return by_dir.get(first, default)


def infer_domain(path, prefixes, fallback):
    if not path:
        return fallback
    for p, did in prefixes:
        if path.startswith(p):
            return did
    return fallback


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", action="store_true",
                    help="存在未归类（fallback_domain）实体时 exit 1")
    ap.add_argument("--report", action="store_true", help="写出 reports/KG_LAYER_DOMAIN_<date>.{md,json}")
    ap.add_argument("--date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    tax = load_taxonomy()
    by_dir, extra, default_layer = build_layer_map(tax)
    prefixes, fallback = build_domain_prefixes(tax)
    domain_ids = {d["id"] for d in tax.get("domains", [])}

    with open(KG, encoding="utf-8") as f:
        kg = json.load(f)
    entities = kg.get("entities", [])

    # 备份（保留最原始备份，不因重跑覆盖）
    if not os.path.exists(BACKUP):
        shutil.copy2(KG, BACKUP)
        print(f"[backup] {os.path.relpath(BACKUP, ROOT)}")
    else:
        print(f"[backup] exists, kept: {os.path.relpath(BACKUP, ROOT)}")

    changed = 0
    unclassified = []
    layer_counts: dict[str, int] = {}
    domain_counts: dict[str, int] = {}
    matrix: dict[str, dict[str, int]] = {}

    for e in entities:
        path = (e.get("ex:path") or "").replace("\\", "/")
        layer = infer_layer(path, by_dir, extra, default_layer)
        domain = infer_domain(path, prefixes, fallback)
        if e.get("ex:layer") != layer or e.get("ex:domain") != domain:
            changed += 1
        e["ex:layer"] = layer
        e["ex:domain"] = domain
        layer_counts[layer] = layer_counts.get(layer, 0) + 1
        domain_counts[domain] = domain_counts.get(domain, 0) + 1
        matrix.setdefault(layer, {}).setdefault(domain, 0)
        matrix[layer][domain] += 1
        if domain == fallback:
            unclassified.append({"@id": e.get("@id"), "ex:path": path})

    total = len(entities)
    covered = total - len(unclassified)
    coverage = (covered / total * 100) if total else 0.0

    kg["entities"] = entities
    with open(KG, "w", encoding="utf-8") as f:
        json.dump(kg, f, ensure_ascii=False, indent=2)
        f.write("\n")

    print(f"[kg-layer-domain] entities={total} changed={changed} "
          f"coverage={coverage:.2f}% unclassified={len(unclassified)}")
    print("  layers : " + " ".join(f"{k}={v}" for k, v in sorted(layer_counts.items())))
    print("  domains: " + " ".join(f"{k}={v}" for k, v in sorted(domain_counts.items())))
    for u in unclassified[:20]:
        print(f"  UNCLASSIFIED: {u['@id']} ({u['ex:path']})")

    if args.report:
        rep_md = os.path.join(ROOT, "reports", f"KG_LAYER_DOMAIN_{args.date}.md")
        rep_json = os.path.join(ROOT, "reports", f"KG_LAYER_DOMAIN_{args.date}.json")
        with open(rep_json, "w", encoding="utf-8") as f:
            json.dump({"date": args.date, "total": total, "changed": changed,
                       "coverage_pct": round(coverage, 2),
                       "layer_counts": layer_counts, "domain_counts": domain_counts,
                       "matrix": matrix, "unclassified": unclassified},
                      f, ensure_ascii=False, indent=2)
        with open(rep_md, "w", encoding="utf-8") as f:
            f.write(f"# KG layer/domain 增强报告\n\n**日期**: {args.date}  **实体**: {total}  "
                    f"**覆盖率**: {coverage:.2f}%  **未归类**: {len(unclassified)}  **变更**: {changed}\n\n")
            f.write("## 层分布\n\n| layer | 实体数 |\n|---|:---:|\n")
            for k, v in sorted(layer_counts.items()):
                f.write(f"| {k} | {v} |\n")
            f.write("\n## 领域分布\n\n| domain | 实体数 |\n|---|:---:|\n")
            for k, v in sorted(domain_counts.items()):
                f.write(f"| {k} | {v} |\n")
            f.write("\n## 未归类实体\n\n")
            if unclassified:
                for u in unclassified:
                    f.write(f"- `{u['@id']}` — `{u['ex:path']}`\n")
            else:
                f.write("- 无\n")
        print(f"[kg-layer-domain] report: {os.path.relpath(rep_md, ROOT).replace(chr(92), '/')}")

    if args.strict and unclassified:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
