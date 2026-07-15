#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""KG 关系谓词精度检查（P3-4 语义质量门补充）。

检查 concept/00_meta/kg_data_v3.json：
  1. 全局 ex:RelationAnnotation 占比。
  2. 核心 50 实体周边是否至少存在一条非通用语义谓词。
  3. 核心 50 实体间语义谓词分布统计。

默认 warning（退出 0）；--strict 时若任一核心实体无语义谓词则退出 1。
输出 reports/KG_RELATION_PRECISION_<date>.{md,json}。
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import sys
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KG = os.path.join(ROOT, "concept", "00_meta", "kg_data_v3.json")

# 核心 50 实体：L1-L4 核心概念（所有权、借用、生命周期、类型系统、trait、泛型、
# 并发、async、unsafe、FFI、Pin、Send/Sync、形式化基础）。
CORE_PATHS = [
    "01_foundation/01_ownership_borrow_lifetime/01_ownership.md",
    "01_foundation/01_ownership_borrow_lifetime/02_borrowing.md",
    "01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md",
    "01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md",
    "01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md",
    "01_foundation/02_type_system/01_type_system.md",
    "01_foundation/03_values_and_references/01_reference_semantics.md",
    "01_foundation/03_values_and_references/03_variable_model.md",
    "02_intermediate/00_traits/01_traits.md",
    "02_intermediate/00_traits/02_dispatch_mechanisms.md",
    "02_intermediate/00_traits/04_advanced_traits.md",
    "02_intermediate/00_traits/06_derive_traits.md",
    "02_intermediate/00_traits/07_generic_associated_types.md",
    "02_intermediate/01_generics/01_generics.md",
    "02_intermediate/01_generics/02_const_generics.md",
    "02_intermediate/01_generics/03_type_level_programming.md",
    "02_intermediate/02_memory_management/01_memory_management.md",
    "02_intermediate/02_memory_management/02_interior_mutability.md",
    "02_intermediate/02_memory_management/04_smart_pointers.md",
    "02_intermediate/04_types_and_conversions/04_type_system_advanced.md",
    "03_advanced/00_concurrency/01_concurrency.md",
    "03_advanced/00_concurrency/02_send_sync_auto_traits.md",
    "03_advanced/00_concurrency/03_concurrency_patterns.md",
    "03_advanced/00_concurrency/06_atomics_and_memory_ordering.md",
    "03_advanced/00_concurrency/07_lock_free.md",
    "03_advanced/00_concurrency/08_parallel_distributed_pattern_spectrum.md",
    "03_advanced/01_async/01_async.md",
    "03_advanced/01_async/02_async_advanced.md",
    "03_advanced/01_async/03_async_patterns.md",
    "03_advanced/01_async/04_future_and_executor_mechanisms.md",
    "03_advanced/01_async/05_async_cancellation_safety.md",
    "03_advanced/01_async/06_async_boundary_panorama.md",
    "03_advanced/01_async/07_async_closures.md",
    "03_advanced/01_async/08_pin_unpin.md",
    "03_advanced/01_async/09_stream_algebra_and_backpressure.md",
    "03_advanced/01_async/10_executor_fairness_and_scheduling.md",
    "03_advanced/01_async/11_pin_projection_counterexamples.md",
    "03_advanced/02_unsafe/01_unsafe.md",
    "03_advanced/02_unsafe/02_unsafe_boundary_panorama.md",
    "03_advanced/02_unsafe/03_nll_and_polonius.md",
    "03_advanced/02_unsafe/04_unsafe_rust_patterns.md",
    "03_advanced/02_unsafe/06_memory_model.md",
    "03_advanced/04_ffi/01_rust_ffi.md",
    "03_advanced/04_ffi/02_ffi_advanced.md",
    "03_advanced/04_ffi/03_linkage.md",
    "03_advanced/04_ffi/04_async_ffi_boundary.md",
    "04_formal/01_ownership_logic/01_linear_logic.md",
    "04_formal/01_ownership_logic/02_ownership_formal.md",
    "04_formal/07_concurrency_semantics/01_process_calculi_for_rust.md",
    "04_formal/00_type_theory/01_type_theory.md",
]

SEMANTIC_PREDICATES = {
    "ex:dependsOn",
    "ex:enables",
    "ex:entails",
    "ex:impliedBy",
    "ex:mutexWith",
    "ex:refines",
    "ex:refinedBy",
    "ex:equivalentTo",
    "ex:counterExample",
    "ex:instanceOf",
    "ex:appliesTo",
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--out-date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    data = json.load(open(KG, encoding="utf-8"))
    entities = data.get("entities", [])
    relations = data.get("relations", [])

    path_to_id = {e["ex:path"]: e["@id"] for e in entities}
    id_to_path = {e["@id"]: e["ex:path"] for e in entities}
    core_ids = {path_to_id[p] for p in CORE_PATHS if p in path_to_id}
    missing_core_paths = [p for p in CORE_PATHS if p not in path_to_id]

    # Global predicate distribution based on @type (the instantiated RDF predicate)
    global_type_counts = Counter(r.get("@type", "UNKNOWN") for r in relations)
    total = len(relations)
    generic_count = global_type_counts.get("ex:RelationAnnotation", 0)
    generic_ratio = generic_count / total if total else 0.0

    # Core-50 coverage
    core_relations = [r for r in relations if r.get("ex:subject") in core_ids or r.get("ex:object") in core_ids]
    core_type_counts = Counter(r.get("@type", "UNKNOWN") for r in core_relations)
    core_total = len(core_relations)
    core_generic_count = core_type_counts.get("ex:RelationAnnotation", 0)
    core_generic_ratio = core_generic_count / core_total if core_total else 0.0

    per_entity_semantic = {eid: [] for eid in core_ids}
    for r in core_relations:
        pred = r.get("@type", "")
        if pred in SEMANTIC_PREDICATES:
            for end in (r.get("ex:subject"), r.get("ex:object")):
                if end in core_ids:
                    per_entity_semantic[end].append(pred)

    lacking = [eid for eid in sorted(core_ids) if not per_entity_semantic[eid]]

    summary = {
        "date": args.out_date,
        "total_relations": total,
        "generic_relation_annotation_count": generic_count,
        "generic_ratio_global": round(generic_ratio, 4),
        "core_entities": len(core_ids),
        "core_relations": core_total,
        "core_generic_count": core_generic_count,
        "core_generic_ratio": round(core_generic_ratio, 4),
        "core_lacking_semantic": len(lacking),
        "global_predicate_distribution": dict(global_type_counts.most_common()),
        "core_predicate_distribution": dict(core_type_counts.most_common()),
    }

    out_md = os.path.join(ROOT, "reports", f"KG_RELATION_PRECISION_{args.out_date}.md")
    out_json = os.path.join(ROOT, "reports", f"KG_RELATION_PRECISION_{args.out_date}.json")

    with open(out_json, "w", encoding="utf-8") as f:
        json.dump(
            {
                "summary": summary,
                "core_entities": sorted(core_ids),
                "missing_core_paths": missing_core_paths,
                "lacking_semantic_entities": sorted(lacking),
                "per_entity_semantic_sample": {
                    eid: Counter(per_entity_semantic[eid]).most_common(3)
                    for eid in sorted(core_ids)
                },
            },
            f,
            ensure_ascii=False,
            indent=2,
        )

    with open(out_md, "w", encoding="utf-8") as f:
        f.write("# KG 关系谓词精度基线报告\n\n")
        f.write(f"**日期**: {args.out_date}  ")
        f.write(f"**总关系数**: {total}  ")
        f.write(f"**核心 50 实体关系数**: {core_total}  ")
        f.write(f"**核心实体数**: {len(core_ids)}\n\n")

        f.write("## 1. 全局 ex:RelationAnnotation 占比\n\n")
        f.write(f"- `ex:RelationAnnotation` 数量: {generic_count}\n")
        f.write(f"- 全局通用谓词占比: **{generic_ratio*100:.2f}%**\n")
        f.write(f"- 核心 50 周边通用谓词占比: **{core_generic_ratio*100:.2f}%**\n\n")

        f.write("## 2. 核心 50 实体语义谓词覆盖\n\n")
        f.write(f"- 至少有一条语义谓词的核心实体: {len(core_ids) - len(lacking)} / {len(core_ids)}\n")
        if lacking:
            f.write(f"- ❌ 缺语义谓词的核心实体 ({len(lacking)}):\n")
            for eid in sorted(lacking):
                f.write(f"  - `{eid}` ({id_to_path.get(eid, '')})\n")
        else:
            f.write("- ✅ 全部核心实体周边至少存在一条语义谓词\n")
        f.write("\n")

        f.write("## 3. 核心 50 实体语义谓词分布\n\n")
        f.write("| 谓词 | 计数 | 占比（核心） |\n")
        f.write("|:---|---:|---:|\n")
        for pred, cnt in core_type_counts.most_common():
            ratio = cnt / core_total * 100 if core_total else 0.0
            f.write(f"| `{pred}` | {cnt} | {ratio:.2f}% |\n")
        f.write("\n")

        f.write("## 4. 核心 50 实体列表\n\n")
        f.write("| @id | ex:path |\n")
        f.write("|:---|:---|\n")
        for eid in sorted(core_ids):
            f.write(f"| `{eid}` | {id_to_path.get(eid, '')} |\n")
        f.write("\n")

        f.write("## 5. 检查结论\n\n")
        if lacking:
            f.write("**结论**: 存在核心实体没有语义谓词，需补充。\n")
        else:
            f.write("**结论**: 核心 50 实体均已实例化至少一条语义谓词。\n")
        f.write(f"\n## 6. 机器可读\n\n- JSON: `reports/KG_RELATION_PRECISION_{args.out_date}.json`\n")

    print(f"[KG relation precision] total_relations={total} generic_ratio={generic_ratio*100:.2f}%")
    print(f"  core_entities={len(core_ids)} core_relations={core_total} core_generic_ratio={core_generic_ratio*100:.2f}%")
    print(f"  core_lacking_semantic={len(lacking)}")
    print(f"  report: {os.path.relpath(out_md, ROOT).replace(chr(92), '/')}")

    if args.strict and lacking:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
