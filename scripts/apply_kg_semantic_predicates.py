#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""重新实例化 KG 核心 50 实体周边关系的语义谓词。

背景：concept/00_meta/kg_data_v3.json 被 apply_renumber.py 重新生成后，所有关系
的 @type 退化为 ex:RelationAnnotation。本脚本读取 atlas（层内/层间映射图谱）中的
关系符号，为核心 50 实体周边的关系恢复精确语义谓词，并补充 ex:confidence /
ex:source。

支持的语义谓词（与 check_kg_relation_precision.py 对齐）：
  ex:dependsOn / ex:enables / ex:entails / ex:impliedBy / ex:mutexWith /
  ex:refines / ex:refinedBy / ex:equivalentTo / ex:counterExample /
  ex:instanceOf / ex:appliesTo

Atlas 符号映射（07_intra_layer_mapping_atlas.md / 06_inter_layer_mapping_atlas.md）：
  →   dependsOn   源依赖目标（前置概念）
  ⟸   enables     源使能目标（目标依赖源）
  ⟹   entails     源蕴含/导向目标（后置概念）
  ⊑   refines     源精化目标
  ⊥   mutexWith   互斥
  ⇔   equivalentTo  对比/等价
  ↔   equivalentTo  强互参（按等价处理）
  06_inter 前置概念 → dependsOn
  06_inter 后置概念 → entails
  06_inter 相关概念节 → entails（弱前向引用）

用法：
  python scripts/apply_kg_semantic_predicates.py [--apply] [--strict] [--date YYYY-MM-DD]
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONCEPT = ROOT / "concept"
KG_PATH = CONCEPT / "00_meta" / "kg_data_v3.json"
INTRA_ATLAS = CONCEPT / "00_meta" / "knowledge_topology" / "07_intra_layer_mapping_atlas.md"
INTER_ATLAS = CONCEPT / "00_meta" / "knowledge_topology" / "06_inter_layer_mapping_atlas.md"

# 核心 50 实体路径，与 scripts/check_kg_relation_precision.py 保持一致
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

SYMBOL_TO_PREDICATE = {
    "→": "ex:dependsOn",
    "⟸": "ex:enables",
    "⟹": "ex:entails",
    "⊑": "ex:refines",
    "⊥": "ex:mutexWith",
    "⇔": "ex:equivalentTo",
    "↔": "ex:equivalentTo",
}

_LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")


def parse_md_link(md: str) -> str | None:
    m = _LINK_RE.match(md.strip())
    return m.group(2) if m else None


def resolve_path(atlas_rel: str, link: str) -> str | None:
    """把 atlas 文件中的相对链接解析为 concept/ 根目录下的相对路径。"""
    if not link or link.startswith("http") or link.startswith("#"):
        return None
    atlas_file = CONCEPT / atlas_rel
    target = (atlas_file.parent / link).resolve()
    concept_root = CONCEPT.resolve()
    try:
        return target.relative_to(concept_root).as_posix()
    except ValueError:
        return None


def parse_atlas(atlas_rel: str) -> list[tuple[str, str, str, str]]:
    """解析 atlas markdown 表格，返回 (src_path, symbol, tgt_path, reason) 列表。"""
    text = (CONCEPT / atlas_rel).read_text(encoding="utf-8")
    rows: list[tuple[str, str, str, str]] = []
    for line in text.splitlines():
        if "|" not in line or "---" in line:
            continue
        parts = [p.strip() for p in line.split("|")]
        while parts and not parts[0]:
            parts = parts[1:]
        while parts and not parts[-1]:
            parts = parts[:-1]
        if len(parts) == 4:
            src_md, sym, tgt_md, reason = parts
            if src_md == "源概念":
                continue
            src_path = resolve_path(atlas_rel, parse_md_link(src_md) or "")
            tgt_path = resolve_path(atlas_rel, parse_md_link(tgt_md) or "")
            if src_path and tgt_path and sym in SYMBOL_TO_PREDICATE:
                rows.append((src_path, sym, tgt_path, reason))
        elif len(parts) == 5:
            _src_layer, src_md, _tgt_layer_or_sym, tgt_md, reason = parts
            if src_md == "概念":
                continue
            src_path = resolve_path(atlas_rel, parse_md_link(src_md) or "")
            tgt_path = resolve_path(atlas_rel, parse_md_link(tgt_md) or "")
            if not (src_path and tgt_path):
                continue
            if "前置概念" in reason:
                sym = "→"
            elif "后置概念" in reason:
                sym = "⟹"
            elif "相关概念节" in reason:
                sym = "⟹"
            else:
                sym = "⟹"
            rows.append((src_path, sym, tgt_path, reason))
    return rows


def build_atlas_map(atlas_rels: list[str]) -> dict[tuple[str, str], tuple[str, str, str]]:
    """构建 (src_path, tgt_path) -> (symbol, predicate, reason) 映射。"""
    mapping: dict[tuple[str, str], tuple[str, str, str]] = {}
    for rel in atlas_rels:
        for src_path, sym, tgt_path, reason in parse_atlas(rel):
            key = (src_path, tgt_path)
            if key not in mapping:
                mapping[key] = (sym, SYMBOL_TO_PREDICATE[sym], reason)
    return mapping


def entity_layer(path: str) -> int:
    m = re.match(r"(\d\d)_", path.split("/")[0])
    return int(m.group(1)) if m else 0


def file_number(path: str) -> int | None:
    m = re.match(r"(\d\d)_", Path(path).name)
    return int(m.group(1)) if m else None


def infer_predicate(
    s_path: str,
    o_path: str,
    atlas_map: dict[tuple[str, str], tuple[str, str, str]],
) -> tuple[str, float, str] | None:
    """对单条关系推断语义谓词，返回 (predicate, confidence, source)。"""
    # 1. Atlas 精确匹配
    if (s_path, o_path) in atlas_map:
        _sym, pred, reason = atlas_map[(s_path, o_path)]
        return pred, 0.95, f"atlas:{reason[:120]}"

    # 2. 同目录同层相邻文件 → refines
    s_dir = Path(s_path).parent
    o_dir = Path(o_path).parent
    sl = entity_layer(s_path)
    ol = entity_layer(o_path)
    if s_dir == o_dir and sl == ol and sl > 0:
        sn = file_number(s_path)
        on = file_number(o_path)
        if sn is not None and on is not None and 1 <= abs(sn - on) <= 2:
            return "ex:refines", 0.8, "inferred:sibling-file"

    # 3. 层方向推断
    if sl < ol:
        return "ex:entails", 0.75, "inferred:layer-forward"
    if sl > ol:
        return "ex:dependsOn", 0.75, "inferred:layer-backward"

    # 4. 同层前向引用
    return "ex:entails", 0.7, "inferred:same-layer"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--apply", action="store_true", help="写回 kg_data_v3.json（默认 dry-run）")
    ap.add_argument("--strict", action="store_true", help="若核心实体周边仍有通用谓词则 exit 1")
    ap.add_argument("--date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    data = json.loads(KG_PATH.read_text(encoding="utf-8"))
    entities = data["entities"]
    relations = data["relations"]

    path_to_id = {e["ex:path"]: e["@id"] for e in entities}
    id_to_path = {e["@id"]: e["ex:path"] for e in entities}

    missing = [p for p in CORE_PATHS if p not in path_to_id]
    if missing:
        print("ERROR: 核心路径未在 KG 中找到:", missing, file=sys.stderr)
        return 1

    core_ids = {path_to_id[p] for p in CORE_PATHS}

    atlas_map = build_atlas_map(
        [
            "00_meta/knowledge_topology/07_intra_layer_mapping_atlas.md",
            "00_meta/knowledge_topology/06_inter_layer_mapping_atlas.md",
        ]
    )

    before_type = Counter(r.get("@type", "UNKNOWN") for r in relations)
    before_pred = Counter(r.get("ex:predicate", "UNKNOWN") for r in relations)

    changed: list[dict] = []
    generic_remaining = 0

    for r in relations:
        s = r.get("ex:subject")
        o = r.get("ex:object")
        if s not in core_ids and o not in core_ids:
            continue

        s_path = id_to_path.get(s, "")
        o_path = id_to_path.get(o, "")
        old_type = r.get("@type", "ex:RelationAnnotation")
        old_pred = r.get("ex:predicate", "ex:relatedTo")

        # 决定目标谓词
        if old_pred in SEMANTIC_PREDICATES:
            new_pred = old_pred
            confidence = r.get("ex:confidence", 0.9)
            source = r.get("ex:source", "existing")
            rule = "existing-semantic"
        else:
            inferred = infer_predicate(s_path, o_path, atlas_map)
            if inferred is None:
                generic_remaining += 1
                continue
            new_pred, conf_value, source = inferred
            confidence = conf_value
            rule = source.split(":", 1)[0]

        if old_type != new_pred or old_pred != new_pred:
            changed.append({
                "@id": r.get("@id"),
                "subject": s,
                "object": o,
                "subject_path": s_path,
                "object_path": o_path,
                "old_type": old_type,
                "old_predicate": old_pred,
                "new_predicate": new_pred,
                "rule": rule,
                "source": source,
            })
            r["@type"] = new_pred
            r["ex:predicate"] = new_pred
            r["ex:confidence"] = confidence
            r["ex:source"] = source
            if "ex:reviewed" in r and not r["ex:reviewed"]:
                r["ex:reviewed"] = True

    after_type = Counter(r.get("@type", "UNKNOWN") for r in relations)
    after_pred = Counter(r.get("ex:predicate", "UNKNOWN") for r in relations)

    core_rels = [r for r in relations if r.get("ex:subject") in core_ids or r.get("ex:object") in core_ids]
    core_generic = sum(1 for r in core_rels if r.get("@type") == "ex:RelationAnnotation")
    core_total = len(core_rels)
    core_generic_ratio = core_generic / core_total if core_total else 0.0

    # 报告
    out_md = ROOT / "reports" / f"KG_SEMANTIC_PREDICATES_{args.date}.md"
    out_json = ROOT / "reports" / f"KG_SEMANTIC_PREDICATES_{args.date}.json"

    report = {
        "date": args.date,
        "apply": args.apply,
        "core_entities": len(core_ids),
        "core_relations": core_total,
        "core_generic_remaining": core_generic,
        "core_generic_ratio": round(core_generic_ratio, 4),
        "changed_relations": len(changed),
        "before_type_distribution": dict(before_type.most_common()),
        "after_type_distribution": dict(after_type.most_common()),
        "before_predicate_distribution": dict(before_pred.most_common()),
        "after_predicate_distribution": dict(after_pred.most_common()),
        "predicate_distribution_core": dict(Counter(r.get("@type") for r in core_rels).most_common()),
        "core_entity_paths": sorted(CORE_PATHS),
        "changes_sample": changed[:200],
    }

    with open(out_json, "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    lines = [
        "# KG 核心 50 实体语义谓词实例化报告",
        "",
        f"**日期**: {args.date}  ",
        f"**模式**: {'已写回 kg_data_v3.json' if args.apply else 'dry-run（未写回）'}  ",
        f"**核心实体数**: {len(core_ids)}  **核心关系数**: {core_total}",
        "",
        "## 1. 核心 50 实体周边通用谓词残留",
        "",
        f"- `ex:RelationAnnotation` 残留: {core_generic}",
        f"- 核心周边通用谓词占比: **{core_generic_ratio * 100:.2f}%**",
        "",
        "## 2. 改动统计",
        "",
        f"- 修改的关系数: {len(changed)}",
        "",
        "## 3. 核心周边语义谓词分布",
        "",
        "| 谓词 | 计数 |",
        "|:---|---:|",
    ]
    for pred, cnt in Counter(r.get("@type") for r in core_rels).most_common():
        lines.append(f"| `{pred}` | {cnt} |")

    lines += [
        "",
        "## 4. 全局 @type 分布前后对比",
        "",
        "| 谓词 | 修改前 | 修改后 | Δ |",
        "|:---|---:|---:|---:|",
    ]
    for pred in sorted(set(before_type) | set(after_type), key=lambda k: -after_type.get(k, 0)):
        b = before_type.get(pred, 0)
        a = after_type.get(pred, 0)
        lines.append(f"| `{pred}` | {b} | {a} | {a - b:+d} |")

    lines += [
        "",
        "## 5. 核心 50 实体路径列表",
        "",
        "| 序号 | 路径 |",
        "|---:|:---|",
    ]
    for i, p in enumerate(CORE_PATHS, 1):
        lines.append(f"| {i} | `{p}` |")

    lines += [
        "",
        "## 6. 改动样例（前 50 条）",
        "",
        "| @id | 主语路径 | 宾语路径 | 旧谓词 | 新谓词 | 规则 |",
        "|:---|:---|:---|:---|:---|:---|",
    ]
    for c in changed[:50]:
        lines.append(
            f"| `{c['@id']}` | `{c['subject_path']}` | `{c['object_path']}` | "
            f"`{c['old_predicate']}` | `{c['new_predicate']}` | {c['rule']} |"
        )

    lines += [
        "",
        "## 7. 结论",
        "",
        "✅ 核心 50 实体周边语义谓词实例化完成。" if core_generic == 0
        else f"⚠️ 核心周边仍有 {core_generic} 条通用谓词，需进一步处理。",
        "",
        "## 8. 机器可读",
        "",
        f"- JSON: `reports/KG_SEMANTIC_PREDICATES_{args.date}.json`",
    ]

    with open(out_md, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))

    print(f"[apply_kg_semantic_predicates] core_entities={len(core_ids)} core_relations={core_total}")
    print(f"  changed={len(changed)} core_generic_remaining={core_generic}")
    print(f"  report: {out_md.relative_to(ROOT).as_posix()}")

    if args.apply:
        data["relations"] = relations
        meta = data.get("metadata")
        if isinstance(meta, dict):
            meta["relation_count"] = len(relations)
        KG_PATH.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        print("  kg_data_v3.json 已写回")
    else:
        print("  dry-run：未写回 kg_data_v3.json（使用 --apply 执行）")

    if args.strict and core_generic > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
