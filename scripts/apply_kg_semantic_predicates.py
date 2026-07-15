#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""为 KG 实体批次重新实例化语义谓词。

背景：concept/00_meta/kg_data_v3.json 被 apply_renumber.py 重新生成后，所有关系
的 @type 退化为 ex:RelationAnnotation。本脚本读取 atlas（层内/层间映射图谱）中的
关系符号，为指定批次实体周边的关系恢复精确语义谓词，并补充 ex:confidence /
ex:source。

支持的语义谓词（与 check_kg_relation_precision.py 对齐）：
  ex:dependsOn / ex:enables / ex:entails / ex:impliedBy / ex:mutexWith /
  ex:refines / ex:refinedBy / ex:equivalentTo / ex:counterExample /
  ex:instanceOf / ex:appliesTo / ex:relatedTo

新增批次（2026-07-15）：
  meta_navigation : 00_meta/knowledge_topology/ + 00_meta/04_navigation/ + SUMMARY.md
  ecosystem       : 06_ecosystem/（含 cargo，覆盖设计模式、领域应用等）
  future          : 07_future/（不含 archive）
  rustc_internals : 04_formal/05_rustc_internals/
  framework       : 00_meta/00_framework/

导航/图谱边专用谓词：
  ex:relatedTo — 用于 atlas、导航索引、SUMMARY.md 等弱语义连接，
  作为消除 ex:RelationAnnotation 的兜底谓词。

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

额外高置信度信号：
  - ex:source 以 "prerequisite:" 开头 → ex:dependsOn
  - ex:source 以 "postrequisite:" 开头 → ex:entails
  - 对称谓词（mutexWith / equivalentTo）支持反向 atlas 查找

用法：
  python scripts/apply_kg_semantic_predicates.py [--apply] [--strict]
       [--batch core|l1|l2|async|unsafe|formal|meta_navigation|ecosystem|future|rustc_internals|framework]
       [--all-batches]
       [--min-confidence 0.75] [--date YYYY-MM-DD]

默认（无 --batch / --all-batches）仅处理核心 50 实体，保持与旧版本兼容。
meta_navigation / ecosystem / future / rustc_internals / framework 建议置信度 0.65。
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

BATCH_DEFINITIONS = {
    "l1": ["01_foundation/"],
    "l2": ["02_intermediate/"],
    "async": ["03_advanced/01_async/"],
    "unsafe": ["03_advanced/02_unsafe/"],
    "formal": ["04_formal/"],
    "l5": [
        "05_comparative/00_paradigms/",
        "05_comparative/01_systems_languages/",
        "05_comparative/02_managed_languages/",
        "05_comparative/03_domain_comparisons/",
    ],
    "l6_concept": [
        "06_ecosystem/00_toolchain/",
        "06_ecosystem/02_core_crates/",
        "06_ecosystem/03_design_patterns/",
        "06_ecosystem/04_web_and_networking/",
        "06_ecosystem/05_systems_and_embedded/",
        "06_ecosystem/06_data_and_distributed/",
        "06_ecosystem/07_security_and_cryptography/",
        "06_ecosystem/08_formal_verification/",
        "06_ecosystem/09_testing_and_quality/",
        "06_ecosystem/10_performance/",
        "06_ecosystem/11_domain_applications/",
        "06_ecosystem/12_networking/",
    ],
    "l7": [
        "07_future/00_version_tracking/",
        "07_future/01_edition_roadmap/",
        "07_future/02_preview_features/",
        "07_future/04_research_and_experimental/",
    ],
    "l3_rem": [
        "03_advanced/00_concurrency/",
        "03_advanced/03_proc_macros/",
        "03_advanced/05_inline_assembly/",
        "03_advanced/06_low_level_patterns/",
        "03_advanced/07_unsafe_internals/",
        "03_advanced/08_process_ipc/",
    ],
    "meta_navigation": [
        "00_meta/knowledge_topology/",
        "00_meta/04_navigation/",
        "SUMMARY.md",
    ],
    "ecosystem": [
        "06_ecosystem/",
    ],
    "future": [
        "07_future/",
    ],
    "rustc_internals": [
        "04_formal/05_rustc_internals/",
    ],
    "framework": [
        "00_meta/00_framework/",
    ],
}

# 始终排除的低价值路径（quiz、README、归档）
BASE_EXCLUDED_PATH_REGEXES = [
    re.compile(r"/\d\d_quizzes/"),
    re.compile(r"(^|/)README\.md$"),
    re.compile(r"^07_future/archive/"),
]

# 仅在批次未显式覆盖时排除的路径
CONDITIONAL_EXCLUDED_PATH_REGEXES = {
    "00_meta": re.compile(r"^00_meta/"),
    "summary": re.compile(r"(^|/)SUMMARY\.md$"),
    "cargo": re.compile(r"^06_ecosystem/01_cargo/"),
    "ecosystem_quizzes": re.compile(r"^06_ecosystem/13_quizzes/"),
}

# 导航/图谱边路径前缀（用于兜底 ex:relatedTo）
NAVIGATION_PATH_PREFIXES = (
    "00_meta/knowledge_topology/",
    "00_meta/04_navigation/",
    "SUMMARY.md",
)


def batch_overrides(batch_names: list[str]) -> set[str]:
    """根据当前处理批次决定允许哪些条件排除项。"""
    overrides = set()
    if "meta_navigation" in batch_names:
        overrides |= {"00_meta", "summary"}
    if "framework" in batch_names:
        overrides |= {"00_meta"}
    if "ecosystem" in batch_names:
        overrides |= {"cargo", "ecosystem_quizzes"}
    return overrides


def is_excluded_path(path: str, overrides: set[str] | None = None) -> bool:
    overrides = overrides or set()
    for rx in BASE_EXCLUDED_PATH_REGEXES:
        if rx.search(path):
            return True
    for key, rx in CONDITIONAL_EXCLUDED_PATH_REGEXES.items():
        if key not in overrides and rx.search(path):
            return True
    return False


def is_navigation_path(path: str) -> bool:
    return path.startswith(NAVIGATION_PATH_PREFIXES)

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
    "ex:relatedTo",
}

# 对称谓词：关系方向反转后谓词不变
SYMMETRIC_PREDICATES = {"ex:mutexWith", "ex:equivalentTo"}

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
    """构建 (src_path, tgt_path) -> (symbol, predicate, reason) 映射。

    对对称谓词同时注册反向键，以便 KG 中的反向关系也能命中 atlas。
    """
    mapping: dict[tuple[str, str], tuple[str, str, str]] = {}
    for rel in atlas_rels:
        for src_path, sym, tgt_path, reason in parse_atlas(rel):
            key = (src_path, tgt_path)
            if key not in mapping:
                pred = SYMBOL_TO_PREDICATE[sym]
                mapping[key] = (sym, pred, reason)
                if pred in SYMMETRIC_PREDICATES:
                    rev = (tgt_path, src_path)
                    if rev not in mapping:
                        mapping[rev] = (sym, pred, reason)
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
    source_value: object | None,
) -> tuple[str, float, str] | None:
    """对单条关系推断语义谓词，返回 (predicate, confidence, source) 三元组。"""
    source_str = ""
    if isinstance(source_value, str):
        source_str = source_value

    # 1. Atlas 精确匹配（含对称谓词反向查找）
    if (s_path, o_path) in atlas_map:
        _sym, pred, reason = atlas_map[(s_path, o_path)]
        return pred, 0.95, f"atlas:{reason[:120]}"

    # 2. 高置信度 source 信号
    if source_str.startswith("prerequisite:"):
        return "ex:dependsOn", 0.9, "inferred:source-prerequisite"
    if source_str.startswith("postrequisite:"):
        return "ex:entails", 0.9, "inferred:source-postrequisite"

    # 3. 导航/图谱/索引页 → relatedTo（兜底消除 RelationAnnotation）
    if is_navigation_path(s_path) or is_navigation_path(o_path):
        return "ex:relatedTo", 0.72, "inferred:navigation-link"

    # 4. 同目录同层相邻文件 → refines
    s_dir = Path(s_path).parent
    o_dir = Path(o_path).parent
    sl = entity_layer(s_path)
    ol = entity_layer(o_path)
    if s_dir == o_dir and sl == ol and sl > 0:
        sn = file_number(s_path)
        on = file_number(o_path)
        if sn is not None and on is not None and 1 <= abs(sn - on) <= 2:
            return "ex:refines", 0.8, "inferred:sibling-file"

    # 5. 层方向推断
    if sl < ol:
        return "ex:entails", 0.75, "inferred:layer-forward"
    if sl > ol:
        return "ex:dependsOn", 0.75, "inferred:layer-backward"

    # 6. 同层前向引用（置信度低于默认阈值，通常不写入）
    return "ex:entails", 0.7, "inferred:same-layer"


def select_batches(args: argparse.Namespace) -> tuple[list[str], dict[str, list[str]]]:
    """根据命令行参数返回要处理的批次名称与路径前缀映射。"""
    if args.all_batches:
        return list(BATCH_DEFINITIONS.keys()), dict(BATCH_DEFINITIONS)
    if args.batch:
        names = [b.strip().lower() for b in args.batch.split(",") if b.strip()]
        invalid = [n for n in names if n not in BATCH_DEFINITIONS]
        if invalid:
            raise ValueError(f"未知批次: {invalid}; 可用: {list(BATCH_DEFINITIONS.keys())}")
        return names, {n: BATCH_DEFINITIONS[n] for n in names}
    # 默认：核心 50 实体（兼容旧行为）
    return ["core"], {"core": [""]}


def collect_entity_ids(
    entities: list[dict],
    batches: dict[str, list[str]],
    overrides: set[str],
) -> dict[str, set[str]]:
    """为每个批次收集实体 @id；'core' 使用固定路径列表。

    按批次覆盖条件排除项，允许 meta_navigation / framework / ecosystem 等
    批次处理原本被屏蔽的 00_meta、SUMMARY.md、cargo 等路径。
    """
    path_to_id = {e["ex:path"]: e["@id"] for e in entities}
    result: dict[str, set[str]] = {}
    for name, prefixes in batches.items():
        if isinstance(prefixes, str):
            prefixes = [prefixes]
        if name == "core":
            ids = {path_to_id[p] for p in CORE_PATHS if p in path_to_id and not is_excluded_path(p, overrides)}
        else:
            ids = set()
            for prefix in prefixes:
                ids.update(
                    path_to_id[p]
                    for p in path_to_id
                    if p.startswith(prefix) and not is_excluded_path(p, overrides)
                )
        result[name] = ids
    return result


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--apply", action="store_true", help="写回 kg_data_v3.json（默认 dry-run）")
    ap.add_argument("--strict", action="store_true", help="若被处理批次周边仍有通用谓词则 exit 1")
    ap.add_argument("--batch", default=None, help="处理指定批次，逗号分隔，如 l1,l2,async,unsafe,formal")
    ap.add_argument("--all-batches", action="store_true", help="处理全部扩展批次（含 l1/l2/async/unsafe/formal/meta_navigation/ecosystem/future/rustc_internals/framework）")
    ap.add_argument("--min-confidence", type=float, default=0.75, help="仅写入置信度不低于此阈值的关系")
    ap.add_argument("--date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    data = json.loads(KG_PATH.read_text(encoding="utf-8"))
    entities = data["entities"]
    relations = data["relations"]

    path_to_id = {e["ex:path"]: e["@id"] for e in entities}
    id_to_path = {e["@id"]: e["ex:path"] for e in entities}

    try:
        batch_names, batch_defs = select_batches(args)
    except ValueError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2

    overrides = batch_overrides(batch_names)
    batch_to_ids = collect_entity_ids(entities, batch_defs, overrides)
    processed_ids = set().union(*batch_to_ids.values())

    if "core" in batch_names:
        missing = [p for p in CORE_PATHS if p not in path_to_id]
        if missing:
            print("ERROR: 核心路径未在 KG 中找到:", missing, file=sys.stderr)
            return 1

    atlas_map = build_atlas_map(
        [
            "00_meta/knowledge_topology/07_intra_layer_mapping_atlas.md",
            "00_meta/knowledge_topology/06_inter_layer_mapping_atlas.md",
        ]
    )

    before_type = Counter(r.get("@type", "UNKNOWN") for r in relations)
    before_pred = Counter(r.get("ex:predicate", "UNKNOWN") for r in relations)

    changed: list[dict] = []
    below_threshold = 0
    generic_remaining = 0

    for r in relations:
        s = r.get("ex:subject")
        o = r.get("ex:object")
        if s not in processed_ids and o not in processed_ids:
            continue

        s_path = id_to_path.get(s, "")
        o_path = id_to_path.get(o, "")
        if not s_path or not o_path:
            continue
        if is_excluded_path(s_path, overrides) or is_excluded_path(o_path, overrides):
            continue
        old_type = r.get("@type", "ex:RelationAnnotation")
        old_pred = r.get("ex:predicate", "ex:relatedTo")

        # 决定目标谓词
        if old_pred in SEMANTIC_PREDICATES:
            new_pred = old_pred
            confidence = r.get("ex:confidence", 0.9)
            source = r.get("ex:source", "existing")
            rule = "existing-semantic"
        else:
            inferred = infer_predicate(s_path, o_path, atlas_map, r.get("ex:source"))
            if inferred is None:
                generic_remaining += 1
                continue
            new_pred, conf_value, source = inferred
            if conf_value < args.min_confidence:
                below_threshold += 1
                generic_remaining += 1
                continue
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
                "confidence": confidence,
            })
            r["@type"] = new_pred
            r["ex:predicate"] = new_pred
            r["ex:confidence"] = confidence
            r["ex:source"] = source
            if "ex:reviewed" in r and not r["ex:reviewed"]:
                r["ex:reviewed"] = True

    after_type = Counter(r.get("@type", "UNKNOWN") for r in relations)
    after_pred = Counter(r.get("ex:predicate", "UNKNOWN") for r in relations)

    # 各批次统计
    batch_stats: list[dict] = []
    for name in batch_names:
        ids = batch_to_ids[name]
        batch_rels = [r for r in relations if r.get("ex:subject") in ids or r.get("ex:object") in ids]
        generic = sum(1 for r in batch_rels if r.get("@type") == "ex:RelationAnnotation")
        batch_stats.append({
            "batch": name,
            "entities": len(ids),
            "relations": len(batch_rels),
            "generic_remaining": generic,
            "generic_ratio": round(generic / len(batch_rels), 4) if batch_rels else 0.0,
        })

    total_processed_rels = sum(s["relations"] for s in batch_stats)
    total_generic_remaining = sum(s["generic_remaining"] for s in batch_stats)

    # 报告
    out_md = ROOT / "reports" / f"KG_SEMANTIC_PREDICATES_{args.date}.md"
    out_json = ROOT / "reports" / f"KG_SEMANTIC_PREDICATES_{args.date}.json"

    report = {
        "date": args.date,
        "apply": args.apply,
        "batches": batch_names,
        "min_confidence": args.min_confidence,
        "processed_entities": len(processed_ids),
        "processed_relations": total_processed_rels,
        "processed_generic_remaining": total_generic_remaining,
        "changed_relations": len(changed),
        "below_threshold_skipped": below_threshold,
        "batch_statistics": batch_stats,
        "before_type_distribution": dict(before_type.most_common()),
        "after_type_distribution": dict(after_type.most_common()),
        "before_predicate_distribution": dict(before_pred.most_common()),
        "after_predicate_distribution": dict(after_pred.most_common()),
        "changes_sample": changed[:200],
    }

    with open(out_json, "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)

    lines = [
        f"# KG 语义谓词实例化报告（{', '.join(batch_names)}）",
        "",
        f"**日期**: {args.date}  ",
        f"**模式**: {'已写回 kg_data_v3.json' if args.apply else 'dry-run（未写回）'}  ",
        f"**置信度阈值**: {args.min_confidence}  ",
        f"**处理实体数**: {len(processed_ids)}  **处理关系数**: {total_processed_rels}",
        "",
        "## 1. 各批次通用谓词残留",
        "",
        "| 批次 | 实体数 | 关系数 | 通用谓词残留 | 占比 |",
        "|:---|---:|---:|---:|---:|",
    ]
    for s in batch_stats:
        lines.append(
            f"| `{s['batch']}` | {s['entities']} | {s['relations']} | "
            f"{s['generic_remaining']} | {s['generic_ratio'] * 100:.2f}% |"
        )
    lines += [
        "",
        f"- 处理批次内通用谓词总计残留: **{total_generic_remaining}**",
        f"- 因低于置信度阈值跳过: **{below_threshold}**",
        "",
        "## 2. 改动统计",
        "",
        f"- 修改的关系数: {len(changed)}",
        "",
        "## 3. 全局 @type 分布前后对比",
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
        "## 4. 改动样例（前 50 条）",
        "",
        "| @id | 主语路径 | 宾语路径 | 旧谓词 | 新谓词 | 规则 | 置信度 |",
        "|:---|:---|:---|:---|:---|:---|---:|",
    ]
    for c in changed[:50]:
        lines.append(
            f"| `{c['@id']}` | `{c['subject_path']}` | `{c['object_path']}` | "
            f"`{c['old_predicate']}` | `{c['new_predicate']}` | {c['rule']} | {c['confidence']:.2f} |"
        )

    lines += [
        "",
        "## 5. 结论",
        "",
        "✅ 语义谓词实例化完成。" if total_generic_remaining == 0
        else f"⚠️ 处理批次内仍有 {total_generic_remaining} 条通用谓词（低于阈值 {below_threshold} 条），需进一步处理。",
        "",
        "## 6. 机器可读",
        "",
        f"- JSON: `reports/KG_SEMANTIC_PREDICATES_{args.date}.json`",
    ]

    with open(out_md, "w", encoding="utf-8") as f:
        f.write("\n".join(lines))

    print(f"[apply_kg_semantic_predicates] batches={batch_names} processed_entities={len(processed_ids)}")
    print(f"  processed_relations={total_processed_rels} changed={len(changed)} below_threshold={below_threshold}")
    print(f"  generic_remaining={total_generic_remaining} report: {out_md.relative_to(ROOT).as_posix()}")

    if args.apply:
        data["relations"] = relations
        meta = data.get("metadata")
        if isinstance(meta, dict):
            meta["relation_count"] = len(relations)
        KG_PATH.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")
        print("  kg_data_v3.json 已写回")
    else:
        print("  dry-run：未写回 kg_data_v3.json（使用 --apply 执行）")

    if args.strict and total_generic_remaining > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
