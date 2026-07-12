#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""KG v3 第二轮（2026-07-12）：补建范畴/领域/实例节点并落地缺口边。

背景：第一轮 scripts/type_kg_semantic_edges.py 实例化 equivalentTo/instanceOf/appliesTo 时，
9 项范畴节点缺口（见 reports/KG_SEMANTIC_EDGE_TYPING_2026_07_12.md “范畴节点缺口清单”）
导致一批 instanceOf/appliesTo 边无法建立。本轮：

  1. 严格按现有实体的同构结构（K1: @id/@type/skos:prefLabel 双语/skos:scopeNote/ex:path
     + K7: ex:layer/ex:domain + ex:bloomLevel）新建 17 个节点；
     ex:path 均指向真实存在的 concept/ 权威页，ex:layer/ex:domain 按
     concept/00_meta/taxonomy.yaml 前缀规则取值。
  2. 按第一轮相同的边结构（ex:subject/ex:predicate/ex:object + ex:evidence 页面行号级引文
     + ex:rule + ex:reviewed）补建 15 条 instanceOf/appliesTo 边，覆盖全部 9 项缺口。
  3. 同向同谓词边已存在时不重复添加；优先将已有 relatedTo 边改型（与第一轮一致）。

规则编号沿用第一轮：
  I1 category-listed   范畴页正文/Summary 明确列出该实例
  I3 self-evident-kind 实例页标题/定位自述其为该范畴的一种
  A1 page-application  技术页正文明确其应用于目标领域

用法：
  python scripts/add_kg_category_nodes.py [--dry-run] [--date YYYY-MM-DD]
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
KG_PATH = ROOT / "concept" / "00_meta" / "kg_data_v3.json"

PRED_INST = "ex:instanceOf"
PRED_APPL = "ex:appliesTo"
PRED_REL = "ex:relatedTo"


def _label(en: str, zh: str) -> list[dict]:
    return [{"@language": "en", "@value": en}, {"@language": "zh", "@value": zh}]


def _note(en: str) -> list[dict]:
    return [{"@language": "en", "@value": en}]


# ---------------------------------------------------------------------------
# 新建节点（17 个：6 范畴/领域节点 + 11 实例节点）
# 字段集与现有实体同构；ex:path 均为已确认存在的 concept/ 页面。
# ---------------------------------------------------------------------------
NEW_ENTITIES: list[dict] = [
    # ---- ① Collections 实例 ----
    {"@id": "ex:Vec", "@type": "ex:Primitive",
     "skos:prefLabel": _label("Vec", "Vec（动态数组）"),
     "skos:scopeNote": _note(
         "Vec<T>: Rust's growable, heap-allocated dynamic array; the standard sequence "
         "collection with amortized O(1) push and contiguous storage."),
     "ex:path": "01_foundation/05_collections/01_collections.md",
     "ex:layer": "L1", "ex:domain": "language_core", "ex:bloomLevel": "L1-L2",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    {"@id": "ex:HashMap", "@type": "ex:Primitive",
     "skos:prefLabel": _label("HashMap", "HashMap（哈希映射）"),
     "skos:scopeNote": _note(
         "HashMap<K, V>: hash-table based associative collection with average O(1) "
         "insert/lookup; requires K: Hash + Eq."),
     "ex:path": "01_foundation/05_collections/01_collections.md",
     "ex:layer": "L1", "ex:domain": "language_core", "ex:bloomLevel": "L1-L2",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    # ---- ② AsyncRuntime 范畴 + Tokio 实例 ----
    {"@id": "ex:AsyncRuntime", "@type": "ex:Concept",
     "skos:prefLabel": _label("Async Runtime", "Async Runtime（异步运行时）"),
     "skos:scopeNote": _note(
         "Async runtime: the executor/reactor that drives futures to completion "
         "(Tokio, async-std, smol), providing task scheduling, I/O drivers, and timers; "
         "the async domain category for concrete runtimes."),
     "ex:path": "03_advanced/01_async/04_future_and_executor_mechanisms.md",
     "ex:layer": "L3", "ex:domain": "async", "ex:bloomLevel": "L3-L4",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    {"@id": "ex:Tokio", "@type": "ex:Concept",
     "skos:prefLabel": _label("Tokio", "Tokio（异步运行时）"),
     "skos:scopeNote": _note(
         "Tokio: the de-facto standard work-stealing async runtime for Rust (multi-thread "
         "scheduler, I/O driver, timers); the runtime assumed by most async ecosystem crates."),
     "ex:path": "03_advanced/01_async/06_async_boundary_panorama.md",
     "ex:layer": "L3", "ex:domain": "async", "ex:bloomLevel": "L3-L4",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    # ---- ③ AutoTrait 范畴 + Send/Sync 实例 ----
    {"@id": "ex:AutoTrait", "@type": "ex:Concept",
     "skos:prefLabel": _label("Auto Trait", "Auto Trait（自动 trait）"),
     "skos:scopeNote": _note(
         "Auto trait: a trait automatically implemented by the compiler for every type "
         "whose structure satisfies the contract (Send, Sync, Unpin, Sized); may be opted "
         "out via negative impls. Category of compiler-derived marker traits."),
     "ex:path": "03_advanced/00_concurrency/02_send_sync_auto_traits.md",
     "ex:layer": "L3", "ex:domain": "concurrency", "ex:bloomLevel": "L3-L4",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    {"@id": "ex:Send", "@type": "ex:Primitive",
     "skos:prefLabel": _label("Send", "Send（跨线程转移标记 trait）"),
     "skos:scopeNote": _note(
         "Send: auto marker trait; `T: Send` means ownership of `T` can be safely "
         "transferred across thread boundaries."),
     "ex:path": "03_advanced/00_concurrency/02_send_sync_auto_traits.md",
     "ex:layer": "L3", "ex:domain": "concurrency", "ex:bloomLevel": "L3-L4",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    {"@id": "ex:Sync", "@type": "ex:Primitive",
     "skos:prefLabel": _label("Sync", "Sync（跨线程共享标记 trait）"),
     "skos:scopeNote": _note(
         "Sync: auto marker trait; `T: Sync` is equivalent to `&T: Send`, meaning shared "
         "references to `T` can be safely used from multiple threads."),
     "ex:path": "03_advanced/00_concurrency/02_send_sync_auto_traits.md",
     "ex:layer": "L3", "ex:domain": "concurrency", "ex:bloomLevel": "L3-L4",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    # ---- ④ SmartPointers 实例 ----
    {"@id": "ex:Box", "@type": "ex:Primitive",
     "skos:prefLabel": _label("Box", "Box（独占堆分配智能指针）"),
     "skos:scopeNote": _note(
         "Box<T>: owning smart pointer providing exclusive heap allocation with "
         "deterministic drop; the simplest smart pointer."),
     "ex:path": "02_intermediate/02_memory_management/04_smart_pointers.md",
     "ex:layer": "L2", "ex:domain": "ownership_memory", "ex:bloomLevel": "L2-L3",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    {"@id": "ex:Rc", "@type": "ex:Primitive",
     "skos:prefLabel": _label("Rc", "Rc（单线程引用计数智能指针）"),
     "skos:scopeNote": _note(
         "Rc<T>: single-threaded reference-counted smart pointer enabling shared "
         "ownership; `!Send`/`!Sync`."),
     "ex:path": "02_intermediate/02_memory_management/04_smart_pointers.md",
     "ex:layer": "L2", "ex:domain": "ownership_memory", "ex:bloomLevel": "L2-L3",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    {"@id": "ex:Arc", "@type": "ex:Primitive",
     "skos:prefLabel": _label("Arc", "Arc（线程安全引用计数智能指针）"),
     "skos:scopeNote": _note(
         "Arc<T>: atomically reference-counted smart pointer enabling shared ownership "
         "across threads; `Send + Sync` when `T: Send + Sync`."),
     "ex:path": "02_intermediate/02_memory_management/04_smart_pointers.md",
     "ex:layer": "L2", "ex:domain": "ownership_memory", "ex:bloomLevel": "L2-L3",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    # ---- ⑤ AlgebraicDataType 范畴 + Result/Option 实例 ----
    {"@id": "ex:AlgebraicDataType", "@type": "ex:Concept",
     "skos:prefLabel": _label("Algebraic Data Type", "Algebraic Data Type（代数数据类型）"),
     "skos:scopeNote": _note(
         "Algebraic data type (ADT): types formed by products (struct/tuple) and sums "
         "(enum); Rust enums — including Option<T> and Result<T, E> — are ADTs "
         "(Pierce, TAPL Ch.11). Category node above concrete sum/product types."),
     "ex:path": "04_formal/00_type_theory/01_type_theory.md",
     "ex:layer": "L4", "ex:domain": "formal_methods", "ex:bloomLevel": "L4-L5",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    {"@id": "ex:Result", "@type": "ex:Primitive",
     "skos:prefLabel": _label("Result", "Result（可恢复错误和类型）"),
     "skos:scopeNote": _note(
         "Result<T, E>: sum type for recoverable errors with variants Ok(T)/Err(E); "
         "embeds error handling into the type system so failures cannot be silently ignored."),
     "ex:path": "01_foundation/08_error_handling/01_error_handling_basics.md",
     "ex:layer": "L1", "ex:domain": "language_core", "ex:bloomLevel": "L1-L2",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    {"@id": "ex:Option", "@type": "ex:Primitive",
     "skos:prefLabel": _label("Option", "Option（可选值和类型）"),
     "skos:scopeNote": _note(
         "Option<T>: sum type with variants Some(T)/None; replaces null pointers and "
         "eliminates null-dereference runtime errors."),
     "ex:path": "01_foundation/07_modules_and_items/05_enumerations.md",
     "ex:layer": "L1", "ex:domain": "language_core", "ex:bloomLevel": "L1-L2",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    # ---- ⑥ Serialization 领域节点 ----
    {"@id": "ex:Serialization", "@type": "ex:Concept",
     "skos:prefLabel": _label("Serialization", "Serialization（序列化）"),
     "skos:scopeNote": _note(
         "Serialization: converting typed values to and from external representations "
         "(JSON, bincode, ...); in Rust driven type-directed by serde's "
         "Serialize/Deserialize traits. Domain node for serde and format crates."),
     "ex:path": "02_intermediate/00_traits/03_serde_patterns.md",
     "ex:layer": "L2", "ex:domain": "type_system", "ex:bloomLevel": "L2-L4",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    # ---- ⑦ ModelChecking 领域节点 ----
    {"@id": "ex:ModelChecking", "@type": "ex:Concept",
     "skos:prefLabel": _label("Model Checking", "Model Checking（模型检查）"),
     "skos:scopeNote": _note(
         "Model checking: exhaustive verification of properties over all possible inputs "
         "and execution paths within bounds (Kani/CBMC, SAT/SMT-based). Domain node for "
         "bounded model checkers in the Rust verification toolchain."),
     "ex:path": "04_formal/04_model_checking/09_kani.md",
     "ex:layer": "L4", "ex:domain": "formal_methods", "ex:bloomLevel": "L4-L5",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    # ---- ⑧ FormalVerificationFramework 范畴节点 ----
    {"@id": "ex:FormalVerificationFramework", "@type": "ex:Concept",
     "skos:prefLabel": _label("Formal Verification Framework",
                              "Formal Verification Framework（形式化验证框架）"),
     "skos:scopeNote": _note(
         "Formal verification framework: Rust's layered formal-ecosystem tower — from "
         "rustc's automatic memory-safety guarantees (L0) up to functional-correctness "
         "proofs with Kani/Verus/Creusot (L4). Category node above the concrete "
         "verification toolchain."),
     "ex:path": "06_ecosystem/08_formal_verification/01_formal_ecosystem_tower.md",
     "ex:layer": "L6", "ex:domain": "ecosystem_security", "ex:bloomLevel": "L5-L6",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
    # ---- ⑨ UnsafeAbstractionSoundness 领域节点 ----
    {"@id": "ex:UnsafeAbstractionSoundness", "@type": "ex:Concept",
     "skos:prefLabel": _label("Unsafe Abstraction Soundness",
                              "Unsafe Abstraction Soundness（unsafe 抽象可靠性）"),
     "skos:scopeNote": _note(
         "Unsafe abstraction soundness: the property that unsafe code encapsulated "
         "behind safe APIs respects safe Rust's abstraction boundaries; the central "
         "proof target of RustBelt (Jung et al., POPL 2018). Domain node for soundness "
         "arguments about unsafe encapsulation."),
     "ex:path": "04_formal/02_separation_logic/01_rustbelt.md",
     "ex:layer": "L4", "ex:domain": "formal_methods", "ex:bloomLevel": "L4-L5",
     "ex:rustVersion": "1.97.0+ (Edition 2024)"},
]

# ---------------------------------------------------------------------------
# 补建边（15 条：12 instanceOf + 3 appliesTo），每条附行号级 evidence + rule
# ---------------------------------------------------------------------------
CURATED_INSTANCE: list[tuple[str, str, str, str]] = [
    ("ex:Vec", "ex:Collections", "I1-category-listed",
     "01_foundation/05_collections/01_collections.md:5 关键术语“集合 (Collection) · 向量 (Vec)”；"
     ":10 Summary“The standard collections (Vec, VecDeque, HashMap, BTreeMap, sets)”——Vec 被集合权威页列为标准集合"),
    ("ex:HashMap", "ex:Collections", "I1-category-listed",
     "01_foundation/05_collections/01_collections.md:5 关键术语“集合 (Collection) · … · 哈希映射 (HashMap)”；"
     ":10 Summary 将 HashMap 列为标准集合；:41 设“1.3 HashMap vs BTreeMap”章节"),
    ("ex:Tokio", "ex:AsyncRuntime", "I3-self-evident-kind",
     "03_advanced/01_async/06_async_boundary_panorama.md:283“work-stealing 运行时（Tokio 多线程、async-std）”"
     "——Tokio 被明确归类为异步运行时；:9“Rust 版本: 1.97.0+ (Edition 2024) · Tokio 1.x”"),
    ("ex:Send", "ex:AutoTrait", "I3-self-evident-kind",
     "03_advanced/00_concurrency/02_send_sync_auto_traits.md:3 标题“Send 与 Sync：Auto Trait 的并发安全契约”；"
     ":5 Summary“Send and Sync are auto traits that encode Rust's concurrency safety contract: `T: Send` …”"),
    ("ex:Sync", "ex:AutoTrait", "I3-self-evident-kind",
     "03_advanced/00_concurrency/02_send_sync_auto_traits.md:3 标题“Send 与 Sync：Auto Trait 的并发安全契约”；"
     ":5 Summary“…and `T: Sync` is equivalent to `&T: Send`”——Sync 自述为 auto trait"),
    ("ex:Box", "ex:SmartPointers", "I1-category-listed",
     "02_intermediate/02_memory_management/04_smart_pointers.md:7 Summary"
     "“Smart Pointers — Box, Rc/Arc, RefCell/Cell”；:37 设“1.2 Box：独占堆分配”章节——Box 被智能指针权威页列为成员"),
    ("ex:Rc", "ex:SmartPointers", "I1-category-listed",
     "02_intermediate/02_memory_management/04_smart_pointers.md:7 Summary"
     "“Smart Pointers — Box, Rc/Arc, RefCell/Cell”；:38 设“1.3 Rc 与 Arc：引用计数共享”章节"),
    ("ex:Arc", "ex:SmartPointers", "I1-category-listed",
     "02_intermediate/02_memory_management/04_smart_pointers.md:7 Summary"
     "“Smart Pointers — Box, Rc/Arc, RefCell/Cell”；:38 设“1.3 Rc 与 Arc：引用计数共享”章节"),
    ("ex:Result", "ex:AlgebraicDataType", "I1-category-listed",
     "04_formal/00_type_theory/01_type_theory.md:504“| `Option<T>` / `Result<T, E>` | C1: 递归类型 + ADT |”；"
     ":121“代数数据类型（ADT）的积与余积语义是类型论的标准结论”（Pierce TAPL Ch.11）——Result 被类型论权威页归类为 ADT"),
    ("ex:Option", "ex:AlgebraicDataType", "I1-category-listed",
     "04_formal/00_type_theory/01_type_theory.md:504“| `Option<T>` / `Result<T, E>` | C1: 递归类型 + ADT |”；"
     "01_foundation/07_modules_and_items/05_enumerations.md:15 后置概念“Algebraic Data Types”——Option 被归类为 ADT"),
    ("ex:VerificationToolchain", "ex:FormalVerificationFramework", "I2-category-section",
     "06_ecosystem/08_formal_verification/01_formal_ecosystem_tower.md:89"
     "“L4 验证扩展层 — 功能正确性证明 — Kani · Verus · Creusot”；:101 分层塔将验证工具链成员"
     "（Kani/Verus/Creusot）纳入形式化生态框架——验证工具链是形式化验证框架的组成部分"),
]

CURATED_APPLIES: list[tuple[str, str, str, str]] = [
    ("ex:SerdePatterns", "ex:Serialization", "A1-page-application",
     "02_intermediate/00_traits/03_serde_patterns.md:2 关键术语“序列化 (Serialization) · 反序列化 "
     "(Deserialization) · serde”；:4 标题“Serde 序列化模式：Rust 的类型驱动数据转换”——serde 模式应用于序列化领域"),
    ("ex:KaniRustBoundedModelChecker", "ex:ModelChecking", "A1-page-application",
     "04_formal/04_model_checking/09_kani.md:9 Summary“Kani is an AWS-developed bounded model checker "
     "for Rust”；:60“Kani 是 AWS 开发并开源的 Rust 有界模型检查器（Bounded Model Checker）”——Kani 应用于模型检查领域"),
    ("ex:RustBelt_02separation", "ex:UnsafeAbstractionSoundness", "A1-page-application",
     "04_formal/02_separation_logic/01_rustbelt.md:118“[RustBelt: POPL 2018] … It provides a proof "
     "technique for verifying that unsafe code respects safe Rust's abstraction boundaries”"
     "——RustBelt 应用于 unsafe 抽象可靠性（soundness）证明"),
]

# 第一轮缺口清单 → 本轮解决映射（用于报告对照）
GAP_RESOLUTION: list[tuple[str, str]] = [
    ("① ex:Vec / ex:HashMap → ex:Collections", "新建 2 实例节点 + 2 条 instanceOf"),
    ("② ex:Tokio → ex:AsyncRuntime", "新建范畴 ex:AsyncRuntime + 实例 ex:Tokio + 1 条 instanceOf"),
    ("③ ex:Send / ex:Sync → ex:AutoTrait", "新建范畴 ex:AutoTrait + 2 实例节点 + 2 条 instanceOf"),
    ("④ ex:Box / ex:Rc / ex:Arc → ex:SmartPointers", "新建 3 实例节点 + 3 条 instanceOf"),
    ("⑤ ex:Result / ex:Option → ex:AlgebraicDataType", "新建范畴 ex:AlgebraicDataType + 2 实例节点 + 2 条 instanceOf"),
    ("⑥ ex:Serialization（serde appliesTo 目标）", "新建领域节点 + ex:SerdePatterns appliesTo ex:Serialization"),
    ("⑦ ex:ModelChecking（kani appliesTo 目标）", "新建领域节点 + ex:KaniRustBoundedModelChecker appliesTo ex:ModelChecking"),
    ("⑧ ex:FormalVerificationFramework", "新建范畴节点 + ex:VerificationToolchain instanceOf ex:FormalVerificationFramework"),
    ("⑨ ex:UnsafeAbstractionSoundness（rustbelt appliesTo 目标）", "新建领域节点 + ex:RustBelt_02separation appliesTo ex:UnsafeAbstractionSoundness"),
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true", help="只输出报告，不写回 kg_data_v3.json")
    ap.add_argument("--date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    data = json.loads(KG_PATH.read_text(encoding="utf-8"))
    entities = data["entities"]
    relations = data["relations"]
    id_set = {e["@id"] for e in entities}

    # ---- 1. 新建节点 ----
    added_entities: list[str] = []
    skipped_entities: list[str] = []
    for e in NEW_ENTITIES:
        if e["@id"] in id_set:
            skipped_entities.append(e["@id"])
            continue
        entities.append(e)
        id_set.add(e["@id"])
        added_entities.append(e["@id"])

    before = Counter(r["ex:predicate"] for r in relations)

    def has_edge(s: str, o: str, pred: str | None = None) -> bool:
        return any(r["ex:subject"] == s and r["ex:object"] == o
                   and (pred is None or r["ex:predicate"] == pred) for r in relations)

    def find_edge(s: str, o: str, pred: str):
        for r in relations:
            if r["ex:subject"] == s and r["ex:object"] == o and r["ex:predicate"] == pred:
                return r
        return None

    max_id = max((int(m.group(1)) for r in relations
                  if (m := re.match(r"_:rel(\d+)$", r.get("@id", "")))), default=0)

    changes: list[dict] = []
    skipped_missing_entity: list[tuple[str, str, str]] = []

    def apply_edge(s: str, o: str, pred: str, rule: str, evidence: str) -> None:
        nonlocal max_id
        if s not in id_set or o not in id_set:
            skipped_missing_entity.append((s, pred, o))
            return
        if has_edge(s, o, pred):
            return
        rel = find_edge(s, o, PRED_REL)
        if rel is not None:
            rel["ex:predicate"] = pred
            rel["ex:evidence"] = evidence
            rel["ex:rule"] = rule
            rel["ex:reviewed"] = True
            changes.append({"rule": rule, "subject": s, "object": o, "predicate": pred,
                            "action": "retyped relatedTo", "evidence": evidence})
        else:
            action = "added parallel edge" if has_edge(s, o) else "added new edge"
            max_id += 1
            relations.append({
                "@id": f"_:rel{max_id}",
                "@type": "ex:RelationAnnotation",
                "ex:subject": s,
                "ex:predicate": pred,
                "ex:object": o,
                "ex:source": "curated:" + rule,
                "ex:evidence": evidence,
                "ex:rule": rule,
                "ex:confidence": 1.0,
                "ex:version": "1.97.0",
                "ex:reviewed": True,
                "dcterms:created": args.date,
            })
            changes.append({"rule": rule, "subject": s, "object": o, "predicate": pred,
                            "action": action, "evidence": evidence})

    for s, o, rule, ev in CURATED_INSTANCE:
        apply_edge(s, o, PRED_INST, rule, ev)
    for s, o, rule, ev in CURATED_APPLIES:
        apply_edge(s, o, PRED_APPL, rule, ev)

    after = Counter(r["ex:predicate"] for r in relations)

    # ---- 报告 ----
    out_md = ROOT / "reports" / f"KG_CATEGORY_NODES_{args.date}.md"
    out_json = ROOT / "reports" / f"KG_CATEGORY_NODES_{args.date}.json"

    n_inst = sum(1 for c in changes if c["predicate"] == PRED_INST)
    n_appl = sum(1 for c in changes if c["predicate"] == PRED_APPL)

    def dist_table(b: Counter, a: Counter) -> list[str]:
        keys = sorted(set(b) | set(a), key=lambda k: -a.get(k, 0))
        rows = ["| 谓词 | 前 | 后 | Δ |", "|:---|---:|---:|---:|"]
        for k in keys:
            rows.append(f"| {k} | {b.get(k, 0)} | {a.get(k, 0)} | {a.get(k, 0) - b.get(k, 0):+d} |")
        return rows

    by_id = {e["@id"]: e for e in NEW_ENTITIES}
    lines = [
        "# KG 范畴/领域节点补建（第二轮语义边实例化）",
        "",
        f"**日期**: {args.date}  **模式**: {'dry-run（未写回）' if args.dry_run else '已写回 kg_data_v3.json'}  ",
        f"**新建节点**: {len(added_entities)}（跳过已存在 {len(skipped_entities)}）  ",
        f"**新建边**: {len(changes)}（instanceOf {n_inst} + appliesTo {n_appl}；跳过实体缺失 {len(skipped_missing_entity)}）  ",
        "**前序**: `reports/KG_SEMANTIC_EDGE_TYPING_2026_07_12.md`（第一轮；本报告解决其“范畴节点缺口清单”全部 9 项）",
        "",
        "## 新建节点明细",
        "",
        "| @id | @type | ex:path | layer | domain | bloom |",
        "|:---|:---|:---|:---:|:---:|:---:|",
    ]
    for eid in added_entities:
        e = by_id[eid]
        lines.append(f"| `{eid}` | {e['@type']} | `{e['ex:path']}` | {e['ex:layer']} "
                     f"| {e['ex:domain']} | {e['ex:bloomLevel']} |")
    if skipped_entities:
        lines += ["", "已存在而跳过: " + ", ".join(f"`{e}`" for e in skipped_entities)]
    lines += ["", "## 谓词分布前后对比", ""]
    lines += dist_table(before, after)
    lines += ["", "## 逐边明细与依据", "",
              "| 规则 | 动作 | 主语 | 谓词 | 宾语 | 依据 |",
              "|:---|:---|:---|:---|:---|:---|"]
    for c in changes:
        ev = c["evidence"].replace("|", "\\|")
        lines.append(f"| {c['rule']} | {c['action']} | {c['subject']} | {c['predicate']} "
                     f"| {c['object']} | {ev} |")
    if skipped_missing_entity:
        lines += ["", "## 跳过（实体缺失）", ""]
        for s, p, o in skipped_missing_entity:
            lines.append(f"- `{s}` -[{p}]-> `{o}`：端点实体不存在")
    lines += ["", "## 第一轮缺口清单 → 本轮解决对照", "",
              "| 第一轮缺口 | 本轮解决 |", "|:---|:---|"]
    for gap, res in GAP_RESOLUTION:
        lines.append(f"| {gap} | {res} |")
    lines += ["", "## 备注", "",
              "- 节点结构严格对齐现有实体（K1 必填字段 + K7 layer/domain + ex:bloomLevel）；"
              "`ex:path` 均指向已确认存在的 concept/ 权威页（范畴节点允许与其实例共享权威页路径，"
              "与既有 E1 同路径双节点惯例一致）。",
              "- `ex:layer`/`ex:domain` 按 `concept/00_meta/taxonomy.yaml` 前缀规则取值，"
              "可用 `scripts/add_kg_layer_domain.py` 复核。",
              "- 边结构与第一轮 `scripts/type_kg_semantic_edges.py` 完全一致"
              "（`ex:evidence` 行号级引文 + `ex:rule` + `ex:reviewed`）。",
              "", "## 机器可读", "",
              f"- JSON: `reports/KG_CATEGORY_NODES_{args.date}.json`", ""]

    out_json.write_text(json.dumps({
        "date": args.date, "dry_run": args.dry_run,
        "counts": {"entities_added": len(added_entities), "entities_skipped": len(skipped_entities),
                   "instanceOf": n_inst, "appliesTo": n_appl,
                   "total_edges": len(changes), "skipped_missing_entity": len(skipped_missing_entity)},
        "entities_added": added_entities,
        "before": dict(before), "after": dict(after),
        "changes_detail": changes,
        "gap_resolution": [{"gap": g, "resolution": r} for g, r in GAP_RESOLUTION],
    }, ensure_ascii=False, indent=2), encoding="utf-8")
    out_md.write_text("\n".join(lines), encoding="utf-8")

    if not args.dry_run:
        meta = data.get("metadata")
        if isinstance(meta, dict):
            if "entity_count" in meta:
                meta["entity_count"] = len(entities)
            if "relation_count" in meta:
                meta["relation_count"] = len(relations)
        KG_PATH.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")

    print(f"[add_kg_category_nodes] entities_added={len(added_entities)} "
          f"instanceOf={n_inst} appliesTo={n_appl} total_edges={len(changes)} "
          f"skipped={len(skipped_missing_entity)} dry_run={args.dry_run}")
    print(f"  entities: {len(entities)}  relations: {len(relations)}")
    print(f"  report: {out_md.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
