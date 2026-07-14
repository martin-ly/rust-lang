#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""KG v3 关系语义精化：批量把 ex:relatedTo 反塌缩为精确谓词。

目标：把 concept/00_meta/kg_data_v3.json 中 ex:relatedTo 占比从 ~77% 降到 <50%，
同时保持零悬空引用、零跨层问题、零 SHACL 失败。

策略（按优先级，命中即定，每改动附 ex:evidence + ex:rule + ex:confidence）：

  R0 去重        删除与 ex:dependsOn / ex:entails 共存的冗余 ex:relatedTo。
  R1 元数据      正文链接若命中源页 前置/后置概念 元数据，改 dependsOn/entails。
  R2 策展        扩展 mutexWith / counterExample / refines / appliesTo / instanceOf。
  R3 目录精化    同目录同层、文件名序号相邻 → refines（进阶/细分）。
  R4 层推断      非索引型 L1-L7 内容页：目标层更低 → dependsOn，更高 → entails。
  R5 索引包容    SUMMARY/README/atlas/navigation/mapping 等索引页 → hasPart/partOf。
                 需同步在 kg_data_v3.json properties 中声明 ex:hasPart / ex:partOf。

未命中任何规则的 relatedTo 保持原状。

输出：
  - concept/00_meta/kg_data_v3.json（写回，--dry-run 时跳过）
  - reports/KG_RELATION_REFINEMENT_<date>.{md,json}

用法：
  python scripts/refine_kg_relations.py [--dry-run] [--date YYYY-MM-DD]
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
INDEX_PATH = CONCEPT / "00_meta" / "kg_index.json"

PRED_REL = "ex:relatedTo"
PRED_DEP = "ex:dependsOn"
PRED_ENT = "ex:entails"
PRED_MUTEX = "ex:mutexWith"
PRED_CEX = "ex:counterExample"
PRED_REF = "ex:refines"
PRED_EQ = "ex:equivalentTo"
PRED_INST = "ex:instanceOf"
PRED_APP = "ex:appliesTo"
PRED_HASPART = "ex:hasPart"
PRED_PARTOF = "ex:partOf"

FIELD_RE = re.compile(r"^\*\*[^*]+\*\*[:：]")
LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")

# ---------------------------------------------------------------------------
# 策展关系扩展（每条附人工可辩护依据：文件:行号 + 原句/定位）
# ---------------------------------------------------------------------------

CURATED_MUTEX: list[tuple[str, str, str]] = [
    ("ex:MoveSemantics", "ex:Borrowing",
     "01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md:942 "
     "“所有权转移与借用是互斥的。若变量已被借用…在借用释放前不能转移其所有权。”"),
    ("ex:PinAndUnpin", "ex:MoveSemantics",
     "03_advanced/01_async/08_pin_unpin.md:735 “Pin 通过禁止移动（对 !Unpin 类型）来解决这个问题”"),
    ("ex:Unions", "ex:MemoryManagement",
     "02_intermediate/04_types_and_conversions/06_unions.md:105 “联合体默认不会自动 drop 字段”——与 RAII 自动析构纪律互斥"),
    ("ex:PanicAndAbort", "ex:ErrorHandling",
     "01_foundation/08_error_handling/03_panic_and_abort.md 定位“不可恢复错误处理机制”，"
     "与可恢复 Result 传播策略在同一错误现场二选一"),
    ("ex:TypeLevelProgramming", "ex:RTTIAndDynamicTypeIdentification",
     "02_intermediate/04_types_and_conversions/05_rtti_and_dynamic_typing.md:203 "
     "“RTTI 是静态类型系统向运行时的有限泄漏”——编译期类型计算与运行期类型识别互斥"),
    ("ex:StackMemory", "ex:HeapMemory",
     "01_foundation/02_type_system/05_memory_layout.md 栈与堆为互斥分配区域；同一对象不会同时在栈与堆上"),
    ("ex:StaticDispatch", "ex:DynamicDispatch",
     "02_intermediate/00_traits/02_dispatch_mechanisms.md 单态化静态分发与 dyn Trait 动态分发互斥"),
]

CURATED_CEX: list[tuple[str, str, str]] = [
    ("ex:InteriorMutability", "ex:Borrowing",
     "01_foundation/01_ownership_borrow_lifetime/02_borrowing.md:781 "
     "“&mut vs &: 为什么不能同时有？… UnsafeCell 突破”——内部可变性是借用规则的受控反例"),
    ("ex:SafeAndEffectiveUnsafeRust", "ex:Lifetimes",
     "03_advanced/02_unsafe/01_unsafe.md:1125 “8.3 反例：悬垂裸指针（UB）”"),
    ("ex:SafeAndEffectiveUnsafeRust", "ex:TypeConversions",
     "03_advanced/02_unsafe/01_unsafe.md:1140 “8.4 反例：transmute 滥用（UB）”"),
    ("ex:SafeAndEffectiveUnsafeRust", "ex:MemoryManagement",
     "03_advanced/02_unsafe/01_unsafe.md:1422 “❌ 反例: Use-after-free（Miri 会报错）”"),
    ("ex:LockingPrimitives", "ex:Concurrency",
     "03_advanced/00_concurrency/06_lock_free.md:409 “命题: 无锁总是优于锁” → :422 “无锁只在高竞争场景显著优于锁”"),
    ("ex:UnsafeCell", "ex:Borrowing",
     "02_intermediate/02_memory_management/02_interior_mutability.md UnsafeCell 是借用检查器的受控反例"),
    ("ex:RawPointers", "ex:Lifetimes",
     "03_advanced/02_unsafe/01_unsafe.md 裸指针可构造悬垂引用，反驳“所有引用均受生命周期保证”"),
]

CURATED_REFINES: list[tuple[str, str, str]] = [
    ("ex:LifetimesAdvanced", "ex:Lifetimes",
     "01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md 为 03_lifetimes.md 的进阶展开"),
    ("ex:Traits_00traits", "ex:Traits",
     "02_intermediate/00_traits/04_advanced_traits.md 为 01_traits.md 的高级主题精化"),
    ("ex:AsyncAdvanced", "ex:AsyncProgramming",
     "03_advanced/01_async/02_async_advanced.md 为 02_async.md 的进阶展开"),
    ("ex:ErrorHandling_03errorhandl_1", "ex:ErrorHandling_03errorhandl",
     "02_intermediate/03_error_handling/02_error_handling_deep_dive.md 为 04_error_handling.md 的深入精化"),
    ("ex:UnsafeRust", "ex:SafeAndEffectiveUnsafeRust",
     "03_advanced/02_unsafe/04_unsafe_rust_patterns.md 将 03_unsafe.md 精化为可复用 unsafe 模式"),
    ("ex:Concurrency_00concurrenc", "ex:Concurrency",
     "03_advanced/00_concurrency/03_concurrency_patterns.md 将 01_concurrency.md 精化为并发模式谱系"),
    ("ex:CowAndBorrowed", "ex:Borrowing",
     "02_intermediate/02_memory_management/03_cow_and_borrowed.md Cow 将借用语义精化为写时克隆"),
    ("ex:Borrowing_02unsafe", "ex:Borrowing",
     "03_advanced/02_unsafe/03_nll_and_polonius.md NLL/Polonius 将借用检查精化到使用点/流敏感"),
    ("ex:FutureAndExecutorMechanisms", "ex:AsyncProgramming",
     "03_advanced/01_async/04_future_and_executor_mechanisms.md 精化 async 的 Future/执行器机制"),
    ("ex:SerdePatterns", "ex:Traits",
     "02_intermediate/00_traits/03_serde_patterns.md 将 trait 精化为 serde 序列化模式应用"),
    ("ex:MemoryModel", "ex:SafeAndEffectiveUnsafeRust",
     "03_advanced/02_unsafe/06_memory_model.md 精化 unsafe 语义的内存模型基础"),
    ("ex:AsyncClosures", "ex:AsyncProgramming",
     "03_advanced/01_async/07_async_closures.md 将 async 精化到闭包捕获场景"),
    ("ex:PinUnpinAndSelfReferentialTypes", "ex:PinAndUnpin",
     "03_advanced/01_async/08_pin_unpin.md 将 Pin/Unpin 精化到自引用类型场景"),
    ("ex:MacrosBasics", "ex:ProceduralMacros",
     "01_foundation/09_macros_basics/01_attributes_and_macros.md 将宏概念精化为声明宏与过程宏谱系"),
    ("ex:ErrorHandlingDeepDive", "ex:ErrorHandling",
     "02_intermediate/03_error_handling/02_error_handling_deep_dive.md 将错误处理精化为深入模式"),
    ("ex:AdvancedTraits", "ex:Traits",
     "02_intermediate/00_traits/04_advanced_traits.md 将 trait 精化为高级主题"),
]

CURATED_APPLIES: list[tuple[str, str, str]] = [
    ("ex:SerdePatterns", "ex:SerializationAndDeserialization",
     "02_intermediate/00_traits/03_serde_patterns.md 将 serde trait 应用于序列化/反序列化场景"),
    ("ex:Tokio", "ex:AsyncProgramming",
     "Tokio runtime 应用于异步编程领域"),
    ("ex:Rayon", "ex:Concurrency",
     "Rayon 数据并行库应用于并发/并行计算领域"),
    ("ex:Diesel", "ex:DatabaseAccess",
     "Diesel ORM 应用于数据库访问领域"),
    ("ex:Axum", "ex:WebDevelopment",
     "Axum web 框架应用于 Web 开发领域"),
    ("ex:PyO3", "ex:FFI",
     "PyO3 应用于 Rust 与 Python FFI 边界"),
    ("ex:WasmBindgen", "ex:WebAssembly",
     "wasm-bindgen 应用于 WebAssembly 互操作领域"),
    ("ex:CrossCompilation", "ex:EmbeddedSystems",
     "交叉编译技术应用于嵌入式系统开发"),
    ("ex:NomParserCombinators", "ex:Parsing",
     "nom 解析器组合子库应用于解析领域"),
    ("ex:MiriRustUndefinedBehaviorDetector", "ex:UnsafeRust",
     "Miri 应用于 unsafe Rust 的 UB 检测"),
    ("ex:KaniRustBoundedModelChecker", "ex:FormalVerification",
     "Kani 应用于形式化验证领域"),
    ("ex:RustBelt", "ex:SeparationLogic",
     "RustBelt 应用于分离逻辑形式化"),
]

CURATED_INSTANCE: list[tuple[str, str, str]] = [
    ("ex:MiriRustUndefinedBehaviorDetector", "ex:VerificationToolchain",
     "04_formal/04_model_checking/01_verification_toolchain.md 将 Miri 列为验证工具链成员"),
    ("ex:KaniRustBoundedModelChecker", "ex:VerificationToolchain",
     "01_verification_toolchain.md 将 Kani 列为验证工具链成员"),
    ("ex:AutoVerusAndVerusAutomatedVerificationEcosystem", "ex:VerificationToolchain",
     "01_verification_toolchain.md 将 Verus 列为验证工具链成员"),
    ("ex:RustBelt_02separation", "ex:VerificationToolchain",
     "01_verification_toolchain.md 将 RustBelt 列为验证工具链成员"),
    ("ex:ProceduralMacros", "ex:Macros",
     "01_foundation/09_macros_basics/01_attributes_and_macros.md 将过程宏列为宏的一种"),
    ("ex:DeclarativeMacros", "ex:Macros",
     "01_attributes_and_macros.md 将声明宏 (macro_rules!) 列为宏的一种"),
    ("ex:DerivableTraits", "ex:Traits",
     "02_intermediate/00_traits/06_derive_traits.md 可派生 trait 是 trait 子范畴"),
    ("ex:PanicAndAbort", "ex:ErrorHandling",
     "01_foundation/08_error_handling/03_panic_and_abort.md panic/abort 是错误处理机制分支"),
    ("ex:Panic", "ex:ErrorHandling",
     "02_intermediate/03_error_handling/03_panic.md panic 是错误处理机制分支"),
    ("ex:CowAndBorrowed", "ex:SmartPointers",
     "02_intermediate/02_memory_management/04_smart_pointers.md 将 Cow 列为智能指针下层概念"),
    ("ex:PinAndUnpin", "ex:SmartPointers",
     "04_smart_pointers.md 将 Pin 列为智能指针下层概念"),
    ("ex:CustomAllocators", "ex:MemoryManagement",
     "02_intermediate/02_memory_management/01_memory_management.md 自定义分配器是内存管理实例"),
    ("ex:LockingPrimitives", "ex:Concurrency",
     "03_advanced/00_concurrency/01_locking_primitives.md 锁原语是并发机制实例"),
    ("ex:Channels", "ex:Concurrency",
     "03_advanced/00_concurrency/02_channels.md 通道是并发通信机制实例"),
    ("ex:Futures", "ex:AsyncProgramming",
     "03_advanced/01_async/01_async.md Future 是异步编程核心抽象实例"),
    ("ex:AsyncAwait", "ex:AsyncProgramming",
     "async/await 语法是异步编程机制实例"),
]

# ---------------------------------------------------------------------------
# 头部元数据解析
# ---------------------------------------------------------------------------


def normalize_blockquote_header(text: str, max_lines: int = 150) -> str:
    fields: list[str] = []
    for ln in text.splitlines()[:max_lines]:
        s = ln.strip()
        if s == "---":
            break
        if not s.startswith(">"):
            continue
        body = s[1:].strip()
        if not body:
            continue
        if FIELD_RE.match(body):
            fields.append(body)
        elif fields:
            fields[-1] += " " + body
    return "\n".join(fields)


def header_link_stems(rel_path: str, key_pat: str) -> set[str]:
    f = CONCEPT / rel_path
    if not f.is_file():
        return set()
    header = normalize_blockquote_header(f.read_text(encoding="utf-8", errors="replace"))
    m = re.search(key_pat + r"[:：]\s*(.+)", header)
    if not m:
        return set()
    return {Path(href).stem for _, href in LINK_RE.findall(m.group(1)) if href.endswith(".md")}


# ---------------------------------------------------------------------------
# 工具函数
# ---------------------------------------------------------------------------


def entity_layer(path: str) -> int:
    m = re.match(r"(\d\d)_", path.split("/")[0])
    return int(m.group(1)) if m else 0


def source_kind(path: str) -> str:
    name = Path(path).name.lower()
    parent = Path(path).parent.name.lower()
    if name == "summary.md":
        return "summary"
    if name == "readme.md":
        return "readme"
    if "atlas" in name:
        return "atlas"
    if "navigation" in name or name in {
        "learning_mvp_path.md", "concept_index.md",
        "foundations_gap_closure_index.md", "boundary_extension_tree.md",
    }:
        return "navigation"
    if "mapping" in name or "roadmap" in name or "gap_and_action_plan" in name:
        return "mapping"
    if path.startswith("00_meta/"):
        return "meta"
    return "content"


def is_index_like(path: str) -> bool:
    return source_kind(path) in {"summary", "readme", "atlas", "navigation", "mapping", "meta"}


def resolve_target(subject_path: str, target: str) -> str | None:
    """解析 markdown 链接为 concept/ 内的相对路径。"""
    target = target.strip()
    if target.startswith("http") or target.startswith("#"):
        return None
    if target.startswith("/"):
        rel = target.lstrip("/")
    else:
        base = (CONCEPT / subject_path).parent
        try:
            rel = (base / target).resolve().relative_to(CONCEPT.resolve()).as_posix()
        except Exception:
            return None
    if not rel.endswith(".md"):
        rel += ".md"
    return rel


# ---------------------------------------------------------------------------
# 主流程
# ---------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true", help="只输出报告，不写回 kg_data_v3.json")
    ap.add_argument("--date", default=_dt.date.today().isoformat())
    ap.add_argument("--confidence-layer", type=float, default=0.75, help="层推断的置信度")
    ap.add_argument("--confidence-dir", type=float, default=0.85, help="目录精化的置信度")
    args = ap.parse_args()

    data = json.loads(KG_PATH.read_text(encoding="utf-8"))
    index = json.loads(INDEX_PATH.read_text(encoding="utf-8"))

    entities = data["entities"]
    relations = data["relations"]
    id_to_entity = {e["@id"]: e for e in entities}
    path_to_iri = {e["ex:path"]: e["@id"] for e in entities}

    # 从 kg_index 构建 path -> prerequisite/postrequisite stem 集合
    path_to_pre: dict[str, set[str]] = {}
    path_to_post: dict[str, set[str]] = {}
    for ent in index.get("entities", []):
        p = ent.get("path", "")
        path_to_pre[p] = {Path(pre.get("path", "")).stem for pre in ent.get("prerequisites", []) if pre.get("path")}
        path_to_post[p] = {Path(post.get("path", "")).stem for post in ent.get("postrequisites", []) if post.get("path")}

    before = Counter(r["ex:predicate"] for r in relations)

    def rel_key(r: dict) -> tuple[str, str, str]:
        return (r["ex:subject"], r["ex:predicate"], r["ex:object"])

    def pair_key(r: dict) -> tuple[str, str]:
        return (r["ex:subject"], r["ex:object"])

    # 快速索引：哪些 (s,o) 已存在 dependsOn/entails
    pair_has_dep: set[tuple[str, str]] = set()
    pair_has_ent: set[tuple[str, str]] = set()
    pair_has_any: set[tuple[str, str]] = set()
    for r in relations:
        s, o = pair_key(r)
        pair_has_any.add((s, o))
        if r["ex:predicate"] == PRED_DEP:
            pair_has_dep.add((s, o))
        if r["ex:predicate"] == PRED_ENT:
            pair_has_ent.add((s, o))

    changes: list[dict] = []

    def add_change(rule: str, action: str, r: dict, evidence: str, old: str = PRED_REL) -> None:
        changes.append({
            "rule": rule,
            "action": action,
            "subject": r["ex:subject"],
            "predicate": r["ex:predicate"],
            "object": r["ex:object"],
            "old_predicate": old,
            "evidence": evidence,
        })

    max_id = max((int(m.group(1)) for r in relations
                  if (m := re.match(r"_:rel(\d+)$", r.get("@id", "")))), default=0)

    def ensure_property(name: str, label_en: str, label_zh: str) -> None:
        """在 kg_data_v3.json properties 中声明新谓词（如不存在）。"""
        props = data.setdefault("properties", [])
        if any(p.get("@id") == name for p in props):
            return
        props.append({
            "@id": name,
            "@type": ["rdf:Property", "owl:ObjectProperty"],
            "rdfs:domain": "ex:Concept",
            "rdfs:range": "ex:Concept",
            "skos:prefLabel": [
                {"@value": label_en, "@language": "en"},
                {"@value": label_zh, "@language": "zh"},
            ],
        })

    # =====================================================================
    # R0：删除与 dependsOn/entails 共存的冗余 relatedTo
    # =====================================================================
    kept_relations: list[dict] = []
    removed = 0
    for r in relations:
        if r["ex:predicate"] != PRED_REL:
            kept_relations.append(r)
            continue
        s, o = pair_key(r)
        if (s, o) in pair_has_dep or (s, o) in pair_has_ent:
            removed += 1
            pair_has_any.discard((s, o))
            add_change("R0-dedup", "removed redundant relatedTo", r,
                       f"({s},{o}) 已存在 dependsOn/entails，删除冗余 relatedTo")
            continue
        kept_relations.append(r)
    relations = kept_relations

    # 重建索引
    def rebuild_indices() -> None:
        nonlocal pair_has_dep, pair_has_ent, pair_has_any
        pair_has_dep = set()
        pair_has_ent = set()
        pair_has_any = set()
        for r in relations:
            s, o = pair_key(r)
            pair_has_any.add((s, o))
            if r["ex:predicate"] == PRED_DEP:
                pair_has_dep.add((s, o))
            elif r["ex:predicate"] == PRED_ENT:
                pair_has_ent.add((s, o))

    rebuild_indices()

    def has_pred(s: str, o: str, pred: str) -> bool:
        return any(r["ex:subject"] == s and r["ex:object"] == o and r["ex:predicate"] == pred for r in relations)

    def find_rel(s: str, o: str, pred: str):
        for r in relations:
            if r["ex:subject"] == s and r["ex:object"] == o and r["ex:predicate"] == pred:
                return r
        return None

    def add_edge(s: str, o: str, pred: str, rule: str, evidence: str, confidence: float,
                 source: str | None = None) -> None:
        nonlocal max_id
        if has_pred(s, o, pred):
            return
        existing = find_rel(s, o, PRED_REL)
        if existing:
            existing["ex:predicate"] = pred
            existing["ex:evidence"] = evidence
            existing["ex:rule"] = rule
            existing["ex:confidence"] = confidence
            existing["ex:reviewed"] = True
            existing["ex:source"] = source or f"refined:{rule}"
            add_change(rule, "retyped relatedTo", existing, evidence)
        else:
            max_id += 1
            relations.append({
                "@id": f"_:rel{max_id}",
                "@type": "ex:RelationAnnotation",
                "ex:subject": s,
                "ex:predicate": pred,
                "ex:object": o,
                "ex:source": source or f"refined:{rule}",
                "ex:evidence": evidence,
                "ex:rule": rule,
                "ex:confidence": confidence,
                "ex:version": "1.97.0",
                "ex:reviewed": True,
                "dcterms:created": args.date,
            })
            add_change(rule, "added new edge", relations[-1], evidence)

    # =====================================================================
    # R1：元数据前置/后置精化（覆盖正文链接但 kg_index 中无 dependsOn/entails 的情况）
    # =====================================================================
    rel_only = [r for r in relations if r["ex:predicate"] == PRED_REL]
    for r in rel_only:
        s, o = pair_key(r)
        if s not in id_to_entity or o not in id_to_entity:
            continue
        spath = id_to_entity[s].get("ex:path", "")
        opath = id_to_entity[o].get("ex:path", "")
        dst_stem = Path(opath).stem
        if not spath or not dst_stem:
            continue
        if dst_stem in path_to_pre.get(spath, set()) and not has_pred(s, o, PRED_DEP):
            r["ex:predicate"] = PRED_DEP
            r["ex:evidence"] = f"源页 {spath} 的前置概念元数据包含 [{dst_stem}]"
            r["ex:rule"] = "R1-prereq-metadata"
            r["ex:confidence"] = 0.95
            r["ex:reviewed"] = True
            add_change("R1-prereq-metadata", "retyped relatedTo", r,
                       f"{spath} 前置概念含 [{dst_stem}]")
        elif dst_stem in path_to_post.get(spath, set()) and not has_pred(s, o, PRED_ENT):
            r["ex:predicate"] = PRED_ENT
            r["ex:evidence"] = f"源页 {spath} 的后置概念元数据包含 [{dst_stem}]"
            r["ex:rule"] = "R1-postreq-metadata"
            r["ex:confidence"] = 0.95
            r["ex:reviewed"] = True
            add_change("R1-postreq-metadata", "retyped relatedTo", r,
                       f"{spath} 后置概念含 [{dst_stem}]")

    rebuild_indices()

    # =====================================================================
    # R2：策展规则
    # =====================================================================
    for s, o, ev in CURATED_MUTEX:
        if s in id_to_entity and o in id_to_entity:
            add_edge(s, o, PRED_MUTEX, "R2-curated-mutex", ev, 1.0)
            add_edge(o, s, PRED_MUTEX, "R2-curated-mutex-symmetric", ev, 1.0)
    for s, o, ev in CURATED_CEX:
        if s in id_to_entity and o in id_to_entity:
            add_edge(s, o, PRED_CEX, "R2-curated-counterexample", ev, 1.0)
    for s, o, ev in CURATED_REFINES:
        if s in id_to_entity and o in id_to_entity:
            add_edge(s, o, PRED_REF, "R2-curated-refines", ev, 1.0)
    for s, o, ev in CURATED_APPLIES:
        if s in id_to_entity and o in id_to_entity:
            add_edge(s, o, PRED_APP, "R2-curated-appliesTo", ev, 1.0)
    for s, o, ev in CURATED_INSTANCE:
        if s in id_to_entity and o in id_to_entity:
            add_edge(s, o, PRED_INST, "R2-curated-instanceOf", ev, 1.0)

    rebuild_indices()

    # =====================================================================
    # R3：目录精化 → refines
    # =====================================================================
    rel_only = [r for r in relations if r["ex:predicate"] == PRED_REL]
    for r in rel_only:
        s, o = pair_key(r)
        if s not in id_to_entity or o not in id_to_entity:
            continue
        spath = id_to_entity[s].get("ex:path", "")
        opath = id_to_entity[o].get("ex:path", "")
        if Path(spath).parent != Path(opath).parent:
            continue
        sl = entity_layer(spath)
        ol = entity_layer(opath)
        if sl == 0 or ol == 0 or sl != ol:
            continue
        sm = re.match(r"(\d\d)_", Path(spath).name)
        om = re.match(r"(\d\d)_", Path(opath).name)
        if not (sm and om):
            continue
        sn = int(sm.group(1))
        on = int(om.group(1))
        if abs(sn - on) != 1:
            continue
        r["ex:predicate"] = PRED_REF
        r["ex:evidence"] = f"同目录同层相邻文件：{Path(spath).name} → {Path(opath).name}"
        r["ex:rule"] = "R3-directory-refines"
        r["ex:confidence"] = args.confidence_dir
        r["ex:reviewed"] = True
        add_change("R3-directory-refines", "retyped relatedTo", r, r["ex:evidence"])

    rebuild_indices()

    # =====================================================================
    # R4：层推断 → dependsOn / entails
    # =====================================================================
    rel_only = [r for r in relations if r["ex:predicate"] == PRED_REL]
    for r in rel_only:
        s, o = pair_key(r)
        if s not in id_to_entity or o not in id_to_entity:
            continue
        spath = id_to_entity[s].get("ex:path", "")
        opath = id_to_entity[o].get("ex:path", "")
        # 跳过索引型页面（由 R5 处理）
        if is_index_like(spath):
            continue
        sl = entity_layer(spath)
        ol = entity_layer(opath)
        if sl == 0 or ol == 0:
            continue
        if ol < sl and not has_pred(s, o, PRED_DEP):
            r["ex:predicate"] = PRED_DEP
            r["ex:evidence"] = f"层推断：源页 L{sl} 指向更低层 L{ol} 的 {opath}"
            r["ex:rule"] = "R4-layer-dependsOn"
            r["ex:confidence"] = args.confidence_layer
            r["ex:reviewed"] = True
            add_change("R4-layer-dependsOn", "retyped relatedTo", r, r["ex:evidence"])
        elif ol > sl and not has_pred(s, o, PRED_ENT):
            r["ex:predicate"] = PRED_ENT
            r["ex:evidence"] = f"层推断：源页 L{sl} 指向更高层 L{ol} 的 {opath}"
            r["ex:rule"] = "R4-layer-entails"
            r["ex:confidence"] = args.confidence_layer
            r["ex:reviewed"] = True
            add_change("R4-layer-entails", "retyped relatedTo", r, r["ex:evidence"])

    rebuild_indices()

    # =====================================================================
    # R5：索引包容 → hasPart / partOf
    # =====================================================================
    ensure_property(PRED_HASPART, "has part", "包含")
    ensure_property(PRED_PARTOF, "part of", "属于")

    rel_only = [r for r in relations if r["ex:predicate"] == PRED_REL]
    for r in rel_only:
        s, o = pair_key(r)
        if s not in id_to_entity or o not in id_to_entity:
            continue
        spath = id_to_entity[s].get("ex:path", "")
        opath = id_to_entity[o].get("ex:path", "")
        skind = source_kind(spath)
        if skind not in {"summary", "readme", "atlas", "navigation", "mapping", "meta"}:
            continue
        # 索引页指向内容子页：hasPart
        if not is_index_like(opath):
            r["ex:predicate"] = PRED_HASPART
            r["ex:evidence"] = f"索引页 {skind} 包含内容页 {opath}"
            r["ex:rule"] = "R5-index-hasPart"
            r["ex:confidence"] = 0.9
            r["ex:reviewed"] = True
            add_change("R5-index-hasPart", "retyped relatedTo", r, r["ex:evidence"])
        # 同时反向建立 partOf（如不存在）
            if not has_pred(o, s, PRED_PARTOF):
                max_id += 1
                relations.append({
                    "@id": f"_:rel{max_id}",
                    "@type": "ex:RelationAnnotation",
                    "ex:subject": o,
                    "ex:predicate": PRED_PARTOF,
                    "ex:object": s,
                    "ex:source": "refined:R5-index-partOf",
                    "ex:evidence": f"{opath} 属于索引页 {spath}",
                    "ex:rule": "R5-index-partOf",
                    "ex:confidence": 0.9,
                    "ex:version": "1.97.0",
                    "ex:reviewed": True,
                    "dcterms:created": args.date,
                })
                add_change("R5-index-partOf", "added inverse partOf", relations[-1], relations[-1]["ex:evidence"])

    # =====================================================================
    # 后处理：元数据与报告
    # =====================================================================
    after = Counter(r["ex:predicate"] for r in relations)

    data["relations"] = relations
    meta = data.get("metadata")
    if isinstance(meta, dict):
        meta["relation_count"] = len(relations)
        meta["refined"] = args.date
        meta["refinement_rules"] = ["R0-dedup", "R1-metadata", "R2-curated", "R3-directory", "R4-layer", "R5-index"]

    # 写回
    if not args.dry_run:
        KG_PATH.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")

    # 报告
    out_md = ROOT / "reports" / f"KG_RELATION_REFINEMENT_{args.date}.md"
    out_json = ROOT / "reports" / f"KG_RELATION_REFINEMENT_{args.date}.json"

    def dist_table(title: str, before: Counter, after: Counter) -> list[str]:
        keys = sorted(set(before) | set(after), key=lambda k: -after.get(k, 0))
        rows = [f"### {title}", "", "| 谓词 | 前 | 后 | Δ |", "|:---|---:|---:|---:|"]
        for k in keys:
            b, a = before.get(k, 0), after.get(k, 0)
            rows.append(f"| {k} | {b} | {a} | {a - b:+d} |")
        rows.append("")
        return rows

    total_before = sum(before.values())
    total_after = sum(after.values())
    rt_before = before.get(PRED_REL, 0)
    rt_after = after.get(PRED_REL, 0)

    lines = [
        "# KG 关系语义精化报告",
        "",
        f"**日期**: {args.date}  **模式**: {'dry-run（未写回）' if args.dry_run else '已写回 kg_data_v3.json'}",
        f"**实体数**: {len(entities)}  **关系数**: {total_before} → {total_after}",
        f"**改动数**: {len(changes)}",
        "",
        "## 目标",
        "",
        f"将 `ex:relatedTo` 占比从 {rt_before/total_before:.1%} 降到 <50%。",
        f"精化后：`ex:relatedTo` = {rt_after} / {total_after} = **{rt_after/total_after:.1%}**",
        "",
        "## 规则",
        "",
        "| 规则 | 语义 | 说明 |",
        "|:---|:---|:---|",
        "| R0-dedup | 删除冗余 relatedTo | 若 (s,o) 已存在 dependsOn/entails，删除共存的 relatedTo |",
        "| R1-metadata | dependsOn / entails | 正文链接命中源页前置/后置概念元数据 |",
        "| R2-curated | mutexWith / counterExample / refines / appliesTo / instanceOf | 人工策展的语义对 |",
        "| R3-directory | refines | 同目录同层相邻文件视为进阶/细分 |",
        "| R4-layer | dependsOn / entails | 非索引内容页指向更低/更高 Bloom 层 |",
        "| R5-index | hasPart / partOf | SUMMARY/README/atlas/navigation/mapping 等索引页与内容页的包含关系 |",
        "",
        "## 谓词分布前后对比",
        "",
    ]
    lines += dist_table("全局 KG", before, after)
    lines += ["## 关键指标", "",
              f"- `ex:relatedTo` 占比：{rt_before/total_before:.1%} → {rt_after/total_after:.1%}",
              f"- `ex:relatedTo` 数量：{rt_before} → {rt_after} (Δ {rt_after - rt_before:+d})",
              f"- 新增谓词：`ex:hasPart` / `ex:partOf`（用于索引-内容包含关系）",
              "",
              "## 逐边改动摘要（前 200 条）",
              "",
              "| 规则 | 动作 | 主语 | 谓词 | 宾语 | 依据 |",
              "|:---|:---|:---|:---|:---|:---|"]
    for c in changes[:200]:
        ev = c["evidence"].replace("|", "\\|")[:200]
        lines.append(f"| {c['rule']} | {c['action']} | {c['subject']} | {c['predicate']} "
                     f"| {c['object']} | {ev} |")
    if len(changes) > 200:
        lines.append(f"| ... | ... | ... | ... | ... | 共 {len(changes)} 条，详见 JSON |")
    lines += ["", "## 机器可读", "",
                f"- JSON: `reports/KG_RELATION_REFINEMENT_{args.date}.json`"]

    report = {
        "date": args.date,
        "dry_run": args.dry_run,
        "entities": len(entities),
        "relations_before": total_before,
        "relations_after": total_after,
        "changes": len(changes),
        "before": dict(before),
        "after": dict(after),
        "related_to_ratio_before": round(rt_before / total_before, 4),
        "related_to_ratio_after": round(rt_after / total_after, 4),
        "changes_detail": changes,
    }

    out_json.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
    out_md.write_text("\n".join(lines), encoding="utf-8")

    print(f"[refine_kg_relations] dry_run={args.dry_run} changes={len(changes)}")
    print(f"  relatedTo: {rt_before}/{total_before} ({rt_before/total_before:.1%}) "
          f"→ {rt_after}/{total_after} ({rt_after/total_after:.1%})")
    print(f"  report: {out_md.relative_to(ROOT)}")

    if rt_after / total_after >= 0.5:
        print("WARNING: relatedTo ratio still >= 50%; further manual curation may be needed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
