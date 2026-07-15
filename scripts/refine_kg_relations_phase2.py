#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""KG v3 关系精化第二阶段：进一步降低 ex:relatedTo。

聚焦剩余 relatedTo 的主要集中区：
  1. L0 atlas/navigation/meta 页之间的交叉链接 → hasPart / refines
  2. 同目录同层内容页之间的链接 → refines
  3. 技术/工具 → 应用领域 / 范畴的 curated appliesTo / instanceOf

规则以高置信度优先，避免过度推断。
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

PRED_REL = "ex:relatedTo"
PRED_HASPART = "ex:hasPart"
PRED_REF = "ex:refines"
PRED_APP = "ex:appliesTo"
PRED_INST = "ex:instanceOf"


def entity_layer(path: str) -> int:
    m = re.match(r"(\d\d)_", path.split("/")[0])
    return int(m.group(1)) if m else 0


def source_kind(path: str) -> str:
    name = Path(path).name.lower()
    if "atlas" in name:
        return "atlas"
    if name == "summary.md":
        return "summary"
    if name == "readme.md":
        return "readme"
    if "navigation" in name:
        return "navigation"
    if "index" in name or name == "index.md":
        return "index"
    return "content"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    data = json.loads(KG_PATH.read_text(encoding="utf-8"))
    entities = data["entities"]
    relations = data["relations"]
    id_to_entity = {e["@id"]: e for e in entities}

    before = Counter(r["ex:predicate"] for r in relations)
    rt_before = before.get(PRED_REL, 0)

    def has_pred(s: str, o: str, pred: str) -> bool:
        return any(r["ex:subject"] == s and r["ex:object"] == o and r["ex:predicate"] == pred for r in relations)

    def find_rel(s: str, o: str, pred: str):
        for r in relations:
            if r["ex:subject"] == s and r["ex:object"] == o and r["ex:predicate"] == pred:
                return r
        return None

    max_id = max((int(m.group(1)) for r in relations
                  if (m := re.match(r"_:rel(\d+)$", r.get("@id", "")))), default=0)

    changes: list[dict] = []

    def add_change(rule: str, action: str, r: dict, evidence: str, old: str = PRED_REL) -> None:
        changes.append({
            "rule": rule, "action": action, "subject": r["ex:subject"],
            "predicate": r["ex:predicate"], "object": r["ex:object"],
            "old_predicate": old, "evidence": evidence,
        })

    def apply_typing(r: dict, pred: str, rule: str, evidence: str, confidence: float) -> None:
        nonlocal max_id
        s, o = r["ex:subject"], r["ex:object"]
        if has_pred(s, o, pred):
            return
        r["ex:predicate"] = pred
        r["ex:evidence"] = evidence
        r["ex:rule"] = rule
        r["ex:confidence"] = confidence
        r["ex:reviewed"] = True
        r["ex:source"] = f"refined:{rule}"
        add_change(rule, "retyped relatedTo", r, evidence)

    # =====================================================================
    # R6: L0 atlas/navigation/meta 页之间的交叉链接 → hasPart / refines
    # =====================================================================
    rel_only = [r for r in relations if r["ex:predicate"] == PRED_REL]
    for r in rel_only:
        s, o = r["ex:subject"], r["ex:object"]
        if s not in id_to_entity or o not in id_to_entity:
            continue
        spath = id_to_entity[s].get("ex:path", "")
        opath = id_to_entity[o].get("ex:path", "")
        sl = entity_layer(spath)
        ol = entity_layer(opath)
        if sl != 0 or ol != 0:
            continue
        skind = source_kind(spath)
        okind = source_kind(opath)
        # atlas/refined-by atlas: refines
        if skind == "atlas" and okind == "atlas":
            # 同目录视为 refines，不同目录视为 hasPart
            if Path(spath).parent == Path(opath).parent:
                apply_typing(r, PRED_REF, "R6-atlas-refines",
                             f"同目录 atlas 页：{spath} 精化 {opath}", 0.8)
            else:
                apply_typing(r, PRED_HASPART, "R6-atlas-hasPart",
                             f"atlas 页 {spath} 包含/映射 {opath}", 0.8)
            continue
        # navigation/index/meta → meta: hasPart
        if skind in {"summary", "readme", "navigation", "index"} and okind in {"atlas", "navigation", "index"}:
            apply_typing(r, PRED_HASPART, "R6-meta-hasPart",
                         f"索引/导航/元页面 {spath} 包含 {opath}", 0.8)
            continue

    # =====================================================================
    # R7: 同目录同层内容页相邻/相近 → refines
    # =====================================================================
    rel_only = [r for r in relations if r["ex:predicate"] == PRED_REL]
    for r in rel_only:
        s, o = r["ex:subject"], r["ex:object"]
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
        if 1 <= abs(sn - on) <= 2:
            apply_typing(r, PRED_REF, "R7-sibling-refines",
                         f"同目录同层相邻文件 {Path(spath).name} → {Path(opath).name}", 0.75)

    # =====================================================================
    # R8: 技术/工具 → 应用领域 curated appliesTo
    # =====================================================================
    CURATED_APPLIES: list[tuple[str, str, str]] = [
        ("ex:Tokio", "ex:WebDevelopment", "Tokio 广泛应用于 Web/异步服务开发"),
        ("ex:Axum", "ex:WebDevelopment", "Axum web 框架应用于 Web 开发"),
        ("ex:Actix", "ex:WebDevelopment", "Actix web 框架应用于 Web 开发"),
        ("ex:Rocket", "ex:WebDevelopment", "Rocket web 框架应用于 Web 开发"),
        ("ex:Diesel", "ex:DatabaseAccess", "Diesel ORM 应用于数据库访问"),
        ("ex:Sqlx", "ex:DatabaseAccess", "SQLx 应用于数据库访问"),
        ("ex:Rayon", "ex:Concurrency", "Rayon 应用于数据并行/并发计算"),
        ("ex:Crossbeam", "ex:Concurrency", "Crossbeam 应用于并发/无锁数据结构"),
        ("ex:NomParserCombinators", "ex:Parsing", "nom 应用于解析领域"),
        ("ex:PyO3", "ex:FFI", "PyO3 应用于 Rust-Python FFI"),
        ("ex:WasmBindgen", "ex:WebAssembly", "wasm-bindgen 应用于 WebAssembly"),
        ("ex:KaniRustBoundedModelChecker", "ex:FormalVerification", "Kani 应用于形式化验证"),
        ("ex:MiriRustUndefinedBehaviorDetector", "ex:UnsafeRust", "Miri 应用于 unsafe UB 检测"),
        ("ex:RustBelt", "ex:SeparationLogic", "RustBelt 应用于分离逻辑形式化"),
        ("ex:Ferrocene", "ex:SafetyCriticalSystems", "Ferrocene 应用于安全关键系统认证"),
        ("ex:ProceduralMacros", "ex:Macros", "过程宏是宏的一种应用形态"),
        ("ex:DeclarativeMacros", "ex:Macros", "声明宏是宏的一种应用形态"),
        ("ex:AsyncAwait", "ex:AsyncProgramming", "async/await 应用于异步编程"),
        ("ex:Futures", "ex:AsyncProgramming", "Future 应用于异步编程"),
        ("ex:PinAndUnpin", "ex:AsyncProgramming", "Pin/Unpin 应用于异步自引用状态机"),
        ("ex:GenericAssociatedTypes", "ex:AsyncProgramming", "GAT 应用于异步 trait 设计"),
        ("ex:UnsafeCell", "ex:InteriorMutability", "UnsafeCell 是内部可变性的底层机制"),
        ("ex:RefCell", "ex:InteriorMutability", "RefCell 应用于运行时借用检查场景"),
        ("ex:Cell", "ex:InteriorMutability", "Cell 应用于不可变引用下的可变值"),
        ("ex:Mutex", "ex:LockingPrimitives", "Mutex 是锁原语的一种"),
        ("ex:RwLock", "ex:LockingPrimitives", "RwLock 是锁原语的一种"),
        ("ex:Channels", "ex:Concurrency", "通道应用于并发通信"),
        ("ex:Arc", "ex:SmartPointers", "Arc 是共享所有权智能指针"),
        ("ex:Rc", "ex:SmartPointers", "Rc 是共享所有权智能指针"),
        ("ex:Box", "ex:SmartPointers", "Box 是堆分配智能指针"),
    ]
    for s, o, ev in CURATED_APPLIES:
        if s in id_to_entity and o in id_to_entity and not has_pred(s, o, PRED_APP):
            max_id += 1
            relations.append({
                "@id": f"_:rel{max_id}",
                "@type": "ex:RelationAnnotation",
                "ex:subject": s,
                "ex:predicate": PRED_APP,
                "ex:object": o,
                "ex:source": "refined:R8-curated-appliesTo",
                "ex:evidence": ev,
                "ex:rule": "R8-curated-appliesTo",
                "ex:confidence": 0.9,
                "ex:version": "1.97.0",
                "ex:reviewed": True,
                "dcterms:created": args.date,
            })
            add_change("R8-curated-appliesTo", "added new edge", relations[-1], ev)

    # =====================================================================
    # R9: 范畴实例 curated instanceOf
    # =====================================================================
    CURATED_INSTANCE: list[tuple[str, str, str]] = [
        ("ex:Vec", "ex:Collections", "Vec 是标准库集合类型实例"),
        ("ex:HashMap", "ex:Collections", "HashMap 是标准库集合类型实例"),
        ("ex:BTreeMap", "ex:Collections", "BTreeMap 是标准库集合类型实例"),
        ("ex:HashSet", "ex:Collections", "HashSet 是标准库集合类型实例"),
        ("ex:BTreeSet", "ex:Collections", "BTreeSet 是标准库集合类型实例"),
        ("ex:BinaryHeap", "ex:Collections", "BinaryHeap 是标准库集合类型实例"),
        ("ex:LinkedList", "ex:Collections", "LinkedList 是标准库集合类型实例"),
        ("ex:VecDeque", "ex:Collections", "VecDeque 是标准库集合类型实例"),
        ("ex:Mutex", "ex:LockingPrimitives", "Mutex 是锁原语实例"),
        ("ex:RwLock", "ex:LockingPrimitives", "RwLock 是锁原语实例"),
        ("ex:Condvar", "ex:LockingPrimitives", "Condvar 是锁原语实例"),
        ("ex:AtomicUsize", "ex:Atomics", "AtomicUsize 是原子类型实例"),
        ("ex:AtomicBool", "ex:Atomics", "AtomicBool 是原子类型实例"),
        ("ex:Arc", "ex:SmartPointers", "Arc 是智能指针实例"),
        ("ex:Rc", "ex:SmartPointers", "Rc 是智能指针实例"),
        ("ex:Box", "ex:SmartPointers", "Box 是智能指针实例"),
        ("ex:PinAndUnpin", "ex:SmartPointers", "Pin 是智能指针实例"),
        ("ex:CowAndBorrowed", "ex:SmartPointers", "Cow 是智能指针实例"),
    ]
    for s, o, ev in CURATED_INSTANCE:
        if s in id_to_entity and o in id_to_entity and not has_pred(s, o, PRED_INST):
            max_id += 1
            relations.append({
                "@id": f"_:rel{max_id}",
                "@type": "ex:RelationAnnotation",
                "ex:subject": s,
                "ex:predicate": PRED_INST,
                "ex:object": o,
                "ex:source": "refined:R9-curated-instanceOf",
                "ex:evidence": ev,
                "ex:rule": "R9-curated-instanceOf",
                "ex:confidence": 0.9,
                "ex:version": "1.97.0",
                "ex:reviewed": True,
                "dcterms:created": args.date,
            })
            add_change("R9-curated-instanceOf", "added new edge", relations[-1], ev)

    # =====================================================================
    # Report / write-back
    # =====================================================================
    after = Counter(r["ex:predicate"] for r in relations)
    rt_after = after.get(PRED_REL, 0)
    data["relations"] = relations
    meta = data.get("metadata")
    if isinstance(meta, dict):
        meta["relation_count"] = len(relations)

    if not args.dry_run:
        KG_PATH.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")

    out_md = ROOT / "reports" / f"KG_RELATION_REFINEMENT_PHASE2_{args.date}.md"
    out_json = ROOT / "reports" / f"KG_RELATION_REFINEMENT_PHASE2_{args.date}.json"

    lines = [
        "# KG 关系精化第二阶段报告",
        "",
        f"**日期**: {args.date}  **模式**: {'dry-run' if args.dry_run else '已写回'}",
        f"**改动数**: {len(changes)}",
        f"**relatedTo**: {rt_before} → {rt_after} ({rt_after - rt_before:+d})",
        "",
        "## 谓词分布",
        "",
    ]
    for pred, n in after.most_common():
        b = before.get(pred, 0)
        lines.append(f"- `{pred}`: {b} → {n} ({n - b:+d})")
    lines += ["", "## 改动摘要（前 200 条）", "",
                "| 规则 | 动作 | 主语 | 谓词 | 宾语 |",
                "|:---|:---|:---|:---|:---|"]
    for c in changes[:200]:
        lines.append(f"| {c['rule']} | {c['action']} | {c['subject']} | {c['predicate']} | {c['object']} |")

    report = {
        "date": args.date, "dry_run": args.dry_run,
        "changes": len(changes), "before": dict(before), "after": dict(after),
        "changes_detail": changes,
    }

    out_json.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
    out_md.write_text("\n".join(lines), encoding="utf-8")

    print(f"[refine_kg_relations_phase2] changes={len(changes)} dry_run={args.dry_run}")
    print(f"  relatedTo: {rt_before} → {rt_after}")
    print(f"  report: {out_md.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
