#!/usr/bin/env python3
"""Smoke tests for tools/kg_rag against concept/00_meta/kg_data_v3.json.

Structural checks (entity query + typed-edge traversal) run with plain
stdlib Python. The hybrid vector search check runs only when the heavy
dependencies (numpy / sentence-transformers) are importable — e.g. inside
``tools/kg_rag/.venv`` — and is skipped otherwise with a clear message.

Usage:
    python tools/kg_rag/smoke_test.py
    tools/kg_rag/.venv/Scripts/python tools/kg_rag/smoke_test.py   # incl. vector search

Exit code 0 = all executed checks passed.
"""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from kg_core import (  # noqa: E402
    KG_PATH,
    get_lang_value,
    iter_entities,
    kg_adjacency,
    kg_paths,
    load_kg,
    short_id,
    typed_edges,
)

FAILURES: list[str] = []
CHECKS = 0


def check(name: str, ok: bool, detail: str = "") -> None:
    global CHECKS
    CHECKS += 1
    status = "PASS" if ok else "FAIL"
    print(f"[{status}] {name}" + (f" — {detail}" if detail else ""))
    if not ok:
        FAILURES.append(name)


def main() -> int:
    if not KG_PATH.exists():
        print(f"[FAIL] KG file not found: {KG_PATH}")
        return 1
    kg = load_kg()
    entities = iter_entities(kg)
    by_id = {e["@id"]: e for e in entities}
    meta = kg.get("metadata", {})

    # ---- 1. dataset sanity -------------------------------------------------
    check("KG version is v3.x", str(meta.get("version", "")).startswith("3"),
          f"version={meta.get('version')}")
    check("entity count >= 490", len(entities) >= 490, f"{len(entities)} entities")
    check("relation count >= 5800", len(kg.get("relations", [])) >= 5800,
          f"{len(kg.get('relations', []))} relations")

    # ---- 2. entity query ---------------------------------------------------
    vec = by_id.get("ex:Vec")
    check("entity query: ex:Vec exists", vec is not None)
    if vec:
        label = get_lang_value(vec.get("skos:prefLabel", []), "en") or ""
        check("ex:Vec has EN prefLabel", "vec" in label.lower(), f"label={label!r}")
        check("ex:Vec has ex:path", bool(vec.get("ex:path")), vec.get("ex:path", ""))

    # ---- 3. typed-edge traversal ------------------------------------------
    adj = kg_adjacency(entities, kg)

    # 3a. instanceOf: "Vec 是什么的实例" -> Collections
    inst = adj.get("ex:Vec", {}).get("ex:instanceOf", [])
    check("instanceOf: Vec instanceOf Collections",
          "ex:Collections" in inst, f"Vec -instanceOf-> {inst}")

    # 3b. appliesTo: unsafe 相关的工具/方法 appliesTo SafeAndEffectiveUnsafeRust
    applies = typed_edges(kg, "ex:appliesTo")
    unsafe_tools = [
        short_id(s) for s, o in applies if o == "ex:SafeAndEffectiveUnsafeRust"
    ]
    check("appliesTo: >=3 tools apply to SafeAndEffectiveUnsafeRust",
          len(unsafe_tools) >= 3, ", ".join(sorted(unsafe_tools)))
    check("appliesTo: Miri appliesTo unsafe",
          ("ex:MiriRustUndefinedBehaviorDetector", "ex:SafeAndEffectiveUnsafeRust") in applies)

    # 3c. equivalentTo: lifetimes advanced 等价节点
    equiv = adj.get("ex:LifetimesAdvanced", {}).get("ex:equivalentTo", [])
    check("equivalentTo: LifetimesAdvanced == Lifetimes_00traits",
          "ex:Lifetimes_00traits" in equiv, f"LifetimesAdvanced -equivalentTo-> {equiv}")

    # 3d. multi-hop path traversal from a core node
    paths = kg_paths(adj, "ex:Vec")
    check("kg_paths: ex:Vec has outgoing paths", len(paths) > 0,
          f"{len(paths)} paths, e.g. {paths[0] if paths else ''}")

    # 3e. every relation endpoint resolves to a known entity (v3 integrity)
    known = set(by_id)
    dangling = [
        (r.get("ex:subject"), r.get("ex:object"))
        for r in kg.get("relations", [])
        if r.get("ex:subject") not in known or r.get("ex:object") not in known
    ]
    check("relations: no dangling endpoints", not dangling,
          f"{len(dangling)} dangling" if dangling else "")

    # ---- 4. hybrid vector search (optional, needs heavy deps) --------------
    try:
        import numpy  # noqa: F401
        import sentence_transformers  # noqa: F401
    except ImportError:
        print("[SKIP] hybrid vector search (run with tools/kg_rag/.venv python to enable)")
    else:
        from kg_rag import build_index, hybrid_search

        index, ents, model = build_index()
        check("vector index covers all entities", len(ents) == len(entities),
              f"index={len(ents)} kg={len(entities)}")
        results = hybrid_search("Vec dynamic array", model, index, ents, kg, top_k=5)
        check("hybrid_search returns 5 results", len(results) == 5)
        scores = [r["combined_score"] for r in results]
        check("hybrid_search scores sorted desc", scores == sorted(scores, reverse=True),
              str(scores))
        check("hybrid_search top-5 contains Vec",
              any(r["short_id"] == "Vec" for r in results),
              "top: " + ", ".join(r["short_id"] for r in results))

    print(f"\n{CHECKS - len(FAILURES)}/{CHECKS} checks passed.")
    if FAILURES:
        print("FAILED:", ", ".join(FAILURES))
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
