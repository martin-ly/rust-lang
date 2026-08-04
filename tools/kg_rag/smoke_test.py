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
    # Use a stable core concept entity. The exact entity set changes as the
    # knowledge graph grows, so we pick a canonical page that is guaranteed to
    # exist in any recent KG refresh.
    core = by_id.get("ex:Collections") or by_id.get("ex:Ownership")
    core_id = "ex:Collections" if by_id.get("ex:Collections") else "ex:Ownership"
    check(f"entity query: {short_id(core_id)} exists", core is not None)
    if core:
        label = get_lang_value(core.get("skos:prefLabel", []), "en") or ""
        check(f"{short_id(core_id)} has EN prefLabel", bool(label), f"label={label!r}")
        check(f"{short_id(core_id)} has ex:path", bool(core.get("ex:path")), core.get("ex:path", ""))

    # ---- 3. typed-edge traversal ------------------------------------------
    adj = kg_adjacency(entities, kg)

    # 3a. instanceOf / dependsOn: core concept relates to a foundational topic
    core_rels = adj.get(core_id, {})
    has_core_rel = bool(core_rels)
    check(f"{short_id(core_id)} has outgoing typed relations", has_core_rel,
          f"relations={list(core_rels.keys())[:5]}")

    # 3b. refines: LifetimesAdvanced refines Lifetimes
    refines = adj.get("ex:LifetimesAdvanced", {}).get("ex:refines", [])
    check("refines: LifetimesAdvanced refines Lifetimes",
          "ex:Lifetimes" in refines, f"LifetimesAdvanced -refines-> {refines}")

    # 3c. equivalentTo: Miri equivalent to a verification/borrow-check topic
    equiv = adj.get("ex:MiriRustUndefinedBehaviorDetector", {}).get("ex:equivalentTo", [])
    check("equivalentTo: Miri has equivalent node",
          bool(equiv), f"Miri -equivalentTo-> {equiv[:3]}")

    # 3d. multi-hop path traversal from a core node
    paths = kg_paths(adj, core_id)
    check(f"kg_paths: {short_id(core_id)} has outgoing paths", len(paths) > 0,
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
        results = hybrid_search("Rust collections and ownership", model, index, ents, kg, top_k=5)
        check("hybrid_search returns 5 results", len(results) == 5)
        scores = [r["combined_score"] for r in results]
        check("hybrid_search scores sorted desc", scores == sorted(scores, reverse=True),
              str(scores))
        expected_ids = {short_id(core_id), "Ownership", "Borrowing", "Collections", "Lifetimes"}
        found = {r["short_id"] for r in results}
        matched = expected_ids & found or any(
            any(eid in sid for eid in ["Ownership", "Collections", "Borrowing", "Lifetimes"])
            for sid in found
        )
        check("hybrid_search top-5 contains a core concept",
              bool(matched),
              "top: " + ", ".join(r["short_id"] for r in results))

    print(f"\n{CHECKS - len(FAILURES)}/{CHECKS} checks passed.")
    if FAILURES:
        print("FAILED:", ", ".join(FAILURES))
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
