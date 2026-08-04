#!/usr/bin/env python3
"""Quick stratified evaluation of KG-RAG hybrid retrieval.

Stratifies golden_queries_v1.json by ``layer`` (used as a difficulty proxy),
draws 30 samples, runs ``kg_rag.hybrid_search`` for each query, and computes
``concept_recall@5`` and ``source_recall@5``.

Run inside the project venv so that numpy/sentence-transformers are available:

    tools/kg_rag/.venv/Scripts/python tools/kg_rag/eval/quick_eval.py
"""
from __future__ import annotations

import json
import random
import re
import sys
from collections import defaultdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))

from kg_core import get_lang_value, iter_entities, load_kg, short_id

try:
    from kg_rag import build_index, hybrid_search
except Exception as exc:  # pragma: no cover
    print(
        f"[quick_eval] Vector retrieval unavailable ({exc}); skipping evaluation.",
        file=sys.stderr,
    )
    sys.exit(0)

GOLDEN_PATH = Path(__file__).resolve().parent / "golden_queries_v1.json"
RESULT_PATH = Path(__file__).resolve().parent / "quick_eval_result.json"
SAMPLE_SIZE = 30
RANDOM_SEED = 20260804
TOP_K = 5


def normalize_name(s: str) -> str:
    """Strip non-alphanumeric characters and lower-case for fuzzy matching."""
    return re.sub(r"[^a-z0-9]+", "", s.lower())


def build_name_index(entities: list[dict[str, Any]]) -> dict[str, str]:
    """Map normalized short_id / EN label -> entity @id."""
    idx: dict[str, str] = {}
    for e in entities:
        eid = e["@id"]
        idx[normalize_name(short_id(eid))] = eid
        label = get_lang_value(e.get("skos:prefLabel", []), "en") or ""
        if label:
            idx[normalize_name(label)] = eid
    return idx


def resolve_concept(name: str, name_index: dict[str, str]) -> str | None:
    """Return the entity @id for an expected concept name, if resolvable."""
    nc = normalize_name(name)
    if not nc:
        return None
    if nc in name_index:
        return name_index[nc]
    # Fuzzy fallback: substring match against indexed names.
    for k, eid in name_index.items():
        if nc in k or k in nc:
            return eid
    return None


def resolve_source(src: str, path_to_id: dict[str, str]) -> str | None:
    """Return the entity @id for an expected source path, if resolvable."""
    path = src.removeprefix("concept/")
    return path_to_id.get(path)


def stratified_sample(
    samples: list[dict[str, Any]], key_fn: Any, n: int
) -> list[dict[str, Any]]:
    """Sample approximately ``n`` items preserving strata from ``key_fn``."""
    groups: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for s in samples:
        groups[key_fn(s)].append(s)

    base = n // len(groups)
    extra = n % len(groups)
    selected: list[dict[str, Any]] = []
    leftover: list[dict[str, Any]] = []
    for group in groups.values():
        random.shuffle(group)
        take = base + (1 if extra > 0 else 0)
        if extra > 0:
            extra -= 1
        selected.extend(group[:take])
        leftover.extend(group[take:])

    if len(selected) < n:
        random.shuffle(leftover)
        selected.extend(leftover[: n - len(selected)])
    random.shuffle(selected)
    return selected


def main() -> int:
    random.seed(RANDOM_SEED)

    kg = load_kg()
    entities = list(iter_entities(kg))
    entities_by_id = {e["@id"]: e for e in entities}
    name_index = build_name_index(entities)
    path_to_id = {
        e.get("ex:path", ""): e["@id"]
        for e in entities
        if e.get("ex:path")
    }

    with open(GOLDEN_PATH, "r", encoding="utf-8") as f:
        data = json.load(f)
    samples = data["samples"]

    print(f"[quick_eval] Loaded {len(samples)} golden queries; building index ...", file=sys.stderr)
    index, ents, model = build_index()

    selected = stratified_sample(samples, lambda s: s.get("layer", "unknown"), SAMPLE_SIZE)

    per_sample: list[dict[str, Any]] = []
    concept_recalls: list[float] = []
    source_recalls: list[float] = []
    unmatched_concepts = 0
    unmatched_sources = 0

    for i, s in enumerate(selected, 1):
        q = s["query"]
        exp_concepts = [
            resolve_concept(c, name_index) for c in s.get("expected_concepts", [])
        ]
        exp_sources = [
            resolve_source(src, path_to_id) for src in s.get("expected_sources", [])
        ]

        concept_ids = {eid for eid in exp_concepts if eid}
        source_ids = {eid for eid in exp_sources if eid}
        unmatched_concepts += sum(1 for eid in exp_concepts if not eid)
        unmatched_sources += sum(1 for eid in exp_sources if not eid)

        results = hybrid_search(q, model, index, ents, kg, top_k=TOP_K)
        result_ids = [r["id"] for r in results]

        c_hit = len(concept_ids & set(result_ids))
        s_hit = len(source_ids & set(result_ids))

        c_recall = c_hit / len(concept_ids) if concept_ids else 0.0
        s_recall = s_hit / len(source_ids) if source_ids else 0.0

        concept_recalls.append(c_recall)
        source_recalls.append(s_recall)

        per_sample.append(
            {
                "query": q,
                "layer": s.get("layer"),
                "domain": s.get("domain"),
                "origin": s.get("origin"),
                "result_ids": result_ids,
                "concept_hits": sorted(concept_ids & set(result_ids)),
                "source_hits": sorted(source_ids & set(result_ids)),
                "concept_recall@5": round(c_recall, 4),
                "source_recall@5": round(s_recall, 4),
            }
        )
        print(f"[quick_eval] {i}/{len(selected)}: {q[:60]!r} c={c_recall:.2f} s={s_recall:.2f}", file=sys.stderr)

    avg_concept = sum(concept_recalls) / len(concept_recalls) if concept_recalls else 0.0
    avg_source = sum(source_recalls) / len(source_recalls) if source_recalls else 0.0

    result: dict[str, Any] = {
        "metadata": {
            "sample_size": len(selected),
            "random_seed": RANDOM_SEED,
            "top_k": TOP_K,
            "kg_version": kg.get("metadata", {}).get("version"),
            "kg_entity_count": len(entities),
            "unmatched_expected_concepts": unmatched_concepts,
            "unmatched_expected_sources": unmatched_sources,
        },
        "metrics": {
            "concept_recall@5": round(avg_concept, 4),
            "source_recall@5": round(avg_source, 4),
        },
        "layer_breakdown": {},
        "samples": per_sample,
    }

    layer_groups: dict[str, list[int]] = defaultdict(list)
    for idx, s in enumerate(selected):
        layer_groups[s.get("layer", "unknown")].append(idx)
    for layer, idxs in sorted(layer_groups.items()):
        result["layer_breakdown"][layer] = {
            "count": len(idxs),
            "concept_recall@5": round(
                sum(concept_recalls[i] for i in idxs) / len(idxs), 4
            ),
            "source_recall@5": round(
                sum(source_recalls[i] for i in idxs) / len(idxs), 4
            ),
        }

    RESULT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(RESULT_PATH, "w", encoding="utf-8") as f:
        json.dump(result, f, ensure_ascii=False, indent=2)

    print(json.dumps(result["metrics"], ensure_ascii=False, indent=2))
    print(f"[quick_eval] Wrote detailed results to {RESULT_PATH}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
