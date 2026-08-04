#!/usr/bin/env python3
"""Semantic Alignment Pipeline — evaluate KG-RAG retrieval against annotated queries.

This script implements a lightweight RAG evaluation framework for the Rust
knowledge graph.  It does **not** require an LLM endpoint: alignment is measured
structurally by comparing retrieved KG entities / sources with a gold set.

Optional vector retrieval from ``kg_rag.py`` is imported lazily so the pipeline
remains runnable in any Python environment for smoke tests.

Example (structural evaluation, stdlib only):

    python tools/kg_rag/semantic_alignment_pipeline.py \
        --kg concept/00_meta/kg_data_v3.json \
        --eval tools/kg_rag/eval/rag_eval_set.json \
        --output reports/RAG_EVAL_2026_08_04.json

Example (with vector hybrid retrieval, requires venv):

    tools/kg_rag/.venv/Scripts/python tools/kg_rag/semantic_alignment_pipeline.py \
        --kg concept/00_meta/kg_data_v3.json \
        --eval tools/kg_rag/eval/rag_eval_set.json \
        --vector --top-k 10
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from kg_core import (
    KG_PATH,
    entity_text,
    get_lang_value,
    iter_entities,
    kg_adjacency,
    load_kg,
    short_id,
)

# Lazy import vector retrieval so stdlib-only smoke tests always work.
try:
    from kg_rag import hybrid_search

    _VECTOR_AVAILABLE = True
except Exception:  # pragma: no cover
    _VECTOR_AVAILABLE = False


ROOT = Path(__file__).resolve().parent
DEFAULT_EVAL = ROOT / "eval" / "rag_eval_set.json"

DEFAULT_PREDICATES = (
    "ex:dependsOn",
    "ex:refines",
    "ex:entails",
    "ex:partOf",
    "ex:hasPart",
    "ex:equivalentTo",
    "ex:counterExample",
)


def _normalize(text: str) -> str:
    return text.lower().strip(" \\t.,;:!?\"'")


def _label_values(entity: dict[str, Any], lang: str = "en") -> list[str]:
    out: list[str] = []
    for key in ("skos:prefLabel", "skos:altLabel", "skos:hiddenLabel"):
        for item in entity.get(key, []):
            if item.get("@language") == lang:
                out.append(item.get("@value", ""))
    return [v for v in out if v]


def entity_linking(
    kg: dict[str, Any],
    query: str,
    top_n: int = 5,
    lang: str = "en",
) -> list[dict[str, Any]]:
    """Link a query to KG entities via token-overlap on SKOS labels."""
    entities = iter_entities(kg)
    q_tokens = set(_normalize(query).split())
    if not q_tokens:
        return []

    scored: list[tuple[float, dict[str, Any]]] = []
    for entity in entities:
        labels = _label_values(entity, lang)
        if lang != "en":
            labels.extend(_label_values(entity, "en"))

        best = 0.0
        for label in labels:
            l_tokens = set(_normalize(label).split())
            if not l_tokens:
                continue
            inter = l_tokens & q_tokens
            score = len(inter) / max(len(q_tokens), len(l_tokens))
            best = max(best, score)

        if best > 0.0:
            scored.append((best, entity))

    scored.sort(key=lambda x: x[0], reverse=True)
    return [entity for _, entity in scored[:top_n]]


def _entity_path(entity: dict[str, Any]) -> str | None:
    """Return the concept/ path stored in the entity, if any."""
    for key in ("ex:path", "path"):
        value = entity.get(key)
        if value:
            return str(value)
    return None


def graph_retrieval(
    kg: dict[str, Any],
    seed_ids: list[str],
    hops: int = 2,
    predicates: tuple[str, ...] | None = None,
) -> set[str]:
    """Return entity IDs reachable from seeds within ``hops`` predicate-constrained steps."""
    if predicates is None:
        predicates = DEFAULT_PREDICATES
    entities = iter_entities(kg)
    adj = kg_adjacency(entities, kg)
    reachable: set[str] = set(seed_ids)
    frontier = set(seed_ids)
    for _ in range(hops):
        next_frontier: set[str] = set()
        for node in frontier:
            for pred, targets in adj.get(node, {}).items():
                if pred in predicates:
                    for target in targets:
                        if target not in reachable:
                            reachable.add(target)
                            next_frontier.add(target)
        frontier = next_frontier
        if not frontier:
            break
    return reachable


def _extract_sources(kg: dict[str, Any], entity_ids: set[str]) -> set[str]:
    """Collect ``ex:path`` / source annotations for a set of entity IDs."""
    sources: set[str] = set()
    by_id = {e["@id"]: e for e in iter_entities(kg)}
    for eid in entity_ids:
        entity = by_id.get(eid, {})
        path = _entity_path(entity)
        if path:
            sources.add(path)
        # Also pull RDF-star source annotations on relations touching this entity.
        for rel in kg.get("relations", []):
            if rel.get("ex:subject") == eid or rel.get("ex:object") == eid:
                annotation = rel.get("@annotation") or {}
                src = annotation.get("ex:source") or annotation.get("source")
                if src:
                    sources.add(str(src))
    return sources


def evaluate_sample(
    kg: dict[str, Any],
    sample: dict[str, Any],
    top_k: int = 5,
    hops: int = 2,
    use_vector: bool = False,
) -> dict[str, Any]:
    """Compute retrieval metrics for a single evaluation sample."""
    query = sample.get("query", "")
    expected_concepts = set(sample.get("expected_concepts", []))
    expected_sources = set(sample.get("expected_sources", []))

    # Seed entities via deterministic linking (always run).
    linked = entity_linking(kg, query, top_n=top_k)
    seed_ids = [e["@id"] for e in linked]

    retrieved_ids: set[str] = set(seed_ids)
    if use_vector and _VECTOR_AVAILABLE:
        try:
            vector_hits = hybrid_search(query, top_k=top_k)
            retrieved_ids |= {h["@id"] for h in vector_hits}
        except Exception as exc:  # pragma: no cover
            print(f"[warn] vector retrieval failed: {exc}", file=sys.stderr)

    # Expand graph around all retrieved seeds.
    graph_ids = graph_retrieval(kg, list(retrieved_ids), hops=hops)
    all_ids = retrieved_ids | graph_ids

    # Convert IDs to short human-readable labels for reporting.
    by_id = {e["@id"]: e for e in iter_entities(kg)}
    retrieved_labels = {
        short_id(eid)
        for eid in all_ids
        if eid in by_id
    }
    expected_labels = {
        c.lower().replace(" ", "_") for c in expected_concepts
    }

    # Sources.
    retrieved_sources = _extract_sources(kg, all_ids)

    # Metrics.
    concept_hits = retrieved_labels & expected_labels
    source_hits = retrieved_sources & expected_sources

    concept_recall = len(concept_hits) / len(expected_labels) if expected_labels else 1.0
    concept_precision = len(concept_hits) / len(retrieved_labels) if retrieved_labels else 0.0
    source_recall = len(source_hits) / len(expected_sources) if expected_sources else 1.0

    # Faithfulness proxy: do retrieved sources cover the expected sources?
    faithfulness = source_recall

    return {
        "query": query,
        "concept_recall": round(concept_recall, 3),
        "concept_precision": round(concept_precision, 3),
        "source_recall": round(source_recall, 3),
        "faithfulness": round(faithfulness, 3),
        "retrieved_entities": sorted(retrieved_labels),
        "retrieved_sources": sorted(retrieved_sources),
        "expected_entities": sorted(expected_labels),
        "expected_sources": sorted(expected_sources),
    }


def load_eval(path: Path) -> list[dict[str, Any]]:
    if not path.exists():
        return []
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    if isinstance(data, dict):
        return data.get("samples", [])
    return list(data)


def default_eval_set() -> list[dict[str, Any]]:
    """A tiny built-in eval set used when no external file is provided."""
    return [
        {
            "query": "how does ownership prevent data races",
            "expected_concepts": ["ownership", "borrowing", "data race"],
            "expected_sources": [
                "concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md",
                "concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md",
            ],
        },
        {
            "query": "why does async fn need Pin",
            "expected_concepts": ["async fn", "Future", "Pin", "self-referential"],
            "expected_sources": [
                "concept/03_advanced/01_async/01_async_await.md",
                "concept/03_advanced/01_async/02_pin_unpin.md",
            ],
        },
    ]


def run_evaluation(
    kg: dict[str, Any],
    samples: list[dict[str, Any]],
    top_k: int = 5,
    hops: int = 2,
    use_vector: bool = False,
) -> dict[str, Any]:
    results: list[dict[str, Any]] = []
    for sample in samples:
        results.append(
            evaluate_sample(
                kg,
                sample,
                top_k=top_k,
                hops=hops,
                use_vector=use_vector,
            )
        )

    if not results:
        return {"samples": [], "aggregates": {}}

    aggregates = {
        "concept_recall": round(sum(r["concept_recall"] for r in results) / len(results), 3),
        "concept_precision": round(sum(r["concept_precision"] for r in results) / len(results), 3),
        "source_recall": round(sum(r["source_recall"] for r in results) / len(results), 3),
        "faithfulness": round(sum(r["faithfulness"] for r in results) / len(results), 3),
        "n_samples": len(results),
    }
    return {"samples": results, "aggregates": aggregates}


def write_report(report: dict[str, Any], output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    with open(output, "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)
    print(f"[semantic_alignment_pipeline] wrote {output}")


def _format_markdown(report: dict[str, Any]) -> str:
    agg = report.get("aggregates", {})
    lines = [
        "# KG-RAG Semantic Alignment Evaluation Report",
        "",
        "## Aggregates",
        "",
        "| Metric | Value |",
        "|:---|---:|",
        f'| Concept Recall | {agg.get("concept_recall", 0.0)} |',
        f'| Concept Precision | {agg.get("concept_precision", 0.0)} |',
        f'| Source Recall | {agg.get("source_recall", 0.0)} |',
        f'| Faithfulness | {agg.get("faithfulness", 0.0)} |',
        f'| Samples | {agg.get("n_samples", 0)} |',
        "",
        "## Per-Sample Results",
        "",
    ]
    for sample in report.get("samples", []):
        lines.append(f"### {sample['query']}")
        lines.append("")
        lines.append(f"- concept_recall: {sample['concept_recall']}")
        lines.append(f"- concept_precision: {sample['concept_precision']}")
        lines.append(f"- source_recall: {sample['source_recall']}")
        lines.append(f"- faithfulness: {sample['faithfulness']}")
        lines.append(f"- retrieved_entities: {', '.join(sample['retrieved_entities'])}")
        lines.append(f"- expected_entities: {', '.join(sample['expected_entities'])}")
        lines.append("")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Evaluate KG-RAG semantic alignment against an annotated query set."
    )
    parser.add_argument("--kg", type=Path, default=KG_PATH, help="Path to kg_data_v3.json")
    parser.add_argument("--eval", type=Path, default=DEFAULT_EVAL, help="Path to eval JSON")
    parser.add_argument("--output", type=Path, help="JSON output path")
    parser.add_argument("--markdown", type=Path, help="Optional Markdown report path")
    parser.add_argument("--top-k", type=int, default=5, help="Top-K entities from linking")
    parser.add_argument("--hops", type=int, default=2, help="Graph expansion hops")
    parser.add_argument("--vector", action="store_true", help="Enable vector hybrid retrieval")
    parser.add_argument("--builtin", action="store_true", help="Use built-in tiny eval set")
    args = parser.parse_args(argv)

    kg = load_kg(args.kg)
    samples = default_eval_set() if args.builtin else load_eval(args.eval)
    if not samples:
        print(f"[warn] no eval samples found in {args.eval}; use --builtin", file=sys.stderr)

    if args.vector and not _VECTOR_AVAILABLE:
        print(
            "[warn] --vector requested but kg_rag.py unavailable; "
            "install tools/kg_rag/requirements.txt",
            file=sys.stderr,
        )

    report = run_evaluation(
        kg,
        samples,
        top_k=args.top_k,
        hops=args.hops,
        use_vector=args.vector,
    )

    print(json.dumps(report["aggregates"], ensure_ascii=False, indent=2))

    if args.output:
        write_report(report, args.output)
    if args.markdown:
        args.markdown.parent.mkdir(parents=True, exist_ok=True)
        args.markdown.write_text(_format_markdown(report), encoding="utf-8")
        print(f"[semantic_alignment_pipeline] wrote {args.markdown}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
