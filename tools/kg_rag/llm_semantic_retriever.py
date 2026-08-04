"""
LLM Semantic Retriever — KG-RAG retrieval prototype for concept/ authority pages.

Reads ``concept/00_meta/kg_data_v3.json`` and produces a structured context
suitable for feeding into an LLM.  Supports:

* entity linking via SKOS labels (no vector deps required)
* predicate-constrained multi-hop subgraph expansion
* optional dense + graph hybrid retrieval via ``kg_rag.py``
* RDF-star provenance annotations turned into inline citations

Example (graph-only, stdlib Python):

    python tools/kg_rag/llm_semantic_retriever.py \
        --query "how does ownership prevent data races" --hops 2

Example (hybrid, requires venv):

    tools/kg_rag/.venv/Scripts/python tools/kg_rag/llm_semantic_retriever.py \
        --query "async runtime" --top-k 5 --hops 2 --vector
"""
from __future__ import annotations

import argparse
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

# kg_rag.py pulls in numpy/sentence-transformers.  Only import it when the
# user explicitly asks for vector retrieval so that graph-only usage works in
# any Python environment.
try:
    from kg_rag import build_index, hybrid_search

    _VECTOR_AVAILABLE = True
except Exception:  # pragma: no cover
    _VECTOR_AVAILABLE = False


def _normalize(text: str) -> str:
    return text.lower().strip(" \\t.,;:!?\"'")


def _label_values(entity: dict[str, Any], lang: str) -> list[str]:
    out: list[str] = []
    for key in ("skos:prefLabel", "skos:altLabel", "skos:hiddenLabel"):
        for item in entity.get(key, []):
            if item.get("@language") == lang:
                out.append(item.get("@value", ""))
    return [v for v in out if v]


def entity_linking(
    kg: dict[str, Any],
    query: str,
    lang: str = "en",
    top_n: int = 5,
) -> list[dict[str, Any]]:
    """Link a natural-language query to KG entities using SKOS labels.

    This is intentionally a lightweight, deterministic matcher.  In production
    it can be replaced by a dense embedding model or a few-shot LLM linker.
    """
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
            if score > best:
                best = score

        if best > 0.0:
            scored.append((best, entity))

    scored.sort(key=lambda x: x[0], reverse=True)
    return [entity for _, entity in scored[:top_n]]


def _relation_annotation(
    kg: dict[str, Any], subject: str, predicate: str, object: str
) -> dict[str, Any]:
    for rel in kg.get("relations", []):
        if (
            rel.get("ex:subject") == subject
            and rel.get("ex:predicate") == predicate
            and rel.get("ex:object") == object
        ):
            return rel.get("@annotation") or {}
    return {}


def subgraph_retrieval(
    adj: dict[str, dict[str, list[str]]],
    kg: dict[str, Any],
    seeds: list[str],
    hops: int = 2,
    predicates: tuple[str, ...] | None = None,
) -> list[dict[str, Any]]:
    """Expand a set of seed entities by ``hops`` predicate-constrained hops."""
    if hops <= 0:
        return []

    visited: set[str] = set(seeds)
    frontier: list[str] = list(seeds)
    results: list[dict[str, Any]] = []

    for _ in range(hops):
        next_frontier: list[str] = []
        for entity_id in frontier:
            for predicate, objects in adj.get(entity_id, {}).items():
                if predicates and predicate not in predicates:
                    continue
                for obj_id in objects:
                    annotation = _relation_annotation(
                        kg, entity_id, predicate, obj_id
                    )
                    results.append(
                        {
                            "subject": entity_id,
                            "predicate": predicate,
                            "object": obj_id,
                            "annotation": annotation,
                        }
                    )
                    if obj_id not in visited:
                        visited.add(obj_id)
                        next_frontier.append(obj_id)
        frontier = next_frontier

    return results


def _entity_lookup(
    entities: list[dict[str, Any]], entity_id: str
) -> dict[str, Any] | None:
    for entity in entities:
        if entity.get("@id") == entity_id:
            return entity
    return None


def _citation(annotation: dict[str, Any]) -> str:
    parts: list[str] = []
    if annotation.get("ex:derivedFromRFC"):
        parts.append(f"RFC {annotation['ex:derivedFromRFC']}")
    if annotation.get("ex:verifiedByCompiler"):
        parts.append(f"compiler={annotation['ex:verifiedByCompiler']}")
    if annotation.get("ex:documentedIn"):
        parts.append(f"doc={annotation['ex:documentedIn']}")
    if annotation.get("ex:source"):
        parts.append(f"src={annotation['ex:source']}")
    if annotation.get("ex:confidence") is not None:
        parts.append(f"conf={annotation['ex:confidence']}")
    return "; ".join(parts) if parts else "no citation"


def build_context(
    kg: dict[str, Any],
    triples: list[dict[str, Any]],
    linked_entities: list[dict[str, Any]],
    max_entities: int = 10,
) -> str:
    """Serialize retrieved triples and entity summaries into an LLM prompt."""
    entity_ids = {e["@id"] for e in linked_entities}
    for triple in triples:
        entity_ids.add(triple["subject"])
        entity_ids.add(triple["object"])

    entities = iter_entities(kg)
    entity_map = {eid: _entity_lookup(entities, eid) for eid in entity_ids}

    lines: list[str] = [
        "You are a Rust assistant. Answer using ONLY the following knowledge graph context.",
        "Cite each claim with [source: ...]. If the context is insufficient, say so.\n",
        "=== Linked Entities ===",
    ]
    for entity in linked_entities[:max_entities]:
        label = get_lang_value(entity.get("skos:prefLabel", []), "en") or short_id(
            entity["@id"]
        )
        summary = entity_text(entity)
        lines.append(f"- {label} ({short_id(entity['@id'])}): {summary}")

    lines.extend(["\n=== Retrieved Triples ==="])
    for triple in triples:
        subj = short_id(triple["subject"])
        pred = short_id(triple["predicate"])
        obj = short_id(triple["object"])
        cite = _citation(triple.get("annotation", {}))
        lines.append(f"- {subj} {pred} {obj}  [source: {cite}]")

    lines.extend(
        [
            "\n=== Instructions ===",
            "1. Prefer triples whose source includes RFC or compiler verification.",
            "2. Treat LLM-generated explanations (explainedByLLM) as tentative.",
            "3. Use short IDs when referring to concepts.",
        ]
    )
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Retrieve KG context for LLM generation."
    )
    parser.add_argument("--query", required=True, help="Natural language query.")
    parser.add_argument(
        "--kg", type=Path, default=KG_PATH, help="Path to kg_data_v3.json."
    )
    parser.add_argument("--top-k", type=int, default=5, help="Top-k entities.")
    parser.add_argument("--hops", type=int, default=2, help="Graph expansion hops.")
    parser.add_argument(
        "--alpha", type=float, default=0.75, help="Hybrid weight for vector score."
    )
    parser.add_argument(
        "--vector", action="store_true", help="Use dense + graph hybrid retrieval."
    )
    parser.add_argument(
        "--predicates",
        default="ex:dependsOn,ex:entails,ex:mutexWith,ex:refines,ex:equivalentTo,ex:counterExample",
        help="Comma-separated predicates for graph expansion.",
    )
    parser.add_argument(
        "--lang", default="en", help="Preferred language for entity linking."
    )
    args = parser.parse_args(argv)

    kg = load_kg(args.kg)
    adj = kg_adjacency(iter_entities(kg), kg)
    predicate_set = tuple(p.strip() for p in args.predicates.split(",") if p.strip())

    seed_ids: list[str] = []
    linked_entities: list[dict[str, Any]] = []

    if args.vector:
        if not _VECTOR_AVAILABLE:
            print(
                "ERROR: vector retrieval unavailable; install dependencies or omit --vector.",
                file=sys.stderr,
            )
            return 1
        index, entities, model = build_index(args.kg)
        results = hybrid_search(
            args.query,
            model,
            index,
            entities,
            kg,
            top_k=args.top_k,
            alpha=args.alpha,
            neighbour_predicates=predicate_set,
        )
        seed_ids = [r["id"] for r in results]
        linked_entities = [_entity_lookup(entities, eid) for eid in seed_ids]
        linked_entities = [e for e in linked_entities if e]
    else:
        linked_entities = entity_linking(kg, args.query, lang=args.lang, top_n=args.top_k)
        seed_ids = [e["@id"] for e in linked_entities]

    if not seed_ids:
        print("No linked entities found.", file=sys.stderr)
        return 0

    triples = subgraph_retrieval(
        adj, kg, seed_ids, hops=args.hops, predicates=predicate_set
    )

    context = build_context(kg, triples, linked_entities)
    print(context)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
