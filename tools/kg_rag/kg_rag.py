"""
KG-RAG: Hybrid semantic search over the Rust knowledge graph.

Reads ``concept/00_meta/kg_data_v3.json``, embeds entity summaries in English,
builds a lightweight numpy vector index, and supports hybrid retrieval that
combines dense similarity with KG structure (``dependsOn`` neighbours).
"""
from __future__ import annotations

import argparse
import json
import math
import os
import pickle
import sys
from pathlib import Path
from typing import Any

import numpy as np

# Re-execute inside the project venv when dependencies are missing.
ROOT = Path(__file__).resolve().parent
VENV_PYTHON = ROOT / ".venv" / "Scripts" / "python.exe"


def _ensure_venv() -> None:
    try:
        import sentence_transformers  # noqa: F401
        import sklearn  # noqa: F401
    except ImportError:
        if VENV_PYTHON.exists() and sys.executable != str(VENV_PYTHON):
            os.execv(str(VENV_PYTHON), [str(VENV_PYTHON)] + sys.argv)
        print(
            "ERROR: missing dependencies. Run:\n"
            "  cd tools/kg_rag && .venv/Scripts/pip install -r requirements.txt",
            file=sys.stderr,
        )
        sys.exit(1)


_ensure_venv()

from sentence_transformers import SentenceTransformer  # noqa: E402

KG_PATH = Path("concept/00_meta/kg_data_v3.json")
CACHE_DIR = ROOT / ".cache"
INDEX_PATH = CACHE_DIR / "index.pkl"
EMBEDDING_MODEL = "all-MiniLM-L6-v2"
DEFAULT_ALPHA = 0.75


def load_kg(path: Path | str = KG_PATH) -> dict[str, Any]:
    """Load the JSON-LD knowledge graph (v3; v2 grouped layout also accepted)."""
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def iter_entities(kg: dict[str, Any]) -> list[dict[str, Any]]:
    """Flatten all entities (concepts, theories, models, primitives, ...).

    Supports both the v3 flat list layout and the legacy v2 layout where
    entities were grouped by category in a dict.
    """
    raw = kg.get("entities", [])
    entities: list[dict[str, Any]] = []
    if isinstance(raw, list):  # v3: flat list of entities
        for item in raw:
            item.setdefault("_category", item.get("@type", "unknown").removeprefix("ex:").lower() + "s")
            entities.append(item)
    else:  # v2 legacy: {category: [entities]}
        for category, items in raw.items():
            for item in items:
                item["_category"] = category
                entities.append(item)
    return entities


def get_lang_value(values: list[dict[str, str]], lang: str) -> str | None:
    for v in values:
        if v.get("@language") == lang:
            return v.get("@value")
    return None


def entity_summary(entity: dict[str, Any]) -> str | None:
    """Return the English summary of an entity.

    v3 entities use ``skos:scopeNote``; legacy v2 entities used
    ``skos:definition``. Fall back to the short id when neither exists.
    """
    return (
        get_lang_value(entity.get("skos:definition", []), "en")
        or get_lang_value(entity.get("skos:scopeNote", []), "en")
    )


def entity_text(entity: dict[str, Any]) -> str:
    """Return the English summary text used for embedding."""
    parts: list[str] = []
    label = get_lang_value(entity.get("skos:prefLabel", []), "en")
    if label:
        parts.append(label)
    summary = entity_summary(entity)
    if summary:
        parts.append(summary)
    alt = get_lang_value(entity.get("skos:altLabel", []), "en")
    if alt:
        parts.append(f"({alt})")
    return " ".join(parts)


def short_id(uri: str) -> str:
    return uri.removeprefix("ex:")


def build_index(
    kg_path: Path | str = KG_PATH,
    model_name: str = EMBEDDING_MODEL,
    cache_path: Path | str = INDEX_PATH,
    force: bool = False,
) -> tuple[np.ndarray, list[dict[str, Any]], SentenceTransformer]:
    """Build or load the vector index for the knowledge graph."""
    cache_path = Path(cache_path)
    cache_path.parent.mkdir(parents=True, exist_ok=True)

    if not force and cache_path.exists():
        try:
            with open(cache_path, "rb") as f:
                cached = pickle.load(f)
            if cached.get("model") == model_name and cached.get("kg_path") == str(kg_path):
                print(f"[kg_rag] Loaded cached index from {cache_path}", file=sys.stderr)
                return cached["vectors"], cached["entities"], SentenceTransformer(model_name)
        except Exception as exc:
            print(f"[kg_rag] Cache load failed ({exc}), rebuilding.", file=sys.stderr)

    print(f"[kg_rag] Loading model {model_name} ...", file=sys.stderr)
    model = SentenceTransformer(model_name)

    kg = load_kg(kg_path)
    entities = iter_entities(kg)
    texts = [entity_text(e) for e in entities]

    print(f"[kg_rag] Encoding {len(texts)} entities ...", file=sys.stderr)
    vectors = model.encode(texts, show_progress_bar=True, convert_to_numpy=True)
    vectors = np.asarray(vectors, dtype=np.float32)
    # L2-normalise for cosine similarity via dot product.
    norms = np.linalg.norm(vectors, axis=1, keepdims=True)
    norms[norms == 0] = 1.0
    vectors = vectors / norms

    cache = {"model": model_name, "kg_path": str(kg_path), "vectors": vectors, "entities": entities}
    with open(cache_path, "wb") as f:
        pickle.dump(cache, f)
    print(f"[kg_rag] Saved index to {cache_path}", file=sys.stderr)

    return vectors, entities, model


def cosine_scores(query_vec: np.ndarray, index: np.ndarray) -> np.ndarray:
    """Return cosine similarity scores for a normalised query vector."""
    return np.dot(index, query_vec)


def kg_adjacency(entities: list[dict[str, Any]], kg: dict[str, Any]) -> dict[str, dict[str, list[str]]]:
    """Build adjacency per entity: {id: {predicate: [object_id]}}."""
    adj: dict[str, dict[str, list[str]]] = {e["@id"]: {} for e in entities}
    for rel in kg.get("relations", []):
        subj = rel.get("ex:subject", "")
        pred = rel.get("ex:predicate", "")
        obj = rel.get("ex:object", "")
        if subj and pred and obj:
            adj.setdefault(subj, {}).setdefault(pred, []).append(obj)
    return adj


def kg_paths(adj: dict[str, dict[str, list[str]]], entity_id: str, max_depth: int = 2) -> list[str]:
    """Return short KG paths rooted at ``entity_id`` with readable IDs."""
    paths: list[str] = []
    seen = set()

    def fmt(uri: str) -> str:
        return short_id(uri)

    def walk(current: str, depth: int, trail: list[str]) -> None:
        if depth > max_depth:
            return
        for pred, objects in adj.get(current, {}).items():
            for obj in objects:
                path_str = " -> ".join(trail + [fmt(pred), fmt(obj)])
                if path_str not in seen:
                    seen.add(path_str)
                    paths.append(path_str)
                if depth + 1 <= max_depth:
                    walk(obj, depth + 1, trail + [fmt(pred), fmt(obj)])

    walk(entity_id, 1, [fmt(entity_id)])
    return paths[:10]


def hybrid_search(
    query: str,
    model: SentenceTransformer,
    index: np.ndarray,
    entities: list[dict[str, Any]],
    kg: dict[str, Any],
    top_k: int = 5,
    alpha: float = DEFAULT_ALPHA,
    neighbour_predicates: tuple[str, ...] = ("ex:dependsOn", "ex:equivalentTo"),
) -> list[dict[str, Any]]:
    """Hybrid retrieval combining dense similarity and KG neighbour signals."""
    query_vec = model.encode([query], convert_to_numpy=True)[0]
    query_vec = query_vec.astype(np.float32)
    qnorm = np.linalg.norm(query_vec)
    if qnorm > 0:
        query_vec = query_vec / qnorm

    vector_scores = cosine_scores(query_vec, index)
    n = len(entities)

    # Graph signal: average vector similarity of outgoing neighbours.
    adj = kg_adjacency(entities, kg)
    id_to_idx = {e["@id"]: i for i, e in enumerate(entities)}
    graph_scores = np.zeros(n, dtype=np.float32)

    for i, entity in enumerate(entities):
        eid = entity["@id"]
        neighbour_scores: list[float] = []
        for pred in neighbour_predicates:
            for obj in adj.get(eid, {}).get(pred, []):
                if obj in id_to_idx:
                    neighbour_scores.append(float(vector_scores[id_to_idx[obj]]))
        if neighbour_scores:
            graph_scores[i] = float(np.mean(neighbour_scores))

    # Combine; both scores are in [0, 1].
    combined = alpha * vector_scores + (1 - alpha) * graph_scores
    top_indices = np.argsort(-combined)[:top_k]

    results: list[dict[str, Any]] = []
    for idx in top_indices:
        entity = entities[idx]
        results.append(
            {
                "id": entity["@id"],
                "short_id": short_id(entity["@id"]),
                "label": get_lang_value(entity.get("skos:prefLabel", []), "en"),
                "label_zh": get_lang_value(entity.get("skos:prefLabel", []), "zh"),
                "definition": entity_summary(entity),
                "category": entity.get("_category", "unknown"),
                "vector_score": round(float(vector_scores[idx]), 4),
                "graph_score": round(float(graph_scores[idx]), 4),
                "combined_score": round(float(combined[idx]), 4),
                "kg_paths": kg_paths(adj, entity["@id"]),
            }
        )
    return results


def format_results(results: list[dict[str, Any]]) -> str:
    lines: list[str] = []
    lines.append(f"{'Rank':<6}{'Label':<22}{'Vec':>8}{'Graph':>8}{'Combined':>10}")
    lines.append("-" * 60)
    for rank, r in enumerate(results, 1):
        label = (r["label"] or r["short_id"])[:20]
        lines.append(
            f"{rank:<6}{label:<22}{r['vector_score']:>8.4f}"
            f"{r['graph_score']:>8.4f}{r['combined_score']:>10.4f}"
        )
        lines.append(f"       {r['definition'] or ''}")
        for p in r["kg_paths"]:
            lines.append(f"       → {p}")
        lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="KG-RAG semantic search over rust-lang KG.")
    parser.add_argument("--query", required=True, help="Natural language query.")
    parser.add_argument("--top-k", type=int, default=5, help="Number of top results.")
    parser.add_argument("--alpha", type=float, default=DEFAULT_ALPHA, help="Vector weight in hybrid score.")
    parser.add_argument("--kg", default=str(KG_PATH), help="Path to kg_data_v3.json.")
    parser.add_argument("--rebuild", action="store_true", help="Force rebuild the embedding index.")
    parser.add_argument("--json", action="store_true", help="Output raw JSON instead of formatted text.")
    args = parser.parse_args()

    if not 0.0 <= args.alpha <= 1.0:
        print("--alpha must be between 0 and 1", file=sys.stderr)
        return 1

    index, entities, model = build_index(kg_path=args.kg, force=args.rebuild)
    kg = load_kg(args.kg)
    results = hybrid_search(
        query=args.query,
        model=model,
        index=index,
        entities=entities,
        kg=kg,
        top_k=args.top_k,
        alpha=args.alpha,
    )

    if args.json:
        print(json.dumps(results, ensure_ascii=False, indent=2))
    else:
        print(format_results(results))
    return 0


if __name__ == "__main__":
    sys.exit(main())
