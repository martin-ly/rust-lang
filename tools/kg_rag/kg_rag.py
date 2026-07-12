"""
KG-RAG: Hybrid semantic search over the Rust knowledge graph.

Reads ``concept/00_meta/kg_data_v3.json``, embeds entity summaries in English,
builds a lightweight numpy vector index, and supports hybrid retrieval that
combines dense similarity with KG structure (``dependsOn`` neighbours).

Data-access helpers live in ``kg_core.py`` (stdlib-only) so that structural
validation (``smoke_test.py``) does not require the heavy vector deps.
"""
from __future__ import annotations

import argparse
import json
import os
import pickle
import sys
from pathlib import Path
from typing import Any

# Re-execute inside the project venv when dependencies are missing.
ROOT = Path(__file__).resolve().parent
VENV_PYTHON = ROOT / ".venv" / "Scripts" / "python.exe"


def _ensure_venv() -> None:
    try:
        import numpy  # noqa: F401
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

import numpy as np  # noqa: E402
from sentence_transformers import SentenceTransformer  # noqa: E402

from kg_core import (  # noqa: E402
    KG_PATH,
    entity_summary,
    entity_text,
    get_lang_value,
    iter_entities,
    kg_adjacency,
    kg_paths,
    load_kg,
    short_id,
)

CACHE_DIR = ROOT / ".cache"
INDEX_PATH = CACHE_DIR / "index.pkl"
EMBEDDING_MODEL = "all-MiniLM-L6-v2"
DEFAULT_ALPHA = 0.75


def _fingerprint(kg_path: Path, entity_count: int) -> dict[str, Any]:
    """Cache key: model + absolute KG path + KG file mtime + entity count.

    Guards against stale caches when kg_data_v3.json is regenerated (the
    previous key only compared the path string and silently served outdated
    embeddings).
    """
    stat = kg_path.stat()
    return {
        "model": EMBEDDING_MODEL,
        "kg_path": str(kg_path.resolve()),
        "kg_mtime_ns": stat.st_mtime_ns,
        "entity_count": entity_count,
    }


def build_index(
    kg_path: Path | str = KG_PATH,
    model_name: str = EMBEDDING_MODEL,
    cache_path: Path | str = INDEX_PATH,
    force: bool = False,
) -> tuple[np.ndarray, list[dict[str, Any]], SentenceTransformer]:
    """Build or load the vector index for the knowledge graph."""
    kg_path = Path(kg_path)
    cache_path = Path(cache_path)
    cache_path.parent.mkdir(parents=True, exist_ok=True)

    kg = load_kg(kg_path)
    entities = iter_entities(kg)
    fingerprint = _fingerprint(kg_path, len(entities))
    fingerprint["model"] = model_name

    if not force and cache_path.exists():
        try:
            with open(cache_path, "rb") as f:
                cached = pickle.load(f)
            if cached.get("fingerprint") == fingerprint:
                print(f"[kg_rag] Loaded cached index from {cache_path}", file=sys.stderr)
                return cached["vectors"], cached["entities"], SentenceTransformer(model_name)
            print("[kg_rag] Cache fingerprint mismatch, rebuilding.", file=sys.stderr)
        except Exception as exc:
            print(f"[kg_rag] Cache load failed ({exc}), rebuilding.", file=sys.stderr)

    print(f"[kg_rag] Loading model {model_name} ...", file=sys.stderr)
    model = SentenceTransformer(model_name)

    texts = [entity_text(e) for e in entities]

    print(f"[kg_rag] Encoding {len(texts)} entities ...", file=sys.stderr)
    vectors = model.encode(texts, show_progress_bar=True, convert_to_numpy=True)
    vectors = np.asarray(vectors, dtype=np.float32)
    # L2-normalise for cosine similarity via dot product.
    norms = np.linalg.norm(vectors, axis=1, keepdims=True)
    norms[norms == 0] = 1.0
    vectors = vectors / norms

    cache = {
        "fingerprint": fingerprint,
        "vectors": vectors,
        "entities": entities,
    }
    with open(cache_path, "wb") as f:
        pickle.dump(cache, f)
    print(f"[kg_rag] Saved index to {cache_path}", file=sys.stderr)

    return vectors, entities, model


def cosine_scores(query_vec: np.ndarray, index: np.ndarray) -> np.ndarray:
    """Return cosine similarity scores for a normalised query vector."""
    return np.dot(index, query_vec)


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
