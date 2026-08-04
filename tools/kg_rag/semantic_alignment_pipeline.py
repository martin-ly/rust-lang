#!/usr/bin/env python3
"""Semantic Alignment Pipeline — evaluate KG-RAG retrieval against annotated queries.

This script implements a lightweight RAG evaluation framework for the Rust
knowledge graph.  It supports multiple retrieval modes:

1. **Structural** (stdlib only): entity linking via SKOS label token overlap.
2. **Local vector**: dense embeddings from ``sentence-transformers``.
3. **OpenAI-compatible API**: embeddings from any OpenAI-compatible endpoint
   (OpenAI, Azure OpenAI, vLLM, Ollama with OpenAI compatibility, etc.).
4. **Hybrid BM25 + vector**: sparse lexical retrieval fused with dense retrieval.
5. **Optional reranker**: a cross-encoder reranks the hybrid candidate pool.

Metrics include standard RAG/IR metrics: recall@k, MRR, NDCG, precision,
faithfulness, and source recall.

Example (structural evaluation, stdlib only):

    python tools/kg_rag/semantic_alignment_pipeline.py \
        --kg concept/00_meta/kg_data_v3.json \
        --eval tools/kg_rag/eval/rag_eval_set.json \
        --output reports/RAG_EVAL_2026_08_04.json

Example (local sentence-transformer model):

    tools/kg_rag/.venv/Scripts/python tools/kg_rag/semantic_alignment_pipeline.py \
        --kg concept/00_meta/kg_data_v3.json \
        --eval tools/kg_rag/eval/rag_eval_set.json \
        --embed-provider sentence-transformers \
        --embed-model all-MiniLM-L6-v2 \
        --top-k 10 \
        --markdown reports/RAG_EVALUATION_BASELINE_2026_08.md

Example (OpenAI-compatible endpoint):

    export OPENAI_API_KEY=...
    export OPENAI_BASE_URL=https://api.openai.com/v1
    tools/kg_rag/.venv/Scripts/python tools/kg_rag/semantic_alignment_pipeline.py \
        --kg concept/00_meta/kg_data_v3.json \
        --eval tools/kg_rag/eval/rag_eval_set.json \
        --embed-provider openai \
        --embed-model text-embedding-3-small \
        --top-k 10

Example (hybrid with optional reranker):

    tools/kg_rag/.venv/Scripts/python tools/kg_rag/semantic_alignment_pipeline.py \
        --kg concept/00_meta/kg_data_v3.json \
        --eval tools/kg_rag/eval/golden_queries_v1.json \
        --embed-provider sentence-transformers \
        --embed-model all-MiniLM-L6-v2 \
        --hybrid --bm25-weight 0.3 \
        --reranker cross-encoder/ms-marco-MiniLM-L-6-v2 \
        --reranker-top-k 20 \
        --top-k 5 \
        --markdown reports/P10_RAG_PRODUCTION_EVALUATION_2026_08.md
"""
from __future__ import annotations

import argparse
import json
import math
import os
import re
import sys
from abc import ABC, abstractmethod
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

# Optional dependencies are loaded lazily so stdlib-only smoke tests always work.
try:
    import numpy as np

    _NUMPY_AVAILABLE = True
except Exception:  # pragma: no cover
    _NUMPY_AVAILABLE = False

try:
    from sentence_transformers import SentenceTransformer

    _ST_AVAILABLE = True
except Exception:  # pragma: no cover
    _ST_AVAILABLE = False

try:
    import openai

    _OPENAI_AVAILABLE = True
except Exception:  # pragma: no cover
    _OPENAI_AVAILABLE = False

try:
    from rank_bm25 import BM25Okapi

    _BM25_AVAILABLE = True
except Exception:  # pragma: no cover
    _BM25_AVAILABLE = False

try:
    from sentence_transformers.cross_encoder import CrossEncoder

    _RERANKER_AVAILABLE = True
except Exception:  # pragma: no cover
    _RERANKER_AVAILABLE = False


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

METRIC_KS = (1, 3, 5, 10)


# ---------------------------------------------------------------------------
# Embedding providers
# ---------------------------------------------------------------------------


class EmbeddingProvider(ABC):
    """Abstract base for embedding providers."""

    @abstractmethod
    def encode(self, texts: list[str]) -> Any:
        """Return an array-like of shape (n_texts, dim)."""
        ...

    @property
    @abstractmethod
    def name(self) -> str:
        ...


class SentenceTransformerProvider(EmbeddingProvider):
    """Local embeddings via ``sentence-transformers``."""

    def __init__(self, model_name: str = "all-MiniLM-L6-v2"):
        if not _ST_AVAILABLE or not _NUMPY_AVAILABLE:
            raise RuntimeError(
                "sentence-transformers and numpy are required for local embeddings; "
                "install tools/kg_rag/requirements.txt"
            )
        self.model_name = model_name
        self.model = SentenceTransformer(model_name)

    def encode(self, texts: list[str]) -> Any:
        return self.model.encode(texts, convert_to_numpy=True, show_progress_bar=False)

    @property
    def name(self) -> str:
        return f"sentence-transformers:{self.model_name}"


class OpenAICompatibleProvider(EmbeddingProvider):
    """Embeddings from any OpenAI-compatible ``/embeddings`` endpoint."""

    def __init__(
        self,
        api_key: str | None = None,
        base_url: str | None = None,
        model: str = "text-embedding-3-small",
    ):
        if not _OPENAI_AVAILABLE:
            raise RuntimeError(
                "openai package is required for OpenAI-compatible embeddings; "
                "install it with: pip install openai"
            )
        self.model = model
        self.client = openai.OpenAI(api_key=api_key, base_url=base_url)

    def encode(self, texts: list[str]) -> Any:
        response = self.client.embeddings.create(input=texts, model=self.model)
        vectors = [item.embedding for item in response.data]
        if _NUMPY_AVAILABLE:
            return np.asarray(vectors, dtype=np.float32)
        return vectors

    @property
    def name(self) -> str:
        return f"openai:{self.model}"


def create_embedding_provider(
    provider: str | None = None,
    model: str | None = None,
    api_key: str | None = None,
    base_url: str | None = None,
) -> EmbeddingProvider | None:
    """Factory selecting an embedding provider by name or environment variables.

    Environment variables:
      - ``KG_RAG_EMBED_PROVIDER``: ``sentence-transformers`` (default), ``openai``, ``none``
      - ``KG_RAG_EMBED_MODEL``: model name (provider-specific default applies if unset)
      - ``OPENAI_API_KEY`` / ``OPENAI_BASE_URL``: OpenAI-compatible endpoint credentials
    """
    provider = provider or os.environ.get("KG_RAG_EMBED_PROVIDER", "sentence-transformers")
    if provider == "none":
        return None
    if provider == "sentence-transformers":
        model = model or os.environ.get("KG_RAG_EMBED_MODEL", "all-MiniLM-L6-v2")
        return SentenceTransformerProvider(model)
    if provider == "openai":
        model = model or os.environ.get("KG_RAG_EMBED_MODEL", "text-embedding-3-small")
        api_key = api_key or os.environ.get("OPENAI_API_KEY")
        base_url = base_url or os.environ.get("OPENAI_BASE_URL")
        return OpenAICompatibleProvider(api_key=api_key, base_url=base_url, model=model)
    raise ValueError(f"Unknown embedding provider: {provider}")


# ---------------------------------------------------------------------------
# Vector index
# ---------------------------------------------------------------------------


class VectorIndex:
    """Simple L2-normalised dense index over KG entities."""

    def __init__(
        self,
        entities: list[dict[str, Any]],
        vectors: Any,
        provider_name: str,
    ):
        self.entities = entities
        self.vectors = vectors
        self.provider_name = provider_name
        if _NUMPY_AVAILABLE:
            self.vectors = np.asarray(vectors, dtype=np.float32)
            norms = np.linalg.norm(self.vectors, axis=1, keepdims=True)
            norms[norms == 0] = 1.0
            self.vectors = self.vectors / norms

    @classmethod
    def build(
        cls,
        kg: dict[str, Any],
        provider: EmbeddingProvider,
    ) -> "VectorIndex":
        entities = iter_entities(kg)
        texts = [entity_text(e) for e in entities]
        print(f"[semantic_alignment_pipeline] encoding {len(texts)} entities with {provider.name}", file=sys.stderr)
        vectors = provider.encode(texts)
        return cls(entities, vectors, provider.name)

    def search(self, query: str, provider: EmbeddingProvider, top_k: int = 5) -> list[dict[str, Any]]:
        query_vec = provider.encode([query])
        if _NUMPY_AVAILABLE:
            query_vec = np.asarray(query_vec, dtype=np.float32)
            qnorm = np.linalg.norm(query_vec)
            if qnorm > 0:
                query_vec = query_vec / qnorm
            scores = np.dot(self.vectors, query_vec.T).flatten()
            top_indices = np.argsort(-scores)[:top_k]
            return [
                {
                    "entity": self.entities[i],
                    "score": round(float(scores[i]), 4),
                }
                for i in top_indices
            ]
        # Fallback for rare no-numpy OpenAI-only environments.
        scores = [
            sum(a * b for a, b in zip(vec, query_vec[0]))
            for vec in self.vectors
        ]
        ranked = sorted(enumerate(scores), key=lambda x: x[1], reverse=True)[:top_k]
        return [{"entity": self.entities[i], "score": round(float(s), 4)} for i, s in ranked]


# ---------------------------------------------------------------------------
# BM25 lexical index
# ---------------------------------------------------------------------------


def _tokenize(text: str) -> list[str]:
    """Simple whitespace/token-based tokenizer for BM25."""
    return re.findall(r"[a-z0-9_]+", text.lower())


class BM25Index:
    """Sparse lexical index over KG entity texts (requires ``rank-bm25``)."""

    def __init__(self, entities: list[dict[str, Any]], corpus: list[list[str]]):
        self.entities = entities
        self.corpus = corpus
        if _BM25_AVAILABLE:
            self.index = BM25Okapi(corpus)
        else:
            self.index = None

    @classmethod
    def build(cls, kg: dict[str, Any]) -> "BM25Index":
        entities = iter_entities(kg)
        corpus = [_tokenize(entity_text(e)) for e in entities]
        return cls(entities, corpus)

    def search(self, query: str, top_k: int = 5) -> list[dict[str, Any]]:
        if not _BM25_AVAILABLE or self.index is None:
            return []
        tokens = _tokenize(query)
        scores = self.index.get_scores(tokens)
        if _NUMPY_AVAILABLE:
            top_indices = np.argsort(-scores)[:top_k]
        else:
            indexed = sorted(enumerate(scores), key=lambda x: x[1], reverse=True)[:top_k]
            top_indices = [i for i, _ in indexed]
        return [
            {"entity": self.entities[i], "score": round(float(scores[i]), 4)}
            for i in top_indices
        ]


# ---------------------------------------------------------------------------
# Hybrid retriever (BM25 + vector + optional reranker)
# ---------------------------------------------------------------------------


class HybridRetriever:
    """Combine dense, sparse, and optional cross-encoder reranking."""

    def __init__(
        self,
        vector_index: VectorIndex,
        bm25_index: BM25Index | None,
        provider: EmbeddingProvider,
        bm25_weight: float = 0.3,
        reranker: Any | None = None,
        reranker_top_k: int = 20,
    ):
        self.vector_index = vector_index
        self.bm25_index = bm25_index
        self.provider = provider
        self.bm25_weight = bm25_weight
        self.reranker = reranker
        self.reranker_top_k = reranker_top_k

    def _fuse(
        self,
        vector_hits: list[dict[str, Any]],
        bm25_hits: list[dict[str, Any]],
        top_k: int,
    ) -> list[dict[str, Any]]:
        """Fuse vector and BM25 rankings with reciprocal rank / min-max score fusion."""
        by_id: dict[str, dict[str, Any]] = {}

        def _min_max_scale(values: list[float]) -> list[float]:
            if not values:
                return []
            lo, hi = min(values), max(values)
            if hi - lo < 1e-9:
                return [0.5 for _ in values]
            return [(v - lo) / (hi - lo) for v in values]

        vec_scores = [h["score"] for h in vector_hits]
        vec_scaled = _min_max_scale(vec_scores)
        for hit, sc in zip(vector_hits, vec_scaled):
            eid = hit["entity"]["@id"]
            by_id[eid] = {
                "entity": hit["entity"],
                "vector_score": sc,
                "bm25_score": 0.0,
            }

        bm25_scores = [h["score"] for h in bm25_hits]
        bm25_scaled = _min_max_scale(bm25_scores)
        for hit, sc in zip(bm25_hits, bm25_scaled):
            eid = hit["entity"]["@id"]
            if eid in by_id:
                by_id[eid]["bm25_score"] = sc
            else:
                by_id[eid] = {
                    "entity": hit["entity"],
                    "vector_score": 0.0,
                    "bm25_score": sc,
                }

        alpha = self.bm25_weight
        for item in by_id.values():
            item["score"] = round(
                (1 - alpha) * item["vector_score"] + alpha * item["bm25_score"], 4
            )

        ranked = sorted(by_id.values(), key=lambda x: x["score"], reverse=True)
        return ranked[:top_k]

    def _rerank(
        self, query: str, candidates: list[dict[str, Any]]
    ) -> list[dict[str, Any]]:
        if self.reranker is None or not candidates:
            return candidates
        texts = [entity_text(c["entity"]) for c in candidates]
        pairs = [[query, t] for t in texts]
        scores = self.reranker.predict(pairs)
        for c, sc in zip(candidates, scores):
            c["reranker_score"] = round(float(sc), 4)
            c["score"] = round(float(sc), 4)
        return sorted(candidates, key=lambda x: x["score"], reverse=True)

    def search(self, query: str, top_k: int = 5) -> list[dict[str, Any]]:
        vector_hits = self.vector_index.search(query, self.provider, top_k=self.reranker_top_k)
        bm25_hits: list[dict[str, Any]] = []
        if self.bm25_index is not None:
            bm25_hits = self.bm25_index.search(query, top_k=self.reranker_top_k)

        fused = self._fuse(vector_hits, bm25_hits, top_k=self.reranker_top_k)
        if self.reranker is not None:
            fused = self._rerank(query, fused)
        return fused[:top_k]


# ---------------------------------------------------------------------------
# Entity linking and graph retrieval
# ---------------------------------------------------------------------------


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


# ---------------------------------------------------------------------------
# Metrics
# ---------------------------------------------------------------------------


def _label_key(label: str) -> str:
    return _normalize(label).replace(" ", "_")


def _source_key(path: str) -> str:
    """Normalize source paths by stripping a leading ``concept/`` prefix."""
    return path.removeprefix("concept/")


def _ranked_concepts(kg: dict[str, Any], ranked_entities: list[dict[str, Any]]) -> list[str]:
    """Return normalized concept labels in rank order."""
    by_id = {e["@id"]: e for e in iter_entities(kg)}
    seen: set[str] = set()
    out: list[str] = []
    for item in ranked_entities:
        entity = item.get("entity") or item
        eid = entity.get("@id")
        if not eid:
            continue
        entity = by_id.get(eid, entity)
        label = get_lang_value(entity.get("skos:prefLabel", []), "en") or short_id(eid)
        key = _label_key(label)
        if key not in seen:
            seen.add(key)
            out.append(key)
    return out


def _ranked_sources(kg: dict[str, Any], ranked_entities: list[dict[str, Any]]) -> list[str]:
    """Return source paths in rank order (entities first, then relation annotations)."""
    by_id = {e["@id"]: e for e in iter_entities(kg)}
    seen: set[str] = set()
    out: list[str] = []
    for item in ranked_entities:
        entity = item.get("entity") or item
        eid = entity.get("@id")
        if not eid:
            continue
        entity = by_id.get(eid, entity)
        path = _entity_path(entity)
        if path:
            key = _source_key(path)
            if key not in seen:
                seen.add(key)
                out.append(key)
        for rel in kg.get("relations", []):
            if rel.get("ex:subject") == eid or rel.get("ex:object") == eid:
                annotation = rel.get("@annotation") or {}
                src = annotation.get("ex:source") or annotation.get("source")
                if src:
                    key = _source_key(str(src))
                    if key not in seen:
                        seen.add(key)
                        out.append(key)
    return out


def recall_at_k(retrieved: list[str], expected: set[str], k: int) -> float:
    if not expected:
        return 1.0
    top = set(retrieved[:k])
    return len(top & expected) / len(expected)


def precision_at_k(retrieved: list[str], expected: set[str], k: int) -> float:
    top = retrieved[:k]
    if not top:
        return 0.0
    return len(set(top) & expected) / len(top)


def mrr(retrieved: list[str], expected: set[str]) -> float:
    """Mean Reciprocal Rank of the first relevant item."""
    for i, item in enumerate(retrieved, start=1):
        if item in expected:
            return 1.0 / i
    return 0.0


def ndcg_at_k(retrieved: list[str], expected: set[str], k: int) -> float:
    """NDCG with binary relevance: 1 if item is in expected set, else 0."""
    if not expected:
        return 1.0
    top = retrieved[:k]
    dcg = sum(
        (1.0 if item in expected else 0.0) / math.log2(i + 1)
        for i, item in enumerate(top, start=1)
    )
    # Ideal ranking places all expected items first.
    ideal_hits = min(len(expected), k)
    idcg = sum(1.0 / math.log2(i + 1) for i in range(1, ideal_hits + 1))
    return dcg / idcg if idcg > 0 else 0.0


def compute_metrics(
    retrieved_concepts: list[str],
    expected_concepts: set[str],
    retrieved_sources: list[str],
    expected_sources: set[str],
) -> dict[str, Any]:
    """Compute recall@k, precision@k, MRR, NDCG@k for concepts and sources."""
    metrics: dict[str, Any] = {}

    # Concepts
    for k in METRIC_KS:
        metrics[f"concept_recall@{k}"] = round(recall_at_k(retrieved_concepts, expected_concepts, k), 3)
        metrics[f"concept_precision@{k}"] = round(precision_at_k(retrieved_concepts, expected_concepts, k), 3)
        metrics[f"concept_ndcg@{k}"] = round(ndcg_at_k(retrieved_concepts, expected_concepts, k), 3)
    metrics["concept_mrr"] = round(mrr(retrieved_concepts, expected_concepts), 3)

    # Sources
    for k in METRIC_KS:
        metrics[f"source_recall@{k}"] = round(recall_at_k(retrieved_sources, expected_sources, k), 3)
        metrics[f"source_precision@{k}"] = round(precision_at_k(retrieved_sources, expected_sources, k), 3)
        metrics[f"source_ndcg@{k}"] = round(ndcg_at_k(retrieved_sources, expected_sources, k), 3)
    metrics["source_mrr"] = round(mrr(retrieved_sources, expected_sources), 3)

    # Legacy aggregate names for backward compatibility.
    metrics["concept_recall"] = metrics["concept_recall@5"]
    metrics["concept_precision"] = metrics["concept_precision@5"]
    metrics["source_recall"] = metrics["source_recall@5"]
    metrics["faithfulness"] = metrics["source_recall@5"]

    return metrics


# ---------------------------------------------------------------------------
# Evaluation
# ---------------------------------------------------------------------------


def evaluate_sample(
    kg: dict[str, Any],
    sample: dict[str, Any],
    top_k: int = 5,
    hops: int = 2,
    index: VectorIndex | None = None,
    provider: EmbeddingProvider | None = None,
    predicates: tuple[str, ...] | None = None,
    hybrid_retriever: HybridRetriever | None = None,
) -> dict[str, Any]:
    """Compute retrieval metrics for a single evaluation sample."""
    query = sample.get("query", "")
    expected_concepts = {_label_key(c) for c in sample.get("expected_concepts", [])}
    expected_sources = {_source_key(s) for s in sample.get("expected_sources", [])}

    # Seed entities via deterministic linking (always run).
    linked = entity_linking(kg, query, top_n=top_k)
    seed_ranked: list[dict[str, Any]] = [{"entity": e, "score": 1.0 - (i * 0.01)} for i, e in enumerate(linked)]

    # Optional hybrid dense+sparse+rerank retrieval.
    if hybrid_retriever is not None:
        try:
            hybrid_hits = hybrid_retriever.search(query, top_k=top_k)
            seen = {item["entity"]["@id"] for item in seed_ranked}
            for hit in hybrid_hits:
                eid = hit["entity"]["@id"]
                if eid not in seen:
                    seed_ranked.append(hit)
                    seen.add(eid)
            seed_ranked.sort(key=lambda x: x["score"], reverse=True)
        except Exception as exc:  # pragma: no cover
            print(f"[warn] hybrid retrieval failed: {exc}", file=sys.stderr)
    elif index is not None and provider is not None:
        try:
            vector_hits = index.search(query, provider, top_k=top_k)
            seen = {item["entity"]["@id"] for item in seed_ranked}
            for hit in vector_hits:
                eid = hit["entity"]["@id"]
                if eid not in seen:
                    seed_ranked.append(hit)
                    seen.add(eid)
            seed_ranked.sort(key=lambda x: x["score"], reverse=True)
        except Exception as exc:  # pragma: no cover
            print(f"[warn] vector retrieval failed: {exc}", file=sys.stderr)

    seed_ids = [item["entity"]["@id"] for item in seed_ranked]

    # Expand graph around all retrieved seeds.
    graph_ids = graph_retrieval(kg, seed_ids, hops=hops, predicates=predicates)
    graph_ranked = [{"entity": {"@id": gid}, "score": 0.0} for gid in graph_ids if gid not in seed_ids]
    all_ranked = seed_ranked + graph_ranked

    all_ids = {item["entity"]["@id"] for item in all_ranked}

    # Convert IDs to short human-readable labels / sources for reporting.
    by_id = {e["@id"]: e for e in iter_entities(kg)}
    retrieved_labels = _ranked_concepts(kg, all_ranked)
    expected_labels = set(expected_concepts)

    # Sources.
    retrieved_sources = _ranked_sources(kg, all_ranked)

    # Per-item debug lists.
    retrieved_entities = sorted(
        {short_id(eid) for eid in all_ids if eid in by_id}
    )
    expected_entities = sorted(expected_labels)

    metrics = compute_metrics(
        retrieved_labels,
        expected_labels,
        retrieved_sources,
        expected_sources,
    )

    return {
        "query": query,
        **metrics,
        "retrieved_entities": retrieved_entities,
        "retrieved_sources": sorted(set(retrieved_sources)),
        "expected_entities": expected_entities,
        "expected_sources": sorted(expected_sources),
        "n_retrieved": len(all_ids),
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
                "concept/03_advanced/01_async/01_async.md",
                "concept/03_advanced/01_async/08_pin_unpin.md",
            ],
        },
        {
            "query": "difference between Send and Sync traits",
            "expected_concepts": ["Send", "Sync", "trait"],
            "expected_sources": [
                "concept/03_advanced/00_concurrency/02_send_sync_auto_traits.md",
            ],
        },
        {
            "query": "what is unsafe Rust used for",
            "expected_concepts": ["unsafe", "raw pointer", "FFI"],
            "expected_sources": [
                "concept/03_advanced/02_unsafe/01_unsafe.md",
                "concept/03_advanced/04_ffi/01_rust_ffi.md",
            ],
        },
        {
            "query": "how do generics work with trait bounds",
            "expected_concepts": ["generics", "trait bound", "where clause"],
            "expected_sources": [
                "concept/02_intermediate/01_generics/01_generics.md",
                "concept/02_intermediate/00_traits/01_traits.md",
            ],
        },
        {
            "query": "what is interior mutability",
            "expected_concepts": ["interior mutability", "RefCell", "Cell"],
            "expected_sources": [
                "concept/02_intermediate/02_memory_management/02_interior_mutability.md",
            ],
        },
    ]


def run_evaluation(
    kg: dict[str, Any],
    samples: list[dict[str, Any]],
    top_k: int = 5,
    hops: int = 2,
    index: VectorIndex | None = None,
    provider: EmbeddingProvider | None = None,
    predicates: tuple[str, ...] | None = None,
    hybrid_retriever: HybridRetriever | None = None,
) -> dict[str, Any]:
    results: list[dict[str, Any]] = []
    for sample in samples:
        results.append(
            evaluate_sample(
                kg,
                sample,
                top_k=top_k,
                hops=hops,
                index=index,
                provider=provider,
                predicates=predicates,
                hybrid_retriever=hybrid_retriever,
            )
        )

    if not results:
        return {"samples": [], "aggregates": {}}

    def avg(key: str) -> float:
        return round(sum(r[key] for r in results) / len(results), 3)

    aggregates: dict[str, Any] = {
        "n_samples": len(results),
        "embedding_provider": provider.name if provider else "structural",
        "retrieval_mode": "hybrid" if hybrid_retriever else ("vector" if provider else "structural"),
        "bm25_weight": hybrid_retriever.bm25_weight if hybrid_retriever else None,
        "reranker": hybrid_retriever.reranker.__class__.__name__ if hybrid_retriever and hybrid_retriever.reranker else None,
    }
    for key in results[0]:
        if key in ("query", "retrieved_entities", "retrieved_sources", "expected_entities", "expected_sources", "n_retrieved"):
            continue
        aggregates[key] = avg(key)

    return {"samples": results, "aggregates": aggregates}


def write_report(report: dict[str, Any], output: Path) -> None:
    output.parent.mkdir(parents=True, exist_ok=True)
    with open(output, "w", encoding="utf-8") as f:
        json.dump(report, f, ensure_ascii=False, indent=2)
    print(f"[semantic_alignment_pipeline] wrote {output}")


def _format_markdown(report: dict[str, Any]) -> str:
    agg = report.get("aggregates", {})
    retrieval_mode = agg.get("retrieval_mode", "structural")
    lines = [
        "# KG-RAG Semantic Alignment Evaluation Report",
        "",
        f"**Generated**: {__import__('datetime').datetime.now().isoformat(timespec='minutes')}",
        f"**Embedding provider**: {agg.get('embedding_provider', 'structural')}",
        f"**Retrieval mode**: {retrieval_mode}",
        f"**Samples**: {agg.get('n_samples', 0)}",
    ]
    if agg.get("bm25_weight") is not None:
        lines.append(f"**BM25 weight**: {agg['bm25_weight']}")
    if agg.get("reranker"):
        lines.append(f"**Reranker**: {agg['reranker']}")
    lines.extend([
        "",
        "## Aggregates",
        "",
        "| Metric | Value |",
        "|:---|---:|",
    ])

    # Group metrics by category and k.
    metric_keys = [k for k in agg if k not in ("n_samples", "embedding_provider")]
    concept_metrics = sorted([k for k in metric_keys if k.startswith("concept_")])
    source_metrics = sorted([k for k in metric_keys if k.startswith("source_")])

    for key in concept_metrics + source_metrics:
        lines.append(f"| {key} | {agg[key]} |")

    lines.extend([
        "",
        "## Per-Sample Results",
        "",
    ])
    for sample in report.get("samples", []):
        lines.append(f"### {sample['query']}")
        lines.append("")
        lines.append(f"- n_retrieved: {sample['n_retrieved']}")
        for key in concept_metrics + source_metrics:
            lines.append(f"- {key}: {sample[key]}")
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
    parser.add_argument("--top-k", type=int, default=5, help="Top-K entities from linking/vector retrieval")
    parser.add_argument("--hops", type=int, default=2, help="Graph expansion hops")
    parser.add_argument("--predicates", default=",".join(DEFAULT_PREDICATES), help="Comma-separated predicates for graph expansion")
    parser.add_argument("--builtin", action="store_true", help="Use built-in tiny eval set")
    # Embedding provider options.
    parser.add_argument(
        "--embed-provider",
        choices=["sentence-transformers", "openai", "none"],
        help="Embedding provider. Defaults to sentence-transformers if deps available; 'none' disables vector retrieval.",
    )
    parser.add_argument("--embed-model", help="Model name for the embedding provider")
    parser.add_argument("--embed-api-key", help="API key for OpenAI-compatible provider (or set OPENAI_API_KEY)")
    parser.add_argument("--embed-base-url", help="Base URL for OpenAI-compatible provider (or set OPENAI_BASE_URL)")
    # Hybrid + reranker options.
    parser.add_argument("--hybrid", action="store_true", help="Enable BM25 + vector hybrid retrieval (requires rank-bm25)")
    parser.add_argument("--bm25-weight", type=float, default=0.3, help="Weight of BM25 score in hybrid fusion (0=vector only, 1=BM25 only)")
    parser.add_argument("--reranker", help="Cross-encoder model name for reranking (requires sentence-transformers)")
    parser.add_argument("--reranker-top-k", type=int, default=20, help="Number of hybrid candidates to feed to reranker")
    parser.add_argument("--sample", type=int, default=0, help="If >0, randomly sample N queries for quick evaluation")
    args = parser.parse_args(argv)

    kg = load_kg(args.kg)
    samples = default_eval_set() if args.builtin else load_eval(args.eval)
    if not samples:
        print(f"[warn] no eval samples found in {args.eval}; use --builtin", file=sys.stderr)

    if args.sample and args.sample < len(samples):
        import random
        random.seed(20260804)
        samples = random.sample(samples, args.sample)

    predicate_set = tuple(p.strip() for p in args.predicates.split(",") if p.strip())

    provider: EmbeddingProvider | None = None
    index: VectorIndex | None = None
    hybrid_retriever: HybridRetriever | None = None
    if args.embed_provider != "none":
        try:
            provider = create_embedding_provider(
                provider=args.embed_provider,
                model=args.embed_model,
                api_key=args.embed_api_key,
                base_url=args.embed_base_url,
            )
            if provider is not None:
                index = VectorIndex.build(kg, provider)
        except Exception as exc:  # pragma: no cover
            print(f"[warn] embedding provider unavailable: {exc}", file=sys.stderr)

    if index is not None and args.hybrid:
        bm25_index: BM25Index | None = None
        try:
            bm25_index = BM25Index.build(kg)
            print(f"[semantic_alignment_pipeline] built BM25 index over {len(bm25_index.entities)} entities", file=sys.stderr)
        except Exception as exc:  # pragma: no cover
            print(f"[warn] BM25 index unavailable: {exc}", file=sys.stderr)

        reranker: Any | None = None
        if args.reranker:
            try:
                from sentence_transformers.cross_encoder import CrossEncoder
                reranker = CrossEncoder(args.reranker)
                print(f"[semantic_alignment_pipeline] loaded reranker {args.reranker}", file=sys.stderr)
            except Exception as exc:  # pragma: no cover
                print(f"[warn] reranker unavailable: {exc}", file=sys.stderr)

        hybrid_retriever = HybridRetriever(
            vector_index=index,
            bm25_index=bm25_index,
            provider=provider,
            bm25_weight=args.bm25_weight,
            reranker=reranker,
            reranker_top_k=args.reranker_top_k,
        )

    report = run_evaluation(
        kg,
        samples,
        top_k=args.top_k,
        hops=args.hops,
        index=index,
        provider=provider,
        predicates=predicate_set,
        hybrid_retriever=hybrid_retriever,
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
