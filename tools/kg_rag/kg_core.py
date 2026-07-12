"""Stdlib-only data access layer for the v3 knowledge graph.

Shared by ``kg_rag.py`` (vector retrieval) and ``smoke_test.py`` (structural
checks) so that lightweight validation does not require numpy /
sentence-transformers.

Single source of truth: ``concept/00_meta/kg_data_v3.json``.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent
REPO_ROOT = ROOT.parents[1]
KG_PATH = REPO_ROOT / "concept" / "00_meta" / "kg_data_v3.json"


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
            atype = item.get("@type", "unknown")
            if isinstance(atype, list):
                atype = atype[0] if atype else "unknown"
            item.setdefault("_category", atype.removeprefix("ex:").lower() + "s")
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
    ``skos:definition``. Falls back to the first available language when no
    English value exists (a few v3 entities are zh-only).
    """
    for key in ("skos:definition", "skos:scopeNote"):
        values = entity.get(key, [])
        en = get_lang_value(values, "en")
        if en:
            return en
        if values:
            return values[0].get("@value")
    return None


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


def kg_adjacency(
    entities: list[dict[str, Any]], kg: dict[str, Any]
) -> dict[str, dict[str, list[str]]]:
    """Build adjacency per entity: {id: {predicate: [object_id]}}."""
    adj: dict[str, dict[str, list[str]]] = {e["@id"]: {} for e in entities}
    for rel in kg.get("relations", []):
        subj = rel.get("ex:subject", "")
        pred = rel.get("ex:predicate", "")
        obj = rel.get("ex:object", "")
        if subj and pred and obj:
            adj.setdefault(subj, {}).setdefault(pred, []).append(obj)
    return adj


def typed_edges(kg: dict[str, Any], predicate: str) -> list[tuple[str, str]]:
    """Return all (subject, object) pairs for a fully-qualified predicate."""
    return [
        (rel["ex:subject"], rel["ex:object"])
        for rel in kg.get("relations", [])
        if rel.get("ex:predicate") == predicate
        and rel.get("ex:subject")
        and rel.get("ex:object")
    ]


def kg_paths(
    adj: dict[str, dict[str, list[str]]], entity_id: str, max_depth: int = 2
) -> list[str]:
    """Return short KG paths rooted at ``entity_id`` with readable IDs."""
    paths: list[str] = []
    seen: set[str] = set()

    def walk(current: str, depth: int, trail: list[str]) -> None:
        if depth > max_depth:
            return
        for pred, objects in adj.get(current, {}).items():
            for obj in objects:
                path_str = " -> ".join(trail + [short_id(pred), short_id(obj)])
                if path_str not in seen:
                    seen.add(path_str)
                    paths.append(path_str)
                if depth + 1 <= max_depth:
                    walk(obj, depth + 1, trail + [short_id(pred), short_id(obj)])

    walk(entity_id, 1, [short_id(entity_id)])
    return paths[:10]
