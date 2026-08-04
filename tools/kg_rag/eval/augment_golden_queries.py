#!/usr/bin/env python3
"""Augment golden_queries_v1.json with domain-focused curated queries.

Adds >=200 new queries across 10 Rust semantic domains, aligns existing curated
expected_concepts with the KG entity label keys used by the evaluator, and
updates metadata.
"""
from __future__ import annotations

import argparse
import json
import random
import re
from collections import Counter
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = ROOT.parents[1]
KG_PATH = REPO_ROOT / "concept" / "00_meta" / "kg_data_v3.json"
DEFAULT_EVAL = ROOT / "eval" / "golden_queries_v1.json"


def short_id(uri: str) -> str:
    return uri.removeprefix("ex:")


def get_lang(values: list[dict[str, str]], lang: str) -> str | None:
    for v in values:
        if v.get("@language") == lang:
            return v.get("@value")
    return None


def evaluator_key(text: str) -> str:
    """Normalize a concept label the same way the evaluator does."""
    return text.lower().strip(" \\t.,;:!?\"'").replace(" ", "_")


def layer_from_entity(entity: dict[str, Any]) -> str:
    layer = entity.get("ex:layer") or "L0"
    bloom = entity.get("ex:bloomLevel") or "L0"
    return str(layer).split("-")[0] or str(bloom).split("-")[0] or "L0"


def path_to_source(path: str) -> str:
    if path.startswith("concept/"):
        return path
    return f"concept/{path}"


def difficulty_from_layer(layer: str) -> str:
    lvl = layer.lstrip("L")
    try:
        n = int(lvl[0]) if lvl else 0
    except Exception:
        n = 0
    if n <= 1:
        return "basic"
    if n <= 3:
        return "intermediate"
    return "advanced"


# Domain -> path/domain matching rules.
DOMAIN_RULES: dict[str, list[str]] = {
    "ownership_borrow_lifetime": [
        "01_foundation/01_ownership_borrow_lifetime",
        "04_formal/01_ownership_logic",
        "04_formal/02_separation_logic",
    ],
    "trait_generic_type": [
        "01_foundation/02_type_system",
        "02_intermediate/00_traits",
        "02_intermediate/01_generics",
        "02_intermediate/04_types_and_conversions",
        "04_formal/00_type_theory",
        "04_formal/05_rustc_internals",
    ],
    "unsafe_ffi_memory": [
        "03_advanced/02_unsafe",
        "03_advanced/04_ffi",
        "03_advanced/06_low_level_patterns",
        "03_advanced/07_unsafe_internals",
        "04_formal/01_ownership_logic/06_behavior_considered_undefined",
        "04_formal/03_operational_semantics",
    ],
    "concurrency_async_parallel": [
        "03_advanced/00_concurrency",
        "03_advanced/01_async",
        "04_formal/07_concurrency_semantics",
        "04_formal/12_concurrency_models",
    ],
    "no_std_embedded_bare_metal": [
        "06_ecosystem/05_systems_and_embedded",
        "04_formal/14_embedded_semantics",
    ],
    "error_handling_idioms": [
        "01_foundation/08_error_handling",
        "02_intermediate/03_error_handling",
        "05_comparative/05_idioms_patterns_architecture/01_idioms",
        "06_ecosystem/03_design_patterns/50_rust_idioms_atlas",
    ],
    "macros_metaprogramming": [
        "01_foundation/09_macros_basics",
        "02_intermediate/06_macros_and_metaprogramming",
        "03_advanced/03_proc_macros",
    ],
    "design_patterns_architecture": [
        "05_comparative/05_idioms_patterns_architecture",
        "06_ecosystem/03_design_patterns",
        "04_formal/10_architecture_semantics",
        "04_formal/00_type_theory/11_formal_design_pattern_theory",
    ],
    "formal_methods_verification": [
        "04_formal",
    ],
    "toolchain_cargo_versions": [
        "06_ecosystem/01_cargo",
        "07_future/00_version_tracking",
    ],
}

SINGLE_TEMPLATES: list[tuple[str, str]] = [
    ("practical guide to {label}", "application"),
    ("common {label} patterns in rust", "application"),
    ("when should I use {label} in rust", "application"),
    ("{label} pitfalls and how to avoid them", "analysis"),
    ("step by step {label} example", "application"),
    ("advanced {label} techniques", "analysis"),
    ("{label} in production codebases", "application"),
    ("how to test {label} in rust", "application"),
    ("best practices for {label}", "application"),
    ("explain {label} with examples", "recall"),
]

COMPARISON_TEMPLATES: list[tuple[str, str]] = [
    ("difference between {a} and {b} in rust", "analysis"),
    ("when to choose {a} over {b}", "analysis"),
    ("{a} vs {b}: trade-offs", "analysis"),
]

CROSS_TEMPLATES: list[tuple[str, str]] = [
    ("how does {label} interact with {related}", "analysis"),
    ("using {label} together with {related}", "application"),
    ("{label} and {related} common patterns", "application"),
]


def entity_label_key(entity: dict[str, Any]) -> str:
    label = get_lang(entity.get("skos:prefLabel", []), "en") or short_id(entity.get("@id", ""))
    return evaluator_key(label)


def build_indexes(kg: dict[str, Any]) -> tuple[dict[str, Any], dict[str, dict[str, Any]], dict[str, list[dict[str, Any]]]]:
    entities = kg.get("entities", [])
    by_id = {e["@id"]: e for e in entities}
    by_path: dict[str, dict[str, Any]] = {}
    for e in entities:
        path = e.get("ex:path") or e.get("path")
        if path:
            by_path[path] = e
            by_path[path_to_source(path)] = e
    related: dict[str, list[dict[str, Any]]] = {eid: [] for eid in by_id}
    for rel in kg.get("relations", []):
        sub = rel.get("ex:subject")
        obj = rel.get("ex:object")
        if sub in related and obj in by_id:
            related[sub].append(by_id[obj])
    return by_id, by_path, related


def matches_domain(entity: dict[str, Any], domain: str) -> bool:
    path = entity.get("ex:path") or entity.get("path") or ""
    entity_domain = entity.get("ex:domain") or ""
    rules = DOMAIN_RULES.get(domain, [])
    for rule in rules:
        if rule in path or rule in entity_domain:
            return True
    return False


def candidate_entities(kg: dict[str, Any], domain: str, by_path: dict[str, Any]) -> list[dict[str, Any]]:
    """Return non-quiz, non-README entities matching the domain, sorted by label."""
    out = []
    for e in kg.get("entities", []):
        if not matches_domain(e, domain):
            continue
        path = e.get("ex:path") or ""
        # Skip quizzes and README/index pages as primary targets.
        if "quiz" in path.lower() or path.endswith("README.md") or path.endswith("INDEX.md"):
            continue
        label = get_lang(e.get("skos:prefLabel", []), "en")
        if not label or not path:
            continue
        out.append(e)
    # Deterministic shuffle by label hash.
    out.sort(key=lambda e: (entity_label_key(e), e["@id"]))
    return out


def make_single_query(entity: dict[str, Any], template: str, reasoning: str) -> dict[str, Any]:
    label = get_lang(entity.get("skos:prefLabel", []), "en")
    path = entity.get("ex:path")
    layer = layer_from_entity(entity)
    return {
        "query": template.format(label=label),
        "expected_concepts": [entity_label_key(entity)],
        "expected_sources": [path_to_source(path)],
        "layer": layer,
        "domain": entity.get("ex:domain", "uncategorized"),
        "origin": "augmented",
        "difficulty": difficulty_from_layer(layer),
        "reasoning_type": reasoning,
    }


def make_comparison_query(a: dict[str, Any], b: dict[str, Any], template: str) -> dict[str, Any]:
    label_a = get_lang(a.get("skos:prefLabel", []), "en")
    label_b = get_lang(b.get("skos:prefLabel", []), "en")
    layer = max(layer_from_entity(a), layer_from_entity(b))
    domain_a = a.get("ex:domain", "uncategorized")
    domain_b = b.get("ex:domain", "uncategorized")
    domain = domain_a if domain_a == domain_b else "cross_domain"
    return {
        "query": template.format(a=label_a, b=label_b),
        "expected_concepts": [entity_label_key(a), entity_label_key(b)],
        "expected_sources": [path_to_source(a.get("ex:path")), path_to_source(b.get("ex:path"))],
        "layer": layer,
        "domain": domain,
        "origin": "augmented",
        "difficulty": difficulty_from_layer(layer),
        "reasoning_type": "analysis",
    }


def make_cross_query(entity: dict[str, Any], related: dict[str, Any], template: str) -> dict[str, Any]:
    label = get_lang(entity.get("skos:prefLabel", []), "en")
    rel_label = get_lang(related.get("skos:prefLabel", []), "en")
    layer = max(layer_from_entity(entity), layer_from_entity(related))
    return {
        "query": template.format(label=label, related=rel_label),
        "expected_concepts": [entity_label_key(entity), entity_label_key(related)],
        "expected_sources": [path_to_source(entity.get("ex:path")), path_to_source(related.get("ex:path"))],
        "layer": layer,
        "domain": entity.get("ex:domain", "uncategorized"),
        "origin": "augmented",
        "difficulty": difficulty_from_layer(layer),
        "reasoning_type": "analysis",
    }


def align_curated_concepts(sample: dict[str, Any], by_path: dict[str, Any], by_id: dict[str, Any]) -> dict[str, Any]:
    """Replace hand-written concept keys with normalized KG label keys when possible."""
    new_concepts: list[str] = []
    seen: set[str] = set()
    # First, derive keys from expected sources.
    for src in sample.get("expected_sources", []):
        # Strip leading concept/ for lookup.
        lookup = src.removeprefix("concept/")
        e = by_path.get(src) or by_path.get(lookup)
        if e:
            key = entity_label_key(e)
            if key and key not in seen:
                seen.add(key)
                new_concepts.append(key)
    # Then keep any existing expected concepts that exactly match a KG entity key.
    for c in sample.get("expected_concepts", []):
        if c in seen:
            continue
        # Does any entity have this exact normalized label key?
        for e in by_id.values():
            if entity_label_key(e) == c:
                seen.add(c)
                new_concepts.append(c)
                break
    if new_concepts:
        sample = dict(sample)
        sample["expected_concepts"] = new_concepts
    return sample


def generate_domain_queries(kg: dict[str, Any], by_path: dict[str, Any], related_map: dict[str, list[dict[str, Any]]], rng: random.Random) -> list[dict[str, Any]]:
    queries: list[dict[str, Any]] = []
    for domain, _ in DOMAIN_RULES.items():
        candidates = candidate_entities(kg, domain, by_path)
        if not candidates:
            continue
        # Pick up to 20 candidates deterministically; if fewer, cycle templates.
        chosen = candidates[:20]
        # Single-concept queries: 1 per chosen entity, cycling templates.
        for i, e in enumerate(chosen):
            tmpl, reasoning = SINGLE_TEMPLATES[i % len(SINGLE_TEMPLATES)]
            queries.append(make_single_query(e, tmpl, reasoning))

        # Add a few comparison queries within the domain.
        if len(chosen) >= 2:
            pairs = [(chosen[i], chosen[i + 1]) for i in range(0, min(6, len(chosen) - 1), 2)]
            for (a, b), (tmpl, _) in zip(pairs, COMPARISON_TEMPLATES):
                queries.append(make_comparison_query(a, b, tmpl))

        # Add a few cross-concept queries using KG relations.
        cross_count = 0
        for e in chosen:
            rels = [r for r in related_map.get(e["@id"], []) if r["@id"] != e["@id"]]
            if not rels:
                continue
            rel = rels[0]
            tmpl, _ = CROSS_TEMPLATES[cross_count % len(CROSS_TEMPLATES)]
            queries.append(make_cross_query(e, rel, tmpl))
            cross_count += 1
            if cross_count >= 3:
                break

    # Hand-written cross-domain queries for each target area.
    handcrafted = [
        {
            "query": "how does ownership transfer affect thread safety in rust",
            "expected_concepts": ["ownership", "send_and_sync_auto_traits_as_compile-time_concurrency_contracts"],
            "expected_sources": [
                "concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md",
                "concept/03_advanced/00_concurrency/02_send_sync_auto_traits.md",
            ],
            "layer": "L3",
            "domain": "cross_domain",
            "origin": "augmented",
            "difficulty": "advanced",
            "reasoning_type": "analysis",
        },
        {
            "query": "why do async futures need stable pinning",
            "expected_concepts": ["async_programming", "pin_and_unpin"],
            "expected_sources": [
                "concept/03_advanced/01_async/01_async.md",
                "concept/03_advanced/01_async/08_pin_unpin.md",
            ],
            "layer": "L4",
            "domain": "cross_domain",
            "origin": "augmented",
            "difficulty": "advanced",
            "reasoning_type": "analysis",
        },
        {
            "query": "how do trait bounds enable generic collections",
            "expected_concepts": ["traits", "generics"],
            "expected_sources": [
                "concept/02_intermediate/00_traits/01_traits.md",
                "concept/02_intermediate/01_generics/01_generics.md",
            ],
            "layer": "L2",
            "domain": "cross_domain",
            "origin": "augmented",
            "difficulty": "intermediate",
            "reasoning_type": "application",
        },
        {
            "query": "safe abstraction over unsafe ffi calls",
            "expected_concepts": ["safe_and_effective_unsafe_rust", "rust_ffi"],
            "expected_sources": [
                "concept/03_advanced/02_unsafe/01_unsafe.md",
                "concept/03_advanced/04_ffi/01_rust_ffi.md",
            ],
            "layer": "L4",
            "domain": "cross_domain",
            "origin": "augmented",
            "difficulty": "advanced",
            "reasoning_type": "application",
        },
        {
            "query": "error handling with result and option idioms",
            "expected_concepts": ["error_handling_basics", "rust_error_handling_idioms"],
            "expected_sources": [
                "concept/01_foundation/08_error_handling/01_error_handling_basics.md",
                "concept/02_intermediate/03_error_handling/05_error_idioms.md",
            ],
            "layer": "L2",
            "domain": "cross_domain",
            "origin": "augmented",
            "difficulty": "intermediate",
            "reasoning_type": "application",
        },
        {
            "query": "procedural macros for custom derive attributes",
            "expected_concepts": ["procedural_macros", "macro_hygiene"],
            "expected_sources": [
                "concept/03_advanced/03_proc_macros/02_proc_macro.md",
                "concept/03_advanced/03_proc_macros/09_macro_hygiene.md",
            ],
            "layer": "L4",
            "domain": "cross_domain",
            "origin": "augmented",
            "difficulty": "advanced",
            "reasoning_type": "application",
        },
        {
            "query": "designing embedded rust without standard library",
            "expected_concepts": ["no_std_and_bare-metal_rust", "embedded_systems"],
            "expected_sources": [
                "concept/06_ecosystem/05_systems_and_embedded/38_no_std_bare_metal_rust.md",
                "concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md",
            ],
            "layer": "L3",
            "domain": "cross_domain",
            "origin": "augmented",
            "difficulty": "advanced",
            "reasoning_type": "application",
        },
        {
            "query": "cargo workspace dependency resolution",
            "expected_concepts": ["cargo_dependency_resolution", "cargo_workspaces"],
            "expected_sources": [
                "concept/06_ecosystem/01_cargo/06_cargo_dependency_resolution.md",
                "concept/06_ecosystem/01_cargo/14_cargo_workspaces.md",
            ],
            "layer": "L2",
            "domain": "cross_domain",
            "origin": "augmented",
            "difficulty": "intermediate",
            "reasoning_type": "application",
        },
        {
            "query": "formal verification with kani and miri",
            "expected_concepts": ["kani:_rust_bounded_model_checker", "miri:_rust_undefined_behavior_detector"],
            "expected_sources": [
                "concept/04_formal/04_model_checking/09_kani.md",
                "concept/04_formal/04_model_checking/08_miri.md",
            ],
            "layer": "L4",
            "domain": "cross_domain",
            "origin": "augmented",
            "difficulty": "advanced",
            "reasoning_type": "analysis",
        },
        {
            "query": "version tracking for rust 1.97 stable features",
            "expected_concepts": ["rust_1.97.0_stabilized_features", "rust_version_tracking"],
            "expected_sources": [
                "concept/07_future/00_version_tracking/rust_1_97_stabilized.md",
                "concept/07_future/00_version_tracking/01_rust_version_tracking.md",
            ],
            "layer": "L2",
            "domain": "cross_domain",
            "origin": "augmented",
            "difficulty": "intermediate",
            "reasoning_type": "recall",
        },
        # Ownership / borrow / lifetime
        {
            "query": "explain rust move semantics and the copy trait",
            "expected_concepts": ["move_semantics"],
            "expected_sources": ["concept/01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md"],
            "layer": "L1",
            "domain": "ownership_memory",
            "origin": "augmented",
            "difficulty": "basic",
            "reasoning_type": "recall",
        },
        {
            "query": "lifetime elision rules in function signatures",
            "expected_concepts": ["lifetimes", "lifetimes_advanced"],
            "expected_sources": [
                "concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md",
                "concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md",
            ],
            "layer": "L2",
            "domain": "ownership_memory",
            "origin": "augmented",
            "difficulty": "intermediate",
            "reasoning_type": "recall",
        },
        {
            "query": "mutable versus immutable borrows in rust",
            "expected_concepts": ["borrowing"],
            "expected_sources": ["concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md"],
            "layer": "L1",
            "domain": "ownership_memory",
            "origin": "augmented",
            "difficulty": "basic",
            "reasoning_type": "recall",
        },
        {
            "query": "how rust prevents use after move",
            "expected_concepts": ["ownership", "move_semantics"],
            "expected_sources": [
                "concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md",
                "concept/01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md",
            ],
            "layer": "L1",
            "domain": "ownership_memory",
            "origin": "augmented",
            "difficulty": "basic",
            "reasoning_type": "analysis",
        },
        {
            "query": "understanding higher ranked trait bounds and lifetimes",
            "expected_concepts": ["lifetimes_advanced"],
            "expected_sources": ["concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md"],
            "layer": "L4",
            "domain": "ownership_memory",
            "origin": "augmented",
            "difficulty": "advanced",
            "reasoning_type": "analysis",
        },
        # Error handling / idioms
        {
            "query": "rust result and option combinators",
            "expected_concepts": ["error_handling_basics"],
            "expected_sources": ["concept/01_foundation/08_error_handling/01_error_handling_basics.md"],
            "layer": "L1",
            "domain": "language_core",
            "origin": "augmented",
            "difficulty": "basic",
            "reasoning_type": "application",
        },
        {
            "query": "when to use panic versus result in rust",
            "expected_concepts": ["panic_and_abort", "error_handling_basics"],
            "expected_sources": [
                "concept/01_foundation/08_error_handling/03_panic_and_abort.md",
                "concept/01_foundation/08_error_handling/01_error_handling_basics.md",
            ],
            "layer": "L2",
            "domain": "language_core",
            "origin": "augmented",
            "difficulty": "intermediate",
            "reasoning_type": "analysis",
        },
        {
            "query": "idiomatic error handling libraries in rust",
            "expected_concepts": ["rust_error_handling_idioms"],
            "expected_sources": ["concept/02_intermediate/03_error_handling/05_error_idioms.md"],
            "layer": "L3",
            "domain": "language_core",
            "origin": "augmented",
            "difficulty": "intermediate",
            "reasoning_type": "application",
        },
        {
            "query": "propagating errors with the question mark operator",
            "expected_concepts": ["error_handling_control_flow"],
            "expected_sources": ["concept/01_foundation/08_error_handling/02_error_handling_control_flow.md"],
            "layer": "L2",
            "domain": "language_core",
            "origin": "augmented",
            "difficulty": "basic",
            "reasoning_type": "application",
        },
        {
            "query": "defining custom error types in rust",
            "expected_concepts": ["error_handling_intermediate"],
            "expected_sources": ["concept/02_intermediate/03_error_handling/01_error_handling.md"],
            "layer": "L3",
            "domain": "language_core",
            "origin": "augmented",
            "difficulty": "intermediate",
            "reasoning_type": "application",
        },
    ]
    queries.extend(handcrafted)
    return queries


def deduplicate(queries: list[dict[str, Any]]) -> list[dict[str, Any]]:
    seen: set[str] = set()
    out: list[dict[str, Any]] = []
    for q in queries:
        key = q["query"].strip().lower()
        if key in seen:
            continue
        seen.add(key)
        out.append(q)
    return out


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Augment golden_queries_v1.json")
    parser.add_argument("--eval", type=Path, default=DEFAULT_EVAL, help="Path to golden_queries_v1.json")
    parser.add_argument("--kg", type=Path, default=KG_PATH, help="Path to kg_data_v3.json")
    parser.add_argument("--seed", type=int, default=20260804, help="Random seed")
    parser.add_argument("--output", type=Path, default=None, help="Output path (defaults to --eval)")
    args = parser.parse_args(argv)

    rng = random.Random(args.seed)
    kg = json.loads(args.kg.read_text(encoding="utf-8"))
    by_id, by_path, related_map = build_indexes(kg)

    eval_data = json.loads(args.eval.read_text(encoding="utf-8"))
    existing = list(eval_data.get("samples", []))

    # Align existing curated queries to KG label keys.
    aligned_existing = [align_curated_concepts(s, by_path, by_id) for s in existing]

    new_queries = generate_domain_queries(kg, by_path, related_map, rng)
    combined = deduplicate(aligned_existing + new_queries)

    new_count = len(combined) - len(aligned_existing)
    domain_counts = Counter(q.get("domain", "uncategorized") for q in new_queries)

    output = {
        "metadata": {
            "generated": "2026-08-04",
            "count": len(combined),
            "augmented_count": new_count,
            "kg_version": kg.get("metadata", {}).get("version", "unknown"),
            "kg_entity_count": len(kg.get("entities", [])),
            "seed": args.seed,
            "generator": "tools/kg_rag/eval/generate_golden_queries.py + tools/kg_rag/eval/augment_golden_queries.py",
        },
        "samples": combined,
    }

    out_path = args.output or args.eval
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(output, ensure_ascii=False, indent=2), encoding="utf-8")

    print(f"[augment_golden_queries] existing={len(aligned_existing)} new={new_count} total={len(combined)}")
    print(f"[augment_golden_queries] new domain distribution:")
    for domain, cnt in sorted(domain_counts.items()):
        print(f"  {domain}: {cnt}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
