#!/usr/bin/env python3
"""Generate a golden query set for KG-RAG evaluation.

The generator uses three sources:

1. **KG entities** — each concept/theory/model/primitive becomes 1–3 natural-language
   query variants with the entity label as the expected concept and its
   ``ex:path`` as the expected source.
2. **Curated cross-domain / error-code / version / no_std / formal-method queries**
   — hand-written to stress semantic retrieval across the L0–L7 spectrum.
3. **Synthetic paraphrases** — simple rule-based rewrites ("What is X?",
   "Explain X", "How does X work?") to increase diversity without adding
   external LLM dependencies.

Output: ``tools/kg_rag/eval/golden_queries_v1.json``

Example:

    python tools/kg_rag/eval/generate_golden_queries.py
    python tools/kg_rag/eval/generate_golden_queries.py --output /tmp/gq.json --seed 42
"""
from __future__ import annotations

import argparse
import json
import random
import re
import sys
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
REPO_ROOT = ROOT.parents[1]
KG_PATH = REPO_ROOT / "concept" / "00_meta" / "kg_data_v3.json"
DEFAULT_OUTPUT = ROOT / "eval" / "golden_queries_v1.json"


def short_id(uri: str) -> str:
    return uri.removeprefix("ex:")


def get_lang(values: list[dict[str, str]], lang: str) -> str | None:
    for v in values:
        if v.get("@language") == lang:
            return v.get("@value")
    return None


def entity_text(entity: dict[str, Any]) -> str:
    parts: list[str] = []
    label = get_lang(entity.get("skos:prefLabel", []), "en")
    if label:
        parts.append(label)
    for key in ("skos:scopeNote", "skos:definition"):
        values = entity.get(key, [])
        en = get_lang(values, "en")
        if en:
            parts.append(en)
            break
    return " ".join(parts)


def normalize_for_key(text: str) -> str:
    text = text.lower()
    text = re.sub(r"[^a-z0-9_\s-]", "", text)
    text = re.sub(r"\s+", "_", text).strip("_")
    return text[:80]


def layer_from_entity(entity: dict[str, Any]) -> str:
    layer = entity.get("ex:layer") or "L0"
    bloom = entity.get("ex:bloomLevel") or "L0"
    return str(layer).split("-")[0] or str(bloom).split("-")[0] or "L0"


def path_to_source(path: str) -> str:
    if path.startswith("concept/"):
        return path
    return f"concept/{path}"


QUERY_TEMPLATES = [
    "what is {label}",
    "explain {label} in rust",
    "how does {label} work",
    "{label} overview",
    "rust {label} tutorial",
]


def kg_derived_queries(kg: dict[str, Any], rng: random.Random) -> list[dict[str, Any]]:
    """Generate query variants from KG entities."""
    queries: list[dict[str, Any]] = []
    entities = kg.get("entities", [])
    if not isinstance(entities, list):
        return []

    for entity in entities:
        eid = entity.get("@id", "")
        label = get_lang(entity.get("skos:prefLabel", []), "en")
        path = entity.get("ex:path")
        if not label or not path:
            continue
        source = path_to_source(path)
        key_label = normalize_for_key(label)
        concept_key = normalize_for_key(short_id(eid))

        # Pick 1–3 templates deterministically based on entity id hash.
        seed = hash(eid) % 10000
        rng2 = random.Random(seed)
        chosen = rng2.sample(QUERY_TEMPLATES, k=min(3, len(QUERY_TEMPLATES)))
        for tmpl in chosen:
            query_text = tmpl.format(label=label)
            queries.append({
                "query": query_text,
                "expected_concepts": [key_label],
                "expected_sources": [source],
                "layer": layer_from_entity(entity),
                "domain": entity.get("ex:domain", "uncategorized"),
                "origin": "kg_template",
            })
    return queries


CURATED_QUERIES: list[dict[str, Any]] = [
    # Cross-domain: ownership + concurrency
    {
        "query": "how does ownership prevent data races in rust",
        "expected_concepts": ["ownership", "borrowing", "data_race"],
        "expected_sources": [
            "concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md",
            "concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md",
            "concept/03_advanced/00_concurrency/05_data_race.md",
        ],
        "layer": "L1",
        "domain": "cross_domain",
        "origin": "curated",
    },
    {
        "query": "difference between Send and Sync traits",
        "expected_concepts": ["send", "sync", "trait"],
        "expected_sources": [
            "concept/03_advanced/00_concurrency/02_send_sync_auto_traits.md",
            "concept/03_advanced/00_concurrency/04_send_sync_boundaries.md",
        ],
        "layer": "L2",
        "domain": "cross_domain",
        "origin": "curated",
    },
    {
        "query": "why does async fn need Pin",
        "expected_concepts": ["async_fn", "future", "pin", "self_referential"],
        "expected_sources": [
            "concept/03_advanced/01_async/01_async.md",
            "concept/03_advanced/01_async/08_pin_unpin.md",
        ],
        "layer": "L3",
        "domain": "cross_domain",
        "origin": "curated",
    },
    {
        "query": "interior mutability with Cell RefCell Mutex RwLock",
        "expected_concepts": ["interior_mutability", "cell", "refcell", "mutex", "rwlock"],
        "expected_sources": [
            "concept/02_intermediate/02_memory_management/02_interior_mutability.md",
            "concept/03_advanced/00_concurrency/03_mutex_and_rwlock.md",
        ],
        "layer": "L2",
        "domain": "cross_domain",
        "origin": "curated",
    },
    {
        "query": "unsafe rust patterns for FFI and raw pointers",
        "expected_concepts": ["unsafe", "raw_pointer", "ffi"],
        "expected_sources": [
            "concept/03_advanced/02_unsafe/01_unsafe.md",
            "concept/03_advanced/04_ffi/01_rust_ffi.md",
            "concept/03_advanced/02_unsafe/04_raw_pointers.md",
        ],
        "layer": "L3",
        "domain": "cross_domain",
        "origin": "curated",
    },
    {
        "query": "Pin projection and self-referential structs safety",
        "expected_concepts": ["pin", "pin_projection", "self_referential"],
        "expected_sources": [
            "concept/03_advanced/01_async/08_pin_unpin.md",
            "concept/03_advanced/01_async/09_pin_projection_counterexamples.md",
        ],
        "layer": "L3",
        "domain": "cross_domain",
        "origin": "curated",
    },
    {
        "query": "lifetime elision rules and anonymous lifetimes",
        "expected_concepts": ["lifetimes", "lifetime_elision", "anonymous_lifetime"],
        "expected_sources": [
            "concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md",
            "concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md",
        ],
        "layer": "L2",
        "domain": "cross_domain",
        "origin": "curated",
    },
    {
        "query": "drop order and destructor semantics in rust",
        "expected_concepts": ["drop", "destructor", "ownership"],
        "expected_sources": [
            "concept/04_formal/05_rustc_internals/09_destructors.md",
            "concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md",
        ],
        "layer": "L4",
        "domain": "cross_domain",
        "origin": "curated",
    },
    # Error codes
    {
        "query": "rustc error E0502 cannot borrow mutably after immutable borrow",
        "expected_concepts": ["e0502", "borrow_checker", "mutable_borrow"],
        "expected_sources": [
            "concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md",
            "concept/00_meta/knowledge_topology/decision_tree_error_code_index.json",
        ],
        "layer": "L1",
        "domain": "error_code",
        "origin": "curated",
    },
    {
        "query": "rustc error E0499 cannot borrow mutably more than once",
        "expected_concepts": ["e0499", "mutable_borrow"],
        "expected_sources": [
            "concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md",
        ],
        "layer": "L1",
        "domain": "error_code",
        "origin": "curated",
    },
    {
        "query": "rustc error E0596 cannot borrow data as mutable",
        "expected_concepts": ["e0596", "interior_mutability"],
        "expected_sources": [
            "concept/02_intermediate/02_memory_management/02_interior_mutability.md",
        ],
        "layer": "L2",
        "domain": "error_code",
        "origin": "curated",
    },
    {
        "query": "rustc error E0382 use of moved value",
        "expected_concepts": ["e0382", "move_semantics"],
        "expected_sources": [
            "concept/01_foundation/01_ownership_borrow_lifetime/05_move_semantics.md",
        ],
        "layer": "L1",
        "domain": "error_code",
        "origin": "curated",
    },
    {
        "query": "rustc error E0308 mismatched types",
        "expected_concepts": ["e0308", "type_checking"],
        "expected_sources": [
            "concept/01_foundation/02_type_system/01_type_system.md",
            "concept/02_intermediate/04_types_and_conversions/04_type_system_advanced.md",
        ],
        "layer": "L1",
        "domain": "error_code",
        "origin": "curated",
    },
    {
        "query": "rustc error E0277 trait bound not satisfied",
        "expected_concepts": ["e0277", "trait_bound"],
        "expected_sources": [
            "concept/02_intermediate/00_traits/01_traits.md",
            "concept/02_intermediate/01_generics/01_generics.md",
        ],
        "layer": "L2",
        "domain": "error_code",
        "origin": "curated",
    },
    # Version features
    {
        "query": "rust 1.98 stabilized features summary",
        "expected_concepts": ["rust_1_98_0_stabilized_features", "rust_version_tracking"],
        "expected_sources": [
            "concept/07_future/00_version_tracking/rust_1_98_stabilized.md",
            "concept/07_future/00_version_tracking/01_rust_version_tracking.md",
        ],
        "layer": "L2",
        "domain": "version_evolution",
        "origin": "curated",
    },
    {
        "query": "rust 1.97 must_use lint and dead_code_pub_in_binary",
        "expected_concepts": ["rust_1_97_0_stabilized_features", "must_use", "dead_code_pub_in_binary"],
        "expected_sources": [
            "concept/07_future/00_version_tracking/rust_1_97_stabilized.md",
        ],
        "layer": "L2",
        "domain": "version_evolution",
        "origin": "curated",
    },
    {
        "query": "rust 1.98 repr transparent stricter rules",
        "expected_concepts": ["repr_transparent", "memory_model"],
        "expected_sources": [
            "concept/07_future/00_version_tracking/rust_1_98_stabilized.md",
            "concept/03_advanced/02_unsafe/06_memory_model.md",
        ],
        "layer": "L3",
        "domain": "version_evolution",
        "origin": "curated",
    },
    {
        "query": "rust 1.98 PanicHookInfo static Location lifetime",
        "expected_concepts": ["panic_hook_info", "location", "static_lifetime"],
        "expected_sources": [
            "concept/07_future/00_version_tracking/rust_1_98_stabilized.md",
            "concept/02_intermediate/03_error_handling/03_panic.md",
        ],
        "layer": "L3",
        "domain": "version_evolution",
        "origin": "curated",
    },
    {
        "query": "rust 1.96 stabilized features and cargo resolver v3",
        "expected_concepts": ["rust_1_96_stabilized_features", "resolver_v3"],
        "expected_sources": [
            "concept/07_future/00_version_tracking/rust_1_96_stabilized.md",
            "concept/06_ecosystem/01_cargo/17_resolver_v3_public_demo.md",
        ],
        "layer": "L2",
        "domain": "version_evolution",
        "origin": "curated",
    },
    # no_std / embedded
    {
        "query": "no_std rust without standard library",
        "expected_concepts": ["no_std", "embedded_systems"],
        "expected_sources": [
            "concept/06_ecosystem/05_systems_and_embedded/01_no_std.md",
            "concept/06_ecosystem/05_systems_and_embedded/03_embedded_systems.md",
        ],
        "layer": "L3",
        "domain": "ecosystem_embedded",
        "origin": "curated",
    },
    {
        "query": "panic handler and allocator in no_std",
        "expected_concepts": ["panic_handler", "global_allocator", "no_std"],
        "expected_sources": [
            "concept/06_ecosystem/05_systems_and_embedded/52_no_std_allocators_and_panic_handlers.md",
            "concept/06_ecosystem/05_systems_and_embedded/01_no_std.md",
        ],
        "layer": "L3",
        "domain": "ecosystem_embedded",
        "origin": "curated",
    },
    {
        "query": "rtic vs embassy real time framework comparison",
        "expected_concepts": ["rtic", "embassy", "real_time"],
        "expected_sources": [
            "concept/06_ecosystem/05_systems_and_embedded/55_rtic_vs_embassy_real_time_frameworks.md",
        ],
        "layer": "L4",
        "domain": "ecosystem_embedded",
        "origin": "curated",
    },
    {
        "query": "rust for linux kernel module basics",
        "expected_concepts": ["rust_for_linux", "kernel_module"],
        "expected_sources": [
            "concept/06_ecosystem/05_systems_and_embedded/56_rust_for_linux_kernel_module_basics.md",
            "concept/07_future/04_research_and_experimental/04_rust_for_linux.md",
        ],
        "layer": "L4",
        "domain": "ecosystem_embedded",
        "origin": "curated",
    },
    {
        "query": "critical sections and synchronization on bare metal",
        "expected_concepts": ["critical_section", "bare_metal", "synchronization"],
        "expected_sources": [
            "concept/06_ecosystem/05_systems_and_embedded/53_critical_sections_and_sync_on_bare_metal.md",
        ],
        "layer": "L4",
        "domain": "ecosystem_embedded",
        "origin": "curated",
    },
    {
        "query": "linker script and memory layout for embedded rust",
        "expected_concepts": ["linker_script", "memory_layout", "embedded"],
        "expected_sources": [
            "concept/06_ecosystem/05_systems_and_embedded/54_linker_scripts_and_memory_layout.md",
        ],
        "layer": "L4",
        "domain": "ecosystem_embedded",
        "origin": "curated",
    },
    {
        "query": "target tier platform support guarantees",
        "expected_concepts": ["target_tier", "platform_support"],
        "expected_sources": [
            "concept/06_ecosystem/05_systems_and_embedded/10_target_tier_platform_support.md",
        ],
        "layer": "L3",
        "domain": "ecosystem_embedded",
        "origin": "curated",
    },
    # Formal methods
    {
        "query": "separation logic and tree borrows in rust",
        "expected_concepts": ["separation_logic", "tree_borrows", "ownership"],
        "expected_sources": [
            "concept/04_formal/02_separation_logic/01_separation_logic.md",
            "concept/04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md",
        ],
        "layer": "L4",
        "domain": "formal_methods",
        "origin": "curated",
    },
    {
        "query": "RustBelt ownership logic and verification",
        "expected_concepts": ["rustbelt", "ownership_logic", "verification"],
        "expected_sources": [
            "concept/04_formal/01_ownership_logic/01_ownership_formalization.md",
            "concept/04_formal/01_ownership_logic/02_rustbelt_predicate_map.md",
        ],
        "layer": "L5",
        "domain": "formal_methods",
        "origin": "curated",
    },
    {
        "query": "Aeneas symbolic semantics and verification pipeline",
        "expected_concepts": ["aeneas", "symbolic_semantics", "verification"],
        "expected_sources": [
            "concept/04_formal/04_model_checking/06_aeneas_symbolic_semantics.md",
            "concept/04_formal/04_model_checking/07_autoverus.md",
        ],
        "layer": "L5",
        "domain": "formal_methods",
        "origin": "curated",
    },
    {
        "query": "Verus automated verification ecosystem",
        "expected_concepts": ["verus", "automated_verification"],
        "expected_sources": [
            "concept/04_formal/04_model_checking/07_autoverus.md",
            "concept/07_future/02_preview_features/33_autoverus_preview.md",
        ],
        "layer": "L5",
        "domain": "formal_methods",
        "origin": "curated",
    },
    {
        "query": "linear logic and ownership types correspondence",
        "expected_concepts": ["linear_logic", "ownership", "types"],
        "expected_sources": [
            "concept/04_formal/11_computational_models/12_linear_logic_and_ownership.md",
        ],
        "layer": "L5",
        "domain": "formal_methods",
        "origin": "curated",
    },
    {
        "query": "session types and rust channels",
        "expected_concepts": ["session_types", "channels", "concurrency"],
        "expected_sources": [
            "concept/04_formal/11_computational_models/13_session_types_and_rust_channels.md",
        ],
        "layer": "L5",
        "domain": "formal_methods",
        "origin": "curated",
    },
    {
        "query": "effect handlers and rust limited effects",
        "expected_concepts": ["effect_handlers", "effects", "algebraic_effects"],
        "expected_sources": [
            "concept/04_formal/11_computational_models/14_effect_handlers_and_rust_limited_effects.md",
            "concept/07_future/02_preview_features/01_effects_system.md",
        ],
        "layer": "L5",
        "domain": "formal_methods",
        "origin": "curated",
    },
    {
        "query": "refinement types and flux verifier",
        "expected_concepts": ["refinement_types", "flux"],
        "expected_sources": [
            "concept/04_formal/11_computational_models/15_refinement_types_and_flux.md",
        ],
        "layer": "L5",
        "domain": "formal_methods",
        "origin": "curated",
    },
    {
        "query": "Kani bounded model checker for rust",
        "expected_concepts": ["kani", "model_checker"],
        "expected_sources": [
            "concept/04_formal/03_model_checking/01_kani_rust_bounded_model_checker.md",
        ],
        "layer": "L4",
        "domain": "formal_methods",
        "origin": "curated",
    },
    {
        "query": "Miri undefined behavior detector",
        "expected_concepts": ["miri", "undefined_behavior"],
        "expected_sources": [
            "concept/04_formal/03_model_checking/02_miri_rust_undefined_behavior_detector.md",
        ],
        "layer": "L4",
        "domain": "formal_methods",
        "origin": "curated",
    },
    # L0 meta
    {
        "query": "bloom taxonomy for rust learning",
        "expected_concepts": ["bloom_taxonomy", "competency_graph"],
        "expected_sources": [
            "concept/00_meta/00_framework/bloom_taxonomy.md",
        ],
        "layer": "L0",
        "domain": "meta_framework",
        "origin": "curated",
    },
    {
        "query": "rust knowledge graph ontology and SHACL",
        "expected_concepts": ["kg_ontology", "shacl"],
        "expected_sources": [
            "concept/00_meta/knowledge_topology/kg_ontology_v2.md",
            "concept/00_meta/03_audit/09_kg_shacl_engine_validation.md",
        ],
        "layer": "L0",
        "domain": "meta_framework",
        "origin": "curated",
    },
]


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
    parser = argparse.ArgumentParser(description="Generate KG-RAG golden query set.")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT, help="Output JSON path")
    parser.add_argument("--seed", type=int, default=20260804, help="Random seed")
    parser.add_argument("--target", type=int, default=240, help="Minimum number of queries")
    args = parser.parse_args(argv)

    rng = random.Random(args.seed)
    kg = json.loads(KG_PATH.read_text(encoding="utf-8"))

    queries: list[dict[str, Any]] = []
    queries.extend(CURATED_QUERIES)
    queries.extend(kg_derived_queries(kg, rng))

    queries = deduplicate(queries)

    # Ensure target size by adding simple paraphrases if needed.
    entities = kg.get("entities", [])
    if isinstance(entities, list):
        idx = 0
        while len(queries) < args.target and idx < len(entities) * 5:
            entity = entities[idx % len(entities)]
            idx += 1
            label = get_lang(entity.get("skos:prefLabel", []), "en")
            path = entity.get("ex:path")
            if not label or not path:
                continue
            query = f"{label} rust concepts"
            key = query.strip().lower()
            if key in {q["query"].strip().lower() for q in queries}:
                continue
            queries.append({
                "query": query,
                "expected_concepts": [normalize_for_key(label)],
                "expected_sources": [path_to_source(path)],
                "layer": layer_from_entity(entity),
                "domain": entity.get("ex:domain", "uncategorized"),
                "origin": "kg_fallback",
            })

    output = {
        "metadata": {
            "generated": "2026-08-04",
            "count": len(queries),
            "kg_version": kg.get("metadata", {}).get("version", "unknown"),
            "kg_entity_count": len(entities) if isinstance(entities, list) else 0,
            "seed": args.seed,
            "generator": "tools/kg_rag/eval/generate_golden_queries.py",
        },
        "samples": queries,
    }

    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(output, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"[generate_golden_queries] wrote {len(queries)} queries to {args.output}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
