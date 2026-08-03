#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Validate the project knowledge graph against W3C SHACL shapes using pySHACL.

Loads `concept/00_meta/kg_data_v3.json` as JSON-LD (via rdflib's JSON-LD plugin)
and `concept/00_meta/kg_shapes.ttl` as SHACL shapes, then runs a real SHACL
engine validation with RDFS inference.

Usage:
    python tools/kg_shacl/validate_kg_shacl.py

Outputs:
    reports/KG_SHACL_ENGINE_VALIDATION_<date>.md
    reports/KG_SHACL_ENGINE_VALIDATION_<date>.json

Exit codes:
    0 - conforms (no SHACL violations)
    1 - violations found
    2 - input file missing or unreadable
"""
from __future__ import annotations

import argparse
import datetime
import json
import os
import sys
from pathlib import Path
from typing import Any

try:
    from pyshacl import validate
    from rdflib import DCTERMS, RDF, SH, Graph, Namespace
except ImportError as exc:  # pragma: no cover - dependency guidance
    print(
        "ERROR: pyshacl and rdflib are required. "
        "Activate the project venv or run:\n"
        "  tools/kg_shacl/.venv/Scripts/python tools/kg_shacl/validate_kg_shacl.py",
        file=sys.stderr,
    )
    raise SystemExit(2) from exc

ROOT = Path(__file__).resolve().parent.parent.parent
KG_PATH = ROOT / "concept" / "00_meta" / "kg_data_v3.json"
SHAPES_PATH = ROOT / "concept" / "00_meta" / "kg_shapes.ttl"
REPORTS_DIR = ROOT / "reports"

EX = Namespace("https://rust-lang-knowledge-graph.org/")

NS = {
    "ex": EX,
    "rdf": RDF,
    "rdfs": Namespace("http://www.w3.org/2000/01/rdf-schema#"),
    "owl": Namespace("http://www.w3.org/2002/07/owl#"),
    "skos": Namespace("http://www.w3.org/2004/02/skos/core#"),
    "xsd": Namespace("http://www.w3.org/2001/XMLSchema#"),
    "sh": SH,
    "dcterms": DCTERMS,
    "prov": Namespace("http://www.w3.org/ns/prov#"),
}

# JSON-LD @context type coercion so plain JSON strings are typed as typed literals.
TYPE_COERCION = {
    "dcterms:created": {"@id": "dcterms:created", "@type": "xsd:date"},
    "dcterms:modified": {"@id": "dcterms:modified", "@type": "xsd:date"},
    "ex:confidence": {"@id": "ex:confidence", "@type": "xsd:float"},
    "ex:reviewed": {"@id": "ex:reviewed", "@type": "xsd:boolean"},
    "ex:entityCount": {"@id": "ex:entityCount", "@type": "xsd:integer"},
    "ex:relationCount": {"@id": "ex:relationCount", "@type": "xsd:integer"},
}


def looks_like_uri(value: Any) -> bool:
    """Return True if the value should be treated as an IRI in this project."""
    if not isinstance(value, str):
        return False
    return value.startswith("ex:") or value.startswith("http://") or value.startswith("https://")


def build_jsonld_document(kg: dict[str, Any]) -> dict[str, Any]:
    """Convert the project's custom KG JSON into a standard JSON-LD @graph document.

    The KG uses a custom layout (metadata, classes, properties, entities,
    relations). This function rewrites it as a flat JSON-LD graph so rdflib's
    JSON-LD parser can load it directly, while preserving relation metadata as
    reified `ex:RelationAnnotation` nodes and materializing the actual triples.
    """
    context = dict(kg.get("@context", {}))
    context.update(TYPE_COERCION)

    doc: dict[str, Any] = {"@context": context, "@graph": []}

    # Metadata -> KnowledgeGraph node
    meta = kg.get("metadata", {})
    doc["@graph"].append({
        "@id": "ex:KnowledgeGraph_v3",
        "@type": "ex:KnowledgeGraph",
        "ex:rustVersion": meta.get("rust_version", ""),
        "ex:entityCount": meta.get("entity_count", 0),
        "ex:relationCount": meta.get("relation_count", 0),
        "dcterms:modified": meta.get("generated", ""),
    })

    # Classes, properties, and entities are already node-shaped
    doc["@graph"].extend(kg.get("classes", []))
    doc["@graph"].extend(kg.get("properties", []))
    doc["@graph"].extend(kg.get("entities", []))

    # Relations: materialize triples + reified annotation nodes
    for idx, r in enumerate(kg.get("relations", [])):
        subj = r.get("ex:subject")
        pred = r.get("ex:predicate")
        obj = r.get("ex:object")
        if not (subj and pred and obj):
            continue

        # Material triple
        triple_obj: Any = {"@id": obj} if looks_like_uri(obj) else obj
        doc["@graph"].append({"@id": subj, pred: triple_obj})

        # Reified annotation node carrying relation-level metadata
        ann_id = r.get("@id")
        if not ann_id:
            ann_id = f"_:rel{idx}"
        ann: dict[str, Any] = {
            "@id": ann_id,
            "@type": "ex:RelationAnnotation",
            "ex:subject": {"@id": subj},
            "ex:predicate": {"@id": pred},
            "ex:object": {"@id": obj} if looks_like_uri(obj) else obj,
        }
        for k, v in r.items():
            if k in ("@id", "@type", "ex:subject", "ex:predicate", "ex:object"):
                continue
            ann[k] = v
        doc["@graph"].append(ann)

    return doc


def load_data_graph(kg_path: Path) -> Graph:
    """Load the KG JSON and return an rdflib Graph parsed via JSON-LD."""
    with open(kg_path, "r", encoding="utf-8") as f:
        kg = json.load(f)

    doc = build_jsonld_document(kg)
    g = Graph()
    for prefix, ns in NS.items():
        g.bind(prefix, ns)
    g.parse(data=json.dumps(doc, ensure_ascii=False), format="json-ld")
    return g, kg


def extract_violations(results_graph: Graph) -> list[dict[str, Any]]:
    """Extract human-readable violation records from the SHACL validation report."""
    violations: list[dict[str, Any]] = []
    for result in results_graph.subjects(RDF.type, SH.ValidationResult):
        severity = results_graph.value(result, SH.resultSeverity)
        focus = results_graph.value(result, SH.focusNode)
        path = results_graph.value(result, SH.resultPath)
        value = results_graph.value(result, SH.value)
        source_shape = results_graph.value(result, SH.sourceShape)
        source_constraint = results_graph.value(result, SH.sourceConstraintComponent)
        message = results_graph.value(result, SH.resultMessage)

        violations.append({
            "severity": str(severity) if severity else None,
            "focus_node": str(focus) if focus else None,
            "result_path": str(path) if path else None,
            "value": str(value) if value else None,
            "result_message": str(message) if message else None,
            "source_shape": str(source_shape) if source_shape else None,
            "source_constraint_component": str(source_constraint) if source_constraint else None,
        })
    return violations


def write_reports(
    date: str,
    kg_file: str,
    shapes_file: str,
    triples: int,
    entities: int,
    relations: int,
    conforms: bool,
    violations: list[dict[str, Any]],
    results_text: str,
) -> tuple[Path, Path]:
    """Write Markdown and JSON validation reports."""
    REPORTS_DIR.mkdir(parents=True, exist_ok=True)
    json_path = REPORTS_DIR / f"KG_SHACL_ENGINE_VALIDATION_{date}.json"
    md_path = REPORTS_DIR / f"KG_SHACL_ENGINE_VALIDATION_{date}.md"

    summary = {
        "date": date,
        "engine": "pySHACL",
        "engine_version": __import__("pyshacl").__version__,
        "kg_file": kg_file,
        "shapes_file": shapes_file,
        "inference": "rdfs",
        "triples": triples,
        "entities": entities,
        "relations": relations,
        "conforms": conforms,
        "violations_total": len(violations),
        "violations": violations,
    }

    with open(json_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, ensure_ascii=False, indent=2)

    with open(md_path, "w", encoding="utf-8") as f:
        f.write("# KG SHACL 引擎验证报告\n\n")
        f.write(f"**日期**: {date}  ")
        f.write(f"**引擎**: pySHACL {summary['engine_version']}  ")
        f.write(f"**推理**: {summary['inference']}\n\n")
        f.write("## 元数据\n\n")
        f.write(f"- KG 文件: `{kg_file}`\n")
        f.write(f"- SHACL 形状: `{shapes_file}`\n")
        f.write(f"- RDF 三元组: {triples}\n")
        f.write(f"- 实体数: {entities}\n")
        f.write(f"- 关系数: {relations}\n\n")
        f.write("## 验证结果\n\n")
        status = "✅ 通过" if conforms else "❌ 未通过"
        f.write(f"**SHACL conforms**: {status}  \n")
        f.write(f"**Violation 总数**: {len(violations)}\n\n")

        if violations:
            f.write("### Violation 明细\n\n")
            f.write("| # | Severity | Focus Node | Result Path | Message |\n")
            f.write("|---:|---|---|---|---|\n")
            for i, v in enumerate(violations[:200], start=1):
                severity = v.get("severity") or ""
                focus = v.get("focus_node") or ""
                path = v.get("result_path") or ""
                msg = (v.get("result_message") or "").replace("|", "\\|")
                if len(msg) > 120:
                    msg = msg[:117] + "..."
                f.write(f"| {i} | `{severity}` | `{focus}` | `{path}` | {msg} |\n")
            if len(violations) > 200:
                f.write(f"\n> 仅显示前 200 条，共 {len(violations)} 条。完整列表见 JSON 报告。\n")
            f.write("\n")
        else:
            f.write("未发现 SHACL violation。\n\n")

        if results_text:
            f.write("## 原始验证输出\n\n")
            f.write("```text\n")
            f.write(results_text[:12000])
            if len(results_text) > 12000:
                f.write("\n... (truncated)")
            f.write("\n```\n")

        f.write("\n## 机器可读\n\n")
        f.write(f"- JSON: `reports/KG_SHACL_ENGINE_VALIDATION_{date}.json`\n")

    return md_path, json_path


def main() -> int:
    ap = argparse.ArgumentParser(
        description="Validate the Rust knowledge graph against SHACL shapes using pySHACL."
    )
    ap.add_argument("--kg", type=Path, default=KG_PATH, help="Path to kg_data_v3.json")
    ap.add_argument("--shapes", type=Path, default=SHAPES_PATH, help="Path to kg_shapes.ttl")
    ap.add_argument("--date", default=datetime.date.today().isoformat(), help="Report date stamp")
    args = ap.parse_args()

    if not args.kg.exists():
        print(f"ERROR: KG file not found: {args.kg}", file=sys.stderr)
        return 2
    if not args.shapes.exists():
        print(f"ERROR: SHACL shapes file not found: {args.shapes}", file=sys.stderr)
        return 2

    print(f"[validate_kg_shacl] loading KG as JSON-LD: {args.kg}")
    data_graph, raw_kg = load_data_graph(args.kg)
    triples = len(data_graph)
    entities = len(raw_kg.get("entities", []))
    relations = len(raw_kg.get("relations", []))
    print(f"[validate_kg_shacl] triples={triples} entities={entities} relations={relations}")

    print(f"[validate_kg_shacl] loading SHACL shapes: {args.shapes}")
    shapes_graph = Graph()
    shapes_graph.parse(args.shapes, format="turtle")
    print(f"[validate_kg_shacl] shape triples={len(shapes_graph)}")

    print("[validate_kg_shacl] running pySHACL validation (inference=rdfs) ...")
    conforms, results_graph, results_text = validate(
        data_graph,
        shacl_graph=shapes_graph,
        inference="rdfs",
        abort_on_first=False,
    )

    violations = extract_violations(results_graph)

    def rel_or_abs(path: Path) -> str:
        try:
            return path.relative_to(ROOT).as_posix()
        except ValueError:
            return path.as_posix()

    md_path, json_path = write_reports(
        args.date,
        rel_or_abs(args.kg),
        rel_or_abs(args.shapes),
        triples,
        entities,
        relations,
        bool(conforms),
        violations,
        results_text,
    )

    print(f"[validate_kg_shacl] conforms={conforms} violations={len(violations)}")
    print(f"[validate_kg_shacl] markdown report: {md_path.relative_to(ROOT).as_posix()}")
    print(f"[validate_kg_shacl] json report: {json_path.relative_to(ROOT).as_posix()}")

    return 0 if conforms else 1


if __name__ == "__main__":
    sys.exit(main())
