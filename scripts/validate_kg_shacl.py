#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Wave I — KG SHACL 真实引擎验证。

加载 concept/00_meta/kg_data_v3.json，将其转换为 RDF，并用真实 SHACL 引擎
（pySHACL）对 concept/00_meta/kg_shapes.ttl 执行验证。

用法:
    python scripts/validate_kg_shacl.py [--strict]

输出:
    reports/KG_SHACL_PY_<date>.md
    reports/KG_SHACL_PY_<date>.json
"""
from __future__ import annotations

import argparse
import datetime
import json
import os
import sys
from collections import Counter
from pathlib import Path

from pyshacl import validate
from rdflib import DCTERMS, OWL, PROV, RDF, RDFS, SH, SKOS, XSD, Graph, Literal, Namespace, URIRef

ROOT = Path(__file__).resolve().parent.parent
KG_PATH = ROOT / "concept" / "00_meta" / "kg_data_v3.json"
SHAPES_PATH = ROOT / "concept" / "00_meta" / "kg_shapes.ttl"
REPORTS_DIR = ROOT / "reports"

EX = Namespace("https://rust-lang-knowledge-graph.org/")

NS = {
    "ex": EX,
    "rdf": RDF,
    "rdfs": RDFS,
    "xsd": XSD,
    "skos": SKOS,
    "owl": OWL,
    "sh": SH,
    "dcterms": DCTERMS,
    "prov": PROV,
}

# 这些属性在 JSON 中以字符串形式出现，但语义上应解析为 URI
URI_VALUED_PROPS = {
    "rdfs:subClassOf",
    "rdfs:subPropertyOf",
    "rdfs:domain",
    "rdfs:range",
    "owl:inverseOf",
    "owl:equivalentProperty",
    "owl:equivalentClass",
    "owl:disjointWith",
    "ex:subject",
    "ex:predicate",
    "ex:object",
    "@type",
}

# 日期属性应编码为 xsd:date
DATE_PROPS = {"dcterms:created", "dcterms:modified", "dcterms:date"}

# 置信度属性应编码为 xsd:float
FLOAT_PROPS = {"ex:confidence"}

KNOWN_RELATION_PREDICATES = {
    "ex:hasPart",
    "ex:partOf",
    "ex:dependsOn",
    "ex:enables",
    "ex:entails",
    "ex:mutexWith",
    "ex:refines",
    "ex:equivalentTo",
    "ex:counterExample",
    "ex:instanceOf",
    "ex:appliesTo",
    "ex:relatedTo",
}


def to_uri(value: str | None) -> URIRef | None:
    if value is None:
        return None
    if isinstance(value, URIRef):
        return value
    s = str(value).strip()
    if not s:
        return None
    if s.startswith("http://") or s.startswith("https://"):
        return URIRef(s)
    if ":" in s:
        prefix, local = s.split(":", 1)
        if prefix in NS:
            return NS[prefix][local]
    return EX[s]


def looks_like_uri(s: str) -> bool:
    if s.startswith("http://") or s.startswith("https://"):
        return True
    if ":" in s:
        prefix, _ = s.split(":", 1)
        if prefix in NS:
            return True
    return False


def to_literal(v) -> Literal:
    if isinstance(v, bool):
        return Literal(v, datatype=XSD.boolean)
    if isinstance(v, int):
        return Literal(v, datatype=XSD.integer)
    if isinstance(v, float):
        return Literal(v, datatype=XSD.float)
    return Literal(str(v))


def add_value(graph: Graph, subject: URIRef, prop: URIRef, value, prop_id: str | None = None) -> None:
    """把 JSON 值加入图，自动识别语言标签与 URI 引用。"""
    key = prop_id or str(prop)
    if isinstance(value, list):
        for item in value:
            add_single_value(graph, subject, prop, item, key)
    else:
        add_single_value(graph, subject, prop, value, key)


def add_single_value(graph: Graph, subject: URIRef, prop: URIRef, value, prop_id: str) -> None:
    if isinstance(value, dict):
        if "@language" in value:
            graph.add((subject, prop, Literal(value["@value"], lang=value["@language"])))
        elif "@id" in value:
            uri = to_uri(value["@id"])
            if uri:
                graph.add((subject, prop, uri))
        elif "@value" in value:
            graph.add((subject, prop, Literal(value["@value"])))
        else:
            graph.add((subject, prop, Literal(json.dumps(value, ensure_ascii=False))))
    elif isinstance(value, bool):
        graph.add((subject, prop, Literal(value, datatype=XSD.boolean)))
    elif isinstance(value, int):
        graph.add((subject, prop, Literal(value, datatype=XSD.integer)))
    elif isinstance(value, float):
        graph.add((subject, prop, Literal(value, datatype=XSD.float)))
    elif isinstance(value, str) and prop_id in URI_VALUED_PROPS and looks_like_uri(value):
        uri = to_uri(value)
        if uri:
            graph.add((subject, prop, uri))
    elif isinstance(value, str) and prop_id in DATE_PROPS:
        # 支持 ISO 日期；若含时间则使用 xsd:dateTime，否则 xsd:date
        if "T" in value:
            graph.add((subject, prop, Literal(value, datatype=XSD.dateTime)))
        else:
            graph.add((subject, prop, Literal(value, datatype=XSD.date)))
    elif isinstance(value, str) and prop_id in FLOAT_PROPS:
        graph.add((subject, prop, Literal(float(value), datatype=XSD.float)))
    else:
        graph.add((subject, prop, to_literal(value)))


def load_kg_graph(path: Path) -> Graph:
    """加载项目 KG JSON 并转换为标准 RDF 图。"""
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)

    g = Graph()
    for prefix, ns in NS.items():
        g.bind(prefix, ns)

    # metadata -> KG node
    meta = data.get("metadata", {})
    kg_node = EX.KnowledgeGraph_v3
    g.add((kg_node, RDF.type, EX.KnowledgeGraph))
    meta_key_map = {
        "rust_version": "ex:rustVersion",
        "entity_count": "ex:entityCount",
        "relation_count": "ex:relationCount",
        "generated": "dcterms:modified",
    }
    for k, v in meta.items():
        mapped = meta_key_map.get(k, k)
        prop = to_uri(mapped) or EX[mapped]
        add_value(g, kg_node, prop, v, mapped)

    # classes
    for c in data.get("classes", []):
        cid = to_uri(c.get("@id"))
        if not cid:
            continue
        for t in as_list(c.get("@type")):
            g.add((cid, RDF.type, to_uri(t)))
        for k, v in c.items():
            if k in ("@id",):
                continue
            prop = to_uri(k) or EX[k]
            add_value(g, cid, prop, v, k)

    # properties
    for p in data.get("properties", []):
        pid = to_uri(p.get("@id"))
        if not pid:
            continue
        for t in as_list(p.get("@type")):
            g.add((pid, RDF.type, to_uri(t)))
        for k, v in p.items():
            if k in ("@id",):
                continue
            prop = to_uri(k) or EX[k]
            add_value(g, pid, prop, v, k)

    # entities
    for e in data.get("entities", []):
        eid = e.get("@id")
        euri = to_uri(eid)
        if not euri:
            continue
        etype = e.get("@type")
        if isinstance(etype, list):
            etype = etype[0] if etype else None
        if etype:
            g.add((euri, RDF.type, to_uri(etype)))
        for k, v in e.items():
            if k in ("@id", "@type"):
                continue
            prop = to_uri(k) or EX[k]
            add_value(g, euri, prop, v, k)

    # relations -> plain triples + reified annotation nodes (RDF-star ready)
    for r in data.get("relations", []):
        subj = to_uri(r.get("ex:subject"))
        pred = to_uri(r.get("ex:predicate"))
        obj_raw = r.get("ex:object")
        if not subj or not pred:
            continue
        if isinstance(obj_raw, str) and looks_like_uri(obj_raw):
            obj = to_uri(obj_raw)
        else:
            obj = to_literal(obj_raw)
        if not obj:
            continue
        g.add((subj, pred, obj))

        # 为 RDF-star 保留关系元数据节点（如果存在）
        rid = r.get("@id")
        if rid:
            ruri = to_uri(rid) if looks_like_uri(rid) else EX[f"rel_{hash(str(rid)) & 0x7FFFFFFF}"]
            g.add((ruri, RDF.type, EX.RelationAnnotation))
            g.add((ruri, EX.subject, subj))
            g.add((ruri, EX.predicate, pred))
            g.add((ruri, EX.object, obj))
            for k, v in r.items():
                if k in ("@id", "ex:subject", "ex:predicate", "ex:object"):
                    continue
                prop = to_uri(k) or EX[k]
                add_value(g, ruri, prop, v, k)

    return g


def as_list(value):
    if value is None:
        return []
    return value if isinstance(value, list) else [value]


def export_neo4j_csv(raw: dict, out_dir: Path) -> tuple[Path, Path]:
    """导出 Neo4j 批量导入 CSV：nodes.csv + relationships.csv。"""
    import csv

    out_dir.mkdir(parents=True, exist_ok=True)
    nodes_path = out_dir / "kg_neo4j_nodes.csv"
    rels_path = out_dir / "kg_neo4j_relationships.csv"

    node_fields = ["id:ID", "label:LABEL", "path", "layer", "domain", "bloomLevel", "rustVersion", "en", "zh"]
    with open(nodes_path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(node_fields)
        for e in raw.get("entities", []):
            eid = e.get("@id", "").replace("ex:", "")
            label = e.get("@type", "Entity").replace("ex:", "")
            path = e.get("ex:path", "")
            layer = e.get("ex:layer", "")
            domain = e.get("ex:domain", "")
            bloom = e.get("ex:bloomLevel", "")
            version = e.get("ex:rustVersion", "")
            labels = e.get("skos:prefLabel", [])
            en = next((x["@value"] for x in labels if x.get("@language") == "en"), "")
            zh = next((x["@value"] for x in labels if x.get("@language") == "zh"), "")
            w.writerow([eid, label, path, layer, domain, bloom, version, en, zh])

    rel_fields = [":START_ID", ":END_ID", ":TYPE", "source", "confidence:float", "version", "reviewed:boolean"]
    with open(rels_path, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(rel_fields)
        for r in raw.get("relations", []):
            subj = str(r.get("ex:subject", "")).replace("ex:", "")
            obj = str(r.get("ex:object", "")).replace("ex:", "")
            pred = str(r.get("ex:predicate", "")).replace("ex:", "")
            source = r.get("ex:source", "")
            confidence = r.get("ex:confidence", "")
            version = r.get("ex:version", "")
            reviewed = bool(r.get("ex:reviewed", False))
            w.writerow([subj, obj, pred, source, confidence, version, reviewed])

    return nodes_path, rels_path


def classify_violation(result_graph: Graph) -> dict[str, int]:
    """按 sh:sourceConstraintComponent / sh:resultPath 对 violation 分类。"""
    counter: Counter[str] = Counter()
    for s in result_graph.subjects(RDF.type, SH.ValidationResult):
        severity = result_graph.value(s, SH.resultSeverity)
        if severity and severity != SH.Violation:
            continue
        comp = result_graph.value(s, SH.sourceConstraintComponent)
        path = result_graph.value(s, SH.resultPath)
        msg = result_graph.value(s, SH.resultMessage)
        key_parts = []
        if comp:
            key_parts.append(str(comp).split("#")[-1])
        if path:
            key_parts.append(str(path).split("/")[-1].split("#")[-1])
        if not key_parts:
            key_parts.append(str(msg)[:60] if msg else "unknown")
        counter["/".join(key_parts)] += 1
    return dict(counter)


def main() -> int:
    ap = argparse.ArgumentParser(description="Validate KG against SHACL shapes using a real engine.")
    ap.add_argument("--strict", action="store_true", help="Exit 1 if any violation is found.")
    ap.add_argument("--kg", type=Path, default=KG_PATH)
    ap.add_argument("--shapes", type=Path, default=SHAPES_PATH)
    ap.add_argument("--date", default=datetime.date.today().isoformat())
    ap.add_argument("--export-neo4j", type=Path, metavar="DIR",
                    help="Export KG as Neo4j bulk-import CSV nodes/relationships to DIR.")
    args = ap.parse_args()

    if not args.kg.exists():
        print(f"ERROR: KG file not found: {args.kg}", file=sys.stderr)
        return 2
    if not args.shapes.exists():
        print(f"ERROR: SHACL shapes file not found: {args.shapes}", file=sys.stderr)
        return 2

    print(f"[validate_kg_shacl] loading KG: {args.kg}")
    data_graph = load_kg_graph(args.kg)
    print(f"[validate_kg_shacl] KG triples: {len(data_graph)}")

    print(f"[validate_kg_shacl] loading shapes: {args.shapes}")
    shapes_graph = Graph()
    shapes_graph.parse(args.shapes, format="turtle")
    print(f"[validate_kg_shacl] shape triples: {len(shapes_graph)}")

    print("[validate_kg_shacl] running pySHACL validation ...")
    conforms, results_graph, results_text = validate(
        data_graph,
        shacl_graph=shapes_graph,
        ont_graph=None,
        inference="rdfs",
        abort_on_first=False,
        meta_shacl=False,
        debug=False,
    )

    violations_by_type = classify_violation(results_graph)
    total_violations = sum(violations_by_type.values())

    # 计算实体 / 关系统计
    with open(args.kg, "r", encoding="utf-8") as f:
        raw = json.load(f)
    entity_count = len(raw.get("entities", []))
    relation_count = len(raw.get("relations", []))

    if args.export_neo4j:
        export_dir = args.export_neo4j.resolve()
        nodes_csv, rels_csv = export_neo4j_csv(raw, export_dir)
        try:
            print(f"[validate_kg_shacl] Neo4j nodes: {nodes_csv.relative_to(ROOT)}")
            print(f"[validate_kg_shacl] Neo4j relationships: {rels_csv.relative_to(ROOT)}")
        except ValueError:
            print(f"[validate_kg_shacl] Neo4j nodes: {nodes_csv}")
            print(f"[validate_kg_shacl] Neo4j relationships: {rels_csv}")

    summary = {
        "date": args.date,
        "engine": "pySHACL",
        "engine_version": __import__("pyshacl").__version__,
        "kg_file": str(args.kg.relative_to(ROOT)).replace("\\", "/"),
        "shapes_file": str(args.shapes.relative_to(ROOT)).replace("\\", "/"),
        "inference": "rdfs",
        "triples": len(data_graph),
        "entities": entity_count,
        "relations": relation_count,
        "conforms": bool(conforms),
        "violations_total": total_violations,
        "violations_by_type": violations_by_type,
    }

    REPORTS_DIR.mkdir(parents=True, exist_ok=True)
    json_path = REPORTS_DIR / f"KG_SHACL_PY_{args.date}.json"
    md_path = REPORTS_DIR / f"KG_SHACL_PY_{args.date}.md"

    with open(json_path, "w", encoding="utf-8") as f:
        json.dump(summary, f, ensure_ascii=False, indent=2)

    with open(md_path, "w", encoding="utf-8") as f:
        f.write("# Wave I — KG SHACL 真实引擎验证报告\n\n")
        f.write(f"**日期**: {args.date}  ")
        f.write(f"**引擎**: pySHACL {summary['engine_version']}  ")
        f.write(f"**推理**: {summary['inference']}\n\n")
        f.write("## 元数据\n\n")
        f.write(f"- KG 文件: `{summary['kg_file']}`\n")
        f.write(f"- SHACL 形状: `{summary['shapes_file']}`\n")
        f.write(f"- RDF 三元组: {summary['triples']}\n")
        f.write(f"- 实体数: {summary['entities']}\n")
        f.write(f"- 关系数: {summary['relations']}\n\n")
        f.write("## 验证结果\n\n")
        status = "✅ 通过" if conforms else "❌ 未通过"
        f.write(f"**SHACL conforms**: {status}  \n")
        f.write(f"**Violation 总数**: {total_violations}\n\n")
        if violations_by_type:
            f.write("### Violation 分类\n\n")
            f.write("| 类型 | 数量 |\n|---:|---:|\n")
            for typ, cnt in sorted(violations_by_type.items(), key=lambda x: -x[1]):
                f.write(f"| {typ} | {cnt} |\n")
            f.write("\n")
        else:
            f.write("未发现 SHACL violation。\n\n")
        if results_text:
            f.write("## 原始验证输出\n\n")
            f.write("```text\n")
            f.write(results_text[:8000])
            if len(results_text) > 8000:
                f.write("\n... (truncated)")
            f.write("\n```\n")
        f.write("\n## 机器可读\n\n")
        f.write(f"- JSON: `reports/KG_SHACL_PY_{args.date}.json`\n")

    print(f"[validate_kg_shacl] conforms={conforms} violations={total_violations}")
    print(f"[validate_kg_shacl] report: {md_path.relative_to(ROOT)}")
    if violations_by_type:
        print("[validate_kg_shacl] violation breakdown:")
        for typ, cnt in sorted(violations_by_type.items(), key=lambda x: -x[1]):
            print(f"  - {typ}: {cnt}")

    if args.strict and not conforms:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
