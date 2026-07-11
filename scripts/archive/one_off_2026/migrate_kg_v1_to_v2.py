#!/usr/bin/env python3
"""
将 kg_data.json (v1) 迁移到 kg_data_v2.json (RDF 1.2 / SKOS / JSON-LD 1.1)。

用法:
    python scripts/migrate_kg_v1_to_v2.py \
        --input concept/00_meta/kg_data.json \
        --output concept/00_meta/kg_data_v2.json \
        --rust-version 1.96.0

迁移规则:
1. 保留 v1 的 entities / relations / decision_trees / fault_trees 结构。
2. 将 @context 扩展为 RDF 1.2 / SKOS / OWL / SHACL / DC / PROV 命名空间。
3. 为每个实体添加 skos:prefLabel / skos:definition（en + zh）。
4. 将关系从扁平三元组转换为 RDF-star 注解对象（ex:subject/predicate/object + 元数据）。
5. 为所有关系附加默认元数据：ex:source="v1-migration", ex:confidence=0.8, reviewed=false。
"""

import argparse
import json
from datetime import date
from pathlib import Path
from typing import Any

TYPE_MAP = {
    "concepts": "ex:Concept",
    "theories": "ex:Theory",
    "models": "ex:Model",
    "properties": "ex:Property",
    "rules": "ex:Rule",
    "primitives": "ex:Primitive",
}

RELATION_REVERSE = {
    "dependsOn": "ex:enables",
    "entails": "ex:impliedBy",
    "mutexWith": "ex:mutexWith",
    "refines": "ex:refinedBy",
    "equivalentTo": "ex:equivalentTo",
    "counterExample": "ex:refutedBy",
    "instanceOf": "ex:hasInstance",
    "appliesTo": "ex:governedBy",
}


def to_skos_label(value: dict) -> list[dict]:
    """将 v1 的 {label_en, label_zh} 转换为 SKOS LangString 列表。"""
    labels = []
    if "label_en" in value and value["label_en"]:
        labels.append({"@value": value["label_en"], "@language": "en"})
    if "label_zh" in value and value["label_zh"]:
        labels.append({"@value": value["label_zh"], "@language": "zh"})
    return labels


def migrate_entity(category: str, value: dict) -> dict:
    """迁移单个实体。"""
    entity: dict = {
        "@id": value["id"],
        "@type": TYPE_MAP.get(category, "ex:Concept"),
        "skos:prefLabel": to_skos_label(value),
    }

    if "layer" in value:
        entity["ex:layer"] = value["layer"]
    if "bloom" in value:
        entity["ex:bloom"] = value["bloom"]
    if "asp" in value:
        entity["ex:asp"] = value["asp"]

    # 从 label 生成简单定义（后续可人工完善）
    definitions = []
    if "label_en" in value:
        definitions.append({"@value": f"Rust concept: {value['label_en']}.", "@language": "en"})
    if "label_zh" in value:
        definitions.append({"@value": f"Rust 概念：{value['label_zh']}。", "@language": "zh"})
    if definitions:
        entity["skos:definition"] = definitions

    return entity


def migrate_relation(rel: dict, rust_version: str) -> dict:
    """迁移单个关系为 RDF-star 注解对象。"""
    return {
        "@id": f"_:rel_{rel['source'].replace(':', '_')}_{rel['relation']}_{rel['target'].replace(':', '_')}",
        "@type": "ex:RelationAnnotation",
        "ex:subject": rel["source"],
        "ex:predicate": f"ex:{rel['relation']}",
        "ex:object": rel["target"],
        "ex:source": "v1-migration",
        "ex:confidence": 0.8,
        "ex:version": rust_version,
        "ex:reviewed": False,
        "dcterms:created": str(date.today()),
    }


def migrate(input_path: Path, output_path: Path, rust_version: str) -> None:
    with input_path.open("r", encoding="utf-8") as f:
        v1 = json.load(f)

    v2: dict[str, Any] = {
        "@context": {
            "ex": "https://rust-lang-knowledge-graph.org/",
            "rdf": "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
            "rdfs": "http://www.w3.org/2000/01/rdf-schema#",
            "owl": "http://www.w3.org/2002/07/owl#",
            "skos": "http://www.w3.org/2004/02/skos/core#",
            "xsd": "http://www.w3.org/2001/XMLSchema#",
            "dcterms": "http://purl.org/dc/terms/",
            "prov": "http://www.w3.org/ns/prov#",
        },
        "metadata": {
            "version": "2.0",
            "generated": str(date.today()),
            "rust_version": rust_version,
            "source": "concept/00_meta/kg_ontology_v2.md",
            "previous_version": str(input_path),
            "alignment": "RDF 1.2 / RDF-star / SKOS / JSON-LD 1.1 / SHACL",
        },
        "classes": [
            {
                "@id": "ex:Concept",
                "@type": ["rdfs:Class", "owl:Class"],
                "rdfs:subClassOf": "skos:Concept",
                "skos:prefLabel": [
                    {"@value": "Concept", "@language": "en"},
                    {"@value": "概念", "@language": "zh"},
                ],
            },
            {
                "@id": "ex:Theory",
                "@type": ["rdfs:Class", "owl:Class"],
                "rdfs:subClassOf": "skos:Concept",
                "skos:prefLabel": [
                    {"@value": "Theory", "@language": "en"},
                    {"@value": "理论", "@language": "zh"},
                ],
            },
            {
                "@id": "ex:Model",
                "@type": ["rdfs:Class", "owl:Class"],
                "rdfs:subClassOf": "skos:Concept",
                "skos:prefLabel": [
                    {"@value": "Model", "@language": "en"},
                    {"@value": "模型", "@language": "zh"},
                ],
            },
            {
                "@id": "ex:Property",
                "@type": ["rdfs:Class", "owl:Class"],
                "rdfs:subClassOf": "skos:Concept",
                "skos:prefLabel": [
                    {"@value": "Property", "@language": "en"},
                    {"@value": "属性", "@language": "zh"},
                ],
            },
            {
                "@id": "ex:Rule",
                "@type": ["rdfs:Class", "owl:Class"],
                "rdfs:subClassOf": "skos:Concept",
                "skos:prefLabel": [
                    {"@value": "Rule", "@language": "en"},
                    {"@value": "规则", "@language": "zh"},
                ],
            },
            {
                "@id": "ex:Primitive",
                "@type": ["rdfs:Class", "owl:Class"],
                "rdfs:subClassOf": "skos:Concept",
                "skos:prefLabel": [
                    {"@value": "Primitive", "@language": "en"},
                    {"@value": "原语", "@language": "zh"},
                ],
            },
        ],
        "properties": [
            {
                "@id": "ex:dependsOn",
                "@type": ["owl:ObjectProperty", "owl:TransitiveProperty"],
                "owl:inverseOf": "ex:enables",
                "rdfs:label": [
                    {"@value": "depends on", "@language": "en"},
                    {"@value": "依赖于", "@language": "zh"},
                ],
            },
            {
                "@id": "ex:entails",
                "@type": ["owl:ObjectProperty", "owl:TransitiveProperty"],
                "owl:inverseOf": "ex:impliedBy",
                "rdfs:label": [
                    {"@value": "entails", "@language": "en"},
                    {"@value": "蕴含", "@language": "zh"},
                ],
            },
            {
                "@id": "ex:mutexWith",
                "@type": ["owl:ObjectProperty", "owl:SymmetricProperty", "owl:IrreflexiveProperty"],
                "rdfs:label": [
                    {"@value": "mutex with", "@language": "en"},
                    {"@value": "互斥于", "@language": "zh"},
                ],
            },
            {
                "@id": "ex:refines",
                "@type": ["owl:ObjectProperty", "owl:TransitiveProperty"],
                "owl:inverseOf": "ex:refinedBy",
                "rdfs:label": [
                    {"@value": "refines", "@language": "en"},
                    {"@value": "细化于", "@language": "zh"},
                ],
            },
            {
                "@id": "ex:equivalentTo",
                "@type": ["owl:ObjectProperty", "owl:SymmetricProperty", "owl:TransitiveProperty", "owl:ReflexiveProperty"],
                "rdfs:label": [
                    {"@value": "equivalent to", "@language": "en"},
                    {"@value": "等价于", "@language": "zh"},
                ],
            },
            {
                "@id": "ex:counterExample",
                "@type": "owl:ObjectProperty",
                "owl:inverseOf": "ex:refutedBy",
                "rdfs:label": [
                    {"@value": "counter example", "@language": "en"},
                    {"@value": "反例", "@language": "zh"},
                ],
            },
            {
                "@id": "ex:instanceOf",
                "@type": "owl:ObjectProperty",
                "owl:inverseOf": "ex:hasInstance",
                "rdfs:label": [
                    {"@value": "instance of", "@language": "en"},
                    {"@value": "实例于", "@language": "zh"},
                ],
            },
            {
                "@id": "ex:appliesTo",
                "@type": "owl:ObjectProperty",
                "owl:inverseOf": "ex:governedBy",
                "rdfs:label": [
                    {"@value": "applies to", "@language": "en"},
                    {"@value": "适用于", "@language": "zh"},
                ],
            },
        ],
        "entities": {},
        "relations": [],
        "decision_trees": v1.get("decision_trees", []),
        "fault_trees": v1.get("fault_trees", []),
    }

    # 迁移实体
    entities_v2: dict[str, list[dict]] = {}
    for category, items in v1.get("entities", {}).items():
        entities_v2[category] = [migrate_entity(category, item) for item in items]
    v2["entities"] = entities_v2

    # 迁移关系
    v2["relations"] = [migrate_relation(rel, rust_version) for rel in v1.get("relations", [])]

    with output_path.open("w", encoding="utf-8") as f:
        json.dump(v2, f, ensure_ascii=False, indent=2)

    print(f"迁移完成: {input_path} -> {output_path}")
    print(f"实体数量: {sum(len(v) for v in entities_v2.values())}")
    print(f"关系数量: {len(v2['relations'])}")


def main() -> None:
    parser = argparse.ArgumentParser(description="Migrate kg_data.json v1 to v2")
    parser.add_argument("--input", default="concept/00_meta/kg_data.json", help="v1 输入文件")
    parser.add_argument("--output", default="concept/00_meta/kg_data_v2.json", help="v2 输出文件")
    parser.add_argument("--rust-version", default="1.96.0+", help="Rust 版本")
    args = parser.parse_args()

    migrate(Path(args.input), Path(args.output), args.rust_version)


if __name__ == "__main__":
    main()
