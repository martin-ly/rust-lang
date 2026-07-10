#!/usr/bin/env python3
"""从 kg_index.json 与 kg_data_v3.json 模板生成完整的 KG v3 数据。

本脚本保留 kg_data_v3.json 中的 @context、classes、properties、decision_trees、
fault_trees 等模式定义，将其 entities 与 relations 替换为从 kg_index.json 自动派生
的完整概念实体与关系三元组。

输出: concept/00_meta/kg_data_v3.json
"""

from __future__ import annotations

import json
import re
import sys
from pathlib import Path
from urllib.parse import quote

ROOT = Path(__file__).resolve().parents[1]
CONCEPT_DIR = ROOT / "concept"
KG_INDEX_PATH = CONCEPT_DIR / "00_meta" / "kg_index.json"
KG_V3_TEMPLATE_PATH = CONCEPT_DIR / "00_meta" / "kg_data_v3.json"
KG_V3_OUTPUT_PATH = CONCEPT_DIR / "00_meta" / "kg_data_v3.json"


def sanitize_id(text: str) -> str:
    """将英文标题转换为 ex: 前缀可用的 CamelCase ID。"""
    # Remove backticks, markdown links, punctuation
    text = re.sub(r"`", "", text)
    text = re.sub(r"\[([^\]]+)\]\([^)]+\)", r"\1", text)
    text = re.sub(r"[^\w\s-]", " ", text)
    words = [w for w in re.split(r"[\s-]+", text) if w]
    return "".join(w[:1].upper() + w[1:] for w in words)


def concept_iri(en_title: str, path: str) -> str:
    """生成稳定的概念 IRI。

    优先使用英文标题的 CamelCase；若标题为空或冲突风险高，则回退到路径。
    """
    title_id = sanitize_id(en_title)
    if len(title_id) >= 2 and re.match(r"^[A-Z]", title_id):
        return f"ex:{title_id}"
    # Fallback to URL-encoded path
    safe_path = quote(path.replace("\\", "/"), safe="/")
    return f"ex:{safe_path}"


def map_bloom_to_class(bloom: str | None, path: str) -> str:
    """根据 Bloom 层级与路径推断 RDF 类。"""
    if not bloom:
        return "ex:Concept"
    b = bloom.lower()
    if "formal" in path or "linear_logic" in path or "separation_logic" in path or "model_checking" in path:
        return "ex:Theory"
    if "l6" in b or "l7" in b or "evaluate" in b or "create" in b:
        return "ex:Model"
    if "l0" in b or "l1" in b:
        return "ex:Primitive"
    return "ex:Concept"


def extract_internal_links(text: str) -> list[tuple[str, str]]:
    """提取正文中的内部 markdown 链接 (display_text, target_path)。"""
    # Skip metadata block: take everything after first '---' or first '#'
    body = text
    if "---" in body:
        parts = body.split("---", 2)
        if len(parts) >= 3:
            body = parts[2]
    links = []
    for title, target in re.findall(r"\[([^\]]+)\]\(([^)]+)\)", body):
        target = target.strip()
        if target.startswith("http") or target.startswith("#"):
            continue
        if target.endswith(".md"):
            links.append((title.strip(), target))
    return links


def resolve_target(path: str, target: str) -> str | None:
    """将相对 markdown 链接解析为 concept/ 内的相对路径。"""
    if target.startswith("/"):
        rel = target.lstrip("/")
    else:
        base = (CONCEPT_DIR / path).parent
        try:
            rel = (base / target).resolve().relative_to(CONCEPT_DIR.resolve()).as_posix()
        except Exception:
            return None
    if not rel.endswith(".md"):
        rel += ".md"
    return rel


def load_kg_index() -> dict:
    return json.loads(KG_INDEX_PATH.read_text(encoding="utf-8"))


def load_v3_template() -> dict:
    return json.loads(KG_V3_TEMPLATE_PATH.read_text(encoding="utf-8"))


def build_entities(index: dict) -> tuple[list[dict], dict[str, str]]:
    """构建 JSON-LD 实体列表，并返回 path -> @id 映射。"""
    entities: list[dict] = []
    path_to_iri: dict[str, str] = {}

    for ent in index["entities"]:
        path: str = ent["path"]
        title: str = ent.get("title", "")
        en: str = ent.get("en", "")
        summary: str = ent.get("summary", "") or ""
        bloom: str | None = ent.get("bloom")
        version: str | None = ent.get("rust_version")
        theorems: list[str] = ent.get("theorems", [])
        crates: list[str] = ent.get("related_crates", [])

        iri = concept_iri(en or title, path)
        # Handle potential collisions by appending a path-derived suffix.
        # For README files the stem is not unique, so use the parent directory name.
        existing_ids = {e["@id"] for e in entities}
        if iri in existing_ids:
            suffix = re.sub(r"[^A-Za-z0-9]", "", Path(path).parent.name)[:12]
            if not suffix:
                suffix = re.sub(r"[^A-Za-z0-9]", "", Path(path).stem)[:12]
            candidate = f"{iri}_{suffix}"
            counter = 1
            while candidate in existing_ids:
                candidate = f"{iri}_{suffix}_{counter}"
                counter += 1
            iri = candidate

        path_to_iri[path] = iri

        node: dict = {
            "@id": iri,
            "@type": map_bloom_to_class(bloom, path),
            "skos:prefLabel": [
                {"@value": title, "@language": "zh"},
            ],
            "skos:scopeNote": [
                {"@value": summary, "@language": "en" if re.search(r"[a-zA-Z]", summary) else "zh"},
            ],
            "ex:path": path,
        }
        if en:
            node["skos:prefLabel"].insert(0, {"@value": en, "@language": "en"})
        if bloom:
            node["ex:bloomLevel"] = bloom
        if version:
            node["ex:rustVersion"] = version
        if theorems:
            node["ex:theoremIds"] = theorems
        if crates:
            node["ex:relatedCrates"] = crates

        entities.append(node)

    return entities, path_to_iri


def build_relations(index: dict, path_to_iri: dict[str, str]) -> list[dict]:
    """从 kg_index 的 prerequisites/postrequisites 及正文内部链接构建关系三元组。"""
    relations: list[dict] = []
    rel_counter = 0

    def add_rel(subject_iri: str, predicate: str, object_iri: str, source: str) -> None:
        nonlocal rel_counter
        rel_counter += 1
        relations.append(
            {
                "@id": f"_:rel{rel_counter}",
                "@type": "ex:RelationAnnotation",
                "ex:subject": subject_iri,
                "ex:predicate": predicate,
                "ex:object": object_iri,
                "ex:source": source,
                "ex:confidence": 1.0,
                "ex:version": "1.97.0",
                "ex:reviewed": False,
                "dcterms:created": "2026-07-11",
            }
        )

    for ent in index["entities"]:
        subject_path: str = ent["path"]
        subject_iri = path_to_iri.get(subject_path)
        if not subject_iri:
            continue

        for pre in ent.get("prerequisites", []):
            target = pre.get("path", "")
            resolved = resolve_target(subject_path, target)
            if resolved and resolved in path_to_iri:
                add_rel(subject_iri, "ex:dependsOn", path_to_iri[resolved], f"prerequisite:{target}")

        for post in ent.get("postrequisites", []):
            target = post.get("path", "")
            resolved = resolve_target(subject_path, target)
            if resolved and resolved in path_to_iri:
                add_rel(subject_iri, "ex:entails", path_to_iri[resolved], f"postrequisite:{target}")

    # Also scan body internal links for broader relations
    for ent in index["entities"]:
        subject_path: str = ent["path"]
        subject_iri = path_to_iri.get(subject_path)
        if not subject_iri:
            continue
        full_path = CONCEPT_DIR / subject_path
        if not full_path.exists():
            continue
        text = full_path.read_text(encoding="utf-8")
        seen_targets = set()
        for _, target in extract_internal_links(text):
            resolved = resolve_target(subject_path, target)
            if resolved and resolved != subject_path and resolved in path_to_iri:
                if resolved in seen_targets:
                    continue
                seen_targets.add(resolved)
                add_rel(subject_iri, "ex:relatedTo", path_to_iri[resolved], f"body-link:{target}")

    return relations


def main() -> int:
    if not KG_INDEX_PATH.exists():
        print(f"ERROR: {KG_INDEX_PATH} not found. Run scripts/generate_kg_index.py first.", file=sys.stderr)
        return 1

    index = load_kg_index()
    template = load_v3_template()

    entities, path_to_iri = build_entities(index)
    relations = build_relations(index, path_to_iri)

    # Update metadata
    # Ensure ex:relatedTo property is declared when body links are present.
    properties = template.setdefault("properties", [])
    if not any(p.get("@id") == "ex:relatedTo" for p in properties):
        properties.append(
            {
                "@id": "ex:relatedTo",
                "@type": ["rdf:Property", "owl:ObjectProperty"],
                "rdfs:domain": "ex:Concept",
                "rdfs:range": "ex:Concept",
                "skos:prefLabel": [
                    {"@value": "related to", "@language": "en"},
                    {"@value": "相关于", "@language": "zh"},
                ],
            }
        )

    template["metadata"] = {
        "version": "3.1",
        "generated": "2026-07-11",
        "rust_version": "1.97.0+",
        "source": "kg_data_v3.json + kg_index.json",
        "previous_version": "3.0",
        "alignment": "RDF 1.2 / RDF-star / SKOS / JSON-LD 1.1 / SHACL",
        "entity_count": len(entities),
        "relation_count": len(relations),
    }

    template["entities"] = entities
    template["relations"] = relations

    # Keep classes/properties/decision_trees/fault_trees from template
    KG_V3_OUTPUT_PATH.write_text(json.dumps(template, ensure_ascii=False, indent=2), encoding="utf-8")
    print(
        f"Generated KG v3 with {len(entities)} entities and {len(relations)} relations: {KG_V3_OUTPUT_PATH}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
