#!/usr/bin/env python3
"""
为 KG 浏览器生成实体 -> Markdown 链接映射。

扫描 concept/ 目录下的 Markdown 文件，根据实体英文标签与文件名的
相似度进行匹配，输出 tools/kg_browser/kg_links.json。
"""
from __future__ import annotations

import json
import re
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent.parent
KG_PATH = ROOT / "concept" / "00_meta" / "kg_data_v2.json"
OUT_PATH = ROOT / "tools" / "kg_browser" / "kg_links.json"


def load_kg(path: Path) -> dict[str, Any]:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def iter_entities(kg: dict[str, Any]) -> list[dict[str, Any]]:
    entities: list[dict[str, Any]] = []
    for category, items in kg.get("entities", {}).items():
        for item in items:
            item["_category"] = category
            entities.append(item)
    return entities


def get_lang_value(values: list[dict[str, str]], lang: str) -> str | None:
    for v in values:
        if v.get("@language") == lang:
            return v.get("@value")
    return None


def normalise(text: str) -> str:
    return re.sub(r"[^a-z0-9]+", "", text.lower())


def main() -> int:
    kg = load_kg(KG_PATH)
    entities = iter_entities(kg)

    md_files = list((ROOT / "concept").rglob("*.md"))
    # Exclude meta and archive from primary matching to avoid noise.
    primary_files = [
        p for p in md_files
        if not any(part in ("00_meta", "archive", "sources") for part in p.parts)
    ]

    links: dict[str, str | None] = {}

    for entity in entities:
        eid = entity["@id"]
        label = get_lang_value(entity.get("skos:prefLabel", []), "en") or ""
        key = normalise(label)
        if not key:
            links[eid] = None
            continue

        best: Path | None = None
        best_score = 0

        candidates = primary_files
        # Fallback to all files if no primary candidate.
        for file in candidates:
            stem = normalise(file.stem)
            # Remove numeric prefix (e.g. 01_ownership -> ownership).
            stem_clean = re.sub(r"^\d+_", "", stem)

            if key == stem or key == stem_clean:
                score = 1000
            elif stem_clean.startswith(key) or stem.startswith(key):
                score = 100 + len(key)
            elif key in stem or key in stem_clean:
                # Avoid very short labels matching inside unrelated words.
                if len(key) >= 5:
                    score = 50 + len(key)
                else:
                    score = 0
            else:
                score = 0

            if score > best_score:
                best_score = score
                best = file

        if best and best_score >= 50:
            links[eid] = str(best.relative_to(ROOT).as_posix())
        else:
            links[eid] = None

    # Some manual overrides for concepts that don't match cleanly.
    overrides: dict[str, str] = {
        "ex:AXM": "concept/04_formal/11_separation_logic.md",
        "ex:Elision": "concept/01_foundation/03_lifetimes.md",
        "ex:OrphanRule": "concept/02_intermediate/01_traits.md",
        "ex:AsyncAwait": "concept/03_advanced/02_async.md",
        "ex:AffineLogic": "concept/04_formal/01_linear_logic.md",
        "ex:RegionTypes": "concept/04_formal/03_ownership_formal.md",
        "ex:SystemF": "concept/04_formal/02_type_theory.md",
    }
    for eid, path in overrides.items():
        if eid in links:
            links[eid] = path

    OUT_PATH.write_text(json.dumps(links, ensure_ascii=False, indent=2), encoding="utf-8")
    print(f"[generate_links] Wrote {len(links)} entity links to {OUT_PATH}")
    matched = sum(1 for v in links.values() if v)
    print(f"[generate_links] Matched {matched} / {len(links)} entities")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
