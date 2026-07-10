#!/usr/bin/env python3
"""
为 KG 浏览器生成实体 -> Markdown 链接映射。

读取 concept/00_meta/kg_data_v3.json，直接利用每个实体的 `ex:path` 字段
生成 tools/kg_browser/kg_links.json。
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent.parent
KG_PATH = ROOT / "concept" / "00_meta" / "kg_data_v3.json"
OUT_PATH = ROOT / "tools" / "kg_browser" / "kg_links.json"


def main() -> int:
    with open(KG_PATH, "r", encoding="utf-8") as f:
        kg: dict[str, Any] = json.load(f)

    links: dict[str, str | None] = {}
    for entity in kg.get("entities", []):
        eid = entity.get("@id")
        path = entity.get("ex:path")
        if not eid:
            continue
        if path:
            links[eid] = f"concept/{path}"
        else:
            links[eid] = None

    with open(OUT_PATH, "w", encoding="utf-8") as f:
        json.dump(links, f, ensure_ascii=False, indent=2)

    print(f"Generated {len(links)} entity links: {OUT_PATH}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
