#!/usr/bin/env python3
"""幂等回填 kg_data_v3.json 中缺失的 ex:bloomLevel（K1b）。

回填优先级（与 scripts/generate_kg_index.py 的 infer_bloom 保持一致）：
1. 概念文件显式声明 `**Bloom 层级**: X` → 使用 X；
2. 文件声明 `**层次定位**: Lx ...` → 使用首个 Lx；
3. 按目录层级推断：00_meta→Meta、01_foundation→L1-L2、02_intermediate→L2-L4、
   03_advanced→L3-L5、04_formal→L4-L7、05_comparative→L5、06_ecosystem→L6、
   07_future→L7。

同时同步补齐 concept/00_meta/kg_index.json 中对应条目的 bloom 字段，
保持两个 KG 产物一致。已有 bloomLevel 的实体不会被修改（幂等）。

用法:
    python scripts/fixes/backfill_kg_bloom_level.py [--dry-run]
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CONCEPT_DIR = ROOT / "concept"
KG_V3_PATH = CONCEPT_DIR / "00_meta" / "kg_data_v3.json"
KG_INDEX_PATH = CONCEPT_DIR / "00_meta" / "kg_index.json"

BLOOM_RE = re.compile(r"^\s*>\s*\*\*Bloom 层级\*\*:\s*(.+)$", re.MULTILINE)
LAYER_LOC_RE = re.compile(r"^\s*>\s*\*\*层次定位\*\*:\s*(L\d)", re.MULTILINE)

DIR_BLOOM_FALLBACK = {
    "00_meta": "Meta",
    "01_foundation": "L1-L2",
    "02_intermediate": "L2-L4",
    "03_advanced": "L3-L5",
    "04_formal": "L4-L7",
    "05_comparative": "L5",
    "06_ecosystem": "L6",
    "07_future": "L7",
}


def infer_bloom_for_path(rel_path: str) -> tuple[str | None, str]:
    """返回 (bloomLevel, 来源说明)。"""
    md_path = CONCEPT_DIR / rel_path
    if md_path.exists():
        text = md_path.read_text(encoding="utf-8", errors="replace")
        m = BLOOM_RE.search(text)
        if m:
            return m.group(1).strip(), "file:Bloom层级"
        m = LAYER_LOC_RE.search(text)
        if m:
            return m.group(1).strip(), "file:层次定位"
    top = rel_path.split("/", 1)[0]
    if top in DIR_BLOOM_FALLBACK:
        return DIR_BLOOM_FALLBACK[top], f"dir:{top}"
    return None, "unresolved"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true")
    args = ap.parse_args()

    kg = json.loads(KG_V3_PATH.read_text(encoding="utf-8"))
    patched: list[tuple[str, str, str]] = []
    unresolved: list[str] = []

    for e in kg.get("entities", []):
        if e.get("ex:bloomLevel"):
            continue  # 幂等：已有不回填
        rel = e.get("ex:path", "")
        bloom, source = infer_bloom_for_path(rel)
        if bloom is None and e.get("ex:layer") == "L0":
            # concept/ 根下的导航/索引文件（README.md、SUMMARY.md、sources/*）
            bloom, source = "Meta", "layer:L0"
        if bloom is None:
            unresolved.append(e.get("@id", "?"))
            continue
        e["ex:bloomLevel"] = bloom
        patched.append((e.get("@id", "?"), bloom, source))

    print(f"kg_data_v3.json: 回填 {len(patched)} 个实体，未解析 {len(unresolved)} 个")
    for eid, bloom, source in patched:
        print(f"  {eid:55s} -> {bloom:8s} ({source})")
    for eid in unresolved:
        print(f"  ⚠ 未解析: {eid}")

    # 同步 kg_index.json 的 bloom 字段（仅补空，保持两产物一致）
    index_patched = 0
    if KG_INDEX_PATH.exists():
        index = json.loads(KG_INDEX_PATH.read_text(encoding="utf-8"))
        for ent in index.get("entities", []):
            if ent.get("bloom"):
                continue
            bloom, _source = infer_bloom_for_path(ent.get("path", ""))
            if bloom:
                ent["bloom"] = bloom
                index_patched += 1
        print(f"kg_index.json: 同步补齐 {index_patched} 个 bloom 字段")
        if not args.dry_run and index_patched:
            KG_INDEX_PATH.write_text(
                json.dumps(index, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
            )

    if not args.dry_run and patched:
        KG_V3_PATH.write_text(
            json.dumps(kg, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )
        print("已写回 kg_data_v3.json")
    elif args.dry_run:
        print("(dry-run，未写入)")

    return 1 if unresolved else 0


if __name__ == "__main__":
    raise SystemExit(main())
