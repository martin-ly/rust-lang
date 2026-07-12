#!/usr/bin/env python3
"""验证 tools/kg_browser/kg_links.json 的全部链接指向存在的 concept 文件。

用法：
    python tools/kg_browser/validate_links.py

退出码：0 = 全部链接有效（或仅 None）；1 = 存在失效链接。
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
LINKS_PATH = ROOT / "tools" / "kg_browser" / "kg_links.json"
KG_PATH = ROOT / "concept" / "00_meta" / "kg_data_v3.json"


def main() -> int:
    links = json.loads(LINKS_PATH.read_text(encoding="utf-8"))
    kg = json.loads(KG_PATH.read_text(encoding="utf-8"))
    entity_ids = {e["@id"] for e in kg.get("entities", [])}

    missing_ids = sorted(set(links) - entity_ids)
    stale = []  # link entries whose entity vanished from the KG
    broken = []  # link targets that do not exist on disk
    none_count = 0
    for eid, path in links.items():
        if eid not in entity_ids:
            stale.append(eid)
            continue
        if path is None:
            none_count += 1
            continue
        if not (ROOT / path).is_file():
            broken.append((eid, path))

    total = len(links)
    valid = total - len(stale) - len(broken) - none_count
    print(f"kg_links.json: {total} entries")
    print(f"  valid links   : {valid}")
    print(f"  None (no path): {none_count}")
    print(f"  stale entity  : {len(stale)}")
    print(f"  broken target : {len(broken)}")

    if missing_ids:
        print("stale entities:", missing_ids[:10])
    for eid, path in broken[:10]:
        print(f"broken: {eid} -> {path}")

    ok = not stale and not broken
    if not ok:
        print("RESULT: FAIL — regenerate with generate_links.py and/or fix KG ex:path fields")
        return 1
    print("RESULT: OK — all non-None links resolve to existing files")
    return 0


if __name__ == "__main__":
    sys.exit(main())
