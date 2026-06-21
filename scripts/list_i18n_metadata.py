#!/usr/bin/env python3
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"

en_re = re.compile(r'^>\s*\*\*EN\*\*:\s*(.*)$', re.MULTILINE)
sum_re = re.compile(r'^>\s*\*\*Summary\*\*:\s*(.*)$', re.MULTILINE)

rows = []
for p in sorted(ROOT.rglob("*.md")):
    text = p.read_text(encoding="utf-8")
    en = en_re.search(text)
    sm = sum_re.search(text)
    rows.append((p.relative_to(ROOT).as_posix(), en.group(1).strip() if en else "", sm.group(1).strip() if sm else ""))

for rel, en, sm in rows:
    print(f"{rel}\t{en}\t{sm}")
