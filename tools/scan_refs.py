#!/usr/bin/env python3
import sys
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PATTERN = re.compile(r"rust_19[0-9]_", re.IGNORECASE)

hits = []
for p in ROOT.rglob("*.md"):
	# 忽略备份目录
	if any(part == "migration-backup" for part in p.parts):
		continue
	try:
		text = p.read_text(encoding="utf-8", errors="ignore")
	except Exception:
		continue
	for i, line in enumerate(text.splitlines(), 1):
		if PATTERN.search(line):
			hits.append(f"{p}:{i}: {line.strip()[:160]}")

if hits:
	print("Found references to >1.89 docs:")
	print("\n".join(hits))
	sys.exit(1)
else:
	print("No >1.89 references found.") 