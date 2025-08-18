#!/usr/bin/env python3
import sys
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")

errors = []

CONTROLLED_DIRS = [
	"formal_rust/framework",
	"formal_rust/language/20_version_features_analysis",
	"theoretical-foundations/memory-models",
]

def iter_controlled_markdowns():
	for rel in CONTROLLED_DIRS:
		base = (ROOT / rel)
		if not base.exists():
			continue
		for p in base.rglob("*.md"):
			yield p

for p in iter_controlled_markdowns():
	# 忽略备份与外部区域
	if any(part == "migration-backup" for part in p.parts):
		continue
	text = p.read_text(encoding="utf-8", errors="ignore")
	for i, line in enumerate(text.splitlines(), 1):
		for m in LINK_RE.finditer(line):
			href = m.group(1).strip()
			# 忽略外链和锚点
			if href.startswith("http://") or href.startswith("https://") or href.startswith("#"):
				continue
			# 版本越界快速检查
			if re.search(r"rust_19[0-9]_", href, re.IGNORECASE):
				errors.append(f"{p}:{i}: link to >1.89 file: {href}")
				continue
			# 解析相对路径
			target = (p.parent / href).resolve()
			# 若是目录引用或带锚点的相对路径，先去掉锚点
			if "#" in str(target):
				target = Path(str(target).split('#', 1)[0])
			if not target.exists():
				errors.append(f"{p}:{i}: missing target: {href}")

if errors:
	print("Cross-reference check failed:")
	print("\n".join(errors))
	sys.exit(1)
else:
	print("Cross-reference check passed.") 