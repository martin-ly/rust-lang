#!/usr/bin/env python3
"""Fix chapter numbering collision introduced by the new Unsafe/FFI 2024 section."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FILE = ROOT / "concept" / "03_advanced" / "03_unsafe.md"

text = FILE.read_text(encoding="utf-8")

# Fix duplicate 九 headings in TOC
old_toc = """  - [九、知识来源关系（Provenance）](#九知识来源关系provenance)
  - [十、待补充与演进方向（TODOs）](#十待补充与演进方向todos)"""
new_toc = """  - [十、知识来源关系（Provenance）](#十知识来源关系provenance)
  - [十一、待补充与演进方向（TODOs）](#十一待补充与演进方向todos)"""
assert old_toc in text
text = text.replace(old_toc, new_toc)

# Fix body headings
old_body = """## 九、知识来源关系（Provenance）"""
new_body = """## 十、知识来源关系（Provenance）"""
assert old_body in text
text = text.replace(old_body, new_body)

old_body2 = """## 十、待补充与演进方向（TODOs）"""
new_body2 = """## 十一、待补充与演进方向（TODOs）"""
assert old_body2 in text
text = text.replace(old_body2, new_body2)

# Fix typo: extra closing bracket
old_typo = "#[unsafe(...)]]"
new_typo = "#[unsafe(...)]"
text = text.replace(old_typo, new_typo)

FILE.write_text(text, encoding="utf-8")
print(f"Fixed numbering in {FILE.relative_to(ROOT)}")
