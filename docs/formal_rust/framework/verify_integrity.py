#!/usr/bin/env python3
import sys
from pathlib import Path

BASE = Path(__file__).resolve().parent
ALLOWED = {
	"verification_index.md",
	"type_system_verification.md",
	"memory_safety_verification.md",
	"concurrency_safety_verification.md",
	"performance_formal_methods.md",
	"README.md",
	"verify_integrity.py",
	"proofs",
}
REQUIRED_HEADINGS = {
	"type_system_verification.md": ["最小可验证示例", "证明义务"],
	"memory_safety_verification.md": ["最小可验证示例", "证明义务"],
	"concurrency_safety_verification.md": ["最小可验证示例", "证明义务"],
	"performance_formal_methods.md": ["最小可验证示例", "证明义务"],
}


def check_proofs_dir() -> list[str]:
	violations: list[str] = []
	p = BASE / "proofs"
	if not p.exists():
		return violations
	# 允许的子结构
	coq = p / "coq"
	lean = p / "lean"
	for d in [coq, lean]:
		if not d.exists():
			violations.append(f"缺少证明子目录: {d.relative_to(BASE)}")
	readme = p / "README.md"
	if not readme.exists():
		violations.append("缺少 proofs/README.md")
	return violations


def find_violations():
	violations = []
	for p in BASE.iterdir():
		if p.name.startswith("."):
			continue
		if p.name not in ALLOWED:
			violations.append(f"非法文件或目录: {p.name}")
	# heading checks
	for fname, headings in REQUIRED_HEADINGS.items():
		f = BASE / fname
		if not f.exists():
			violations.append(f"缺失文档: {fname}")
			continue
		text = f.read_text(encoding="utf-8", errors="ignore")
		for h in headings:
			if h not in text:
				violations.append(f"文档缺少必要章节: {fname} -> {h}")
	violations.extend(check_proofs_dir())
	return violations


def main():
	violations = find_violations()
	if violations:
		print("验证失败:\n" + "\n".join(violations))
		sys.exit(1)
	print("验证通过: framework 目录完整且文档结构达标")

if __name__ == "__main__":
	main() 