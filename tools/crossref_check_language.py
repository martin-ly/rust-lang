#!/usr/bin/env python3
import sys
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "formal_rust" / "language"
LINK_RE = re.compile(r"\[[^\]]*\]\(([^)]+)\)")

def main() -> int:
    if not BASE.exists():
        print(f"language base not found: {BASE}")
        return 1

    errors = []

    for p in BASE.rglob("*.md"):
        # 忽略迁移/备份目录
        if any(part == "migration-backup" for part in p.parts):
            continue
        text = p.read_text(encoding="utf-8", errors="ignore")
        for i, line in enumerate(text.splitlines(), 1):
            for m in LINK_RE.finditer(line):
                href = m.group(1).strip()
                # 忽略外链和纯锚点
                if href.startswith(("http://", "https://", "#")):
                    continue
                # 去掉锚点部分
                rel, *_ = href.split('#', 1)
                if rel == "":
                    continue
                target = (p.parent / rel).resolve()
                if not target.exists():
                    errors.append(f"{p}:{i}: missing target: {href}")

    if errors:
        print("language crossref check failed:")
        print("\n".join(errors))
        return 1
    else:
        print("language crossref check passed.")
        return 0

if __name__ == "__main__":
    sys.exit(main())


