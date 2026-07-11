#!/usr/bin/env python3
"""
为包含 async-std / wasm32-wasi 旧引用的归档/报告/研究文档
批量添加「历史文档」警告头，避免学习者误将旧信息当作当前推荐。

用法：
    python scripts/maintenance/bulk_archive_warning.py [--dry-run]
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

# 被视为历史/归档目录的路径片段
ARCHIVE_SEGMENTS = {
    "archive",
    "reports",
    # ".kimi" 是当前执行计划，不属于需标注的历史文档
    "rust-ownership-decidability",
    "research_notes",
}

# 不需要添加警告头的文件（自身就是治理文档或当前计划）
EXCLUDED_FILES = {
    "ARCHIVED_ECOSYSTEM_REFERENCES_CLEANUP_PLAN_2026_06_19.md",
}

# 匹配旧引用
PATTERNS = [
    re.compile(r"async-std|async_std", re.IGNORECASE),
    re.compile(r"wasm32-wasi(?!p1|p2)", re.IGNORECASE),
]

WARNING_TEMPLATE = """\
> **⚠️ 历史文档提示**：本文档包含 `async-std`、`wasm32-wasi` 等已归档或已重命名的生态引用。
> 其中技术观点反映了对应时间点的社区状态，可能与当前（Rust 1.96+）推荐实践不一致。
> 学习时请以 `concept/`、`knowledge/` 及官方文档为准。
>
> - `async-std` 已进入维护模式，新项目建议优先考虑 Tokio / smol。
> - `wasm32-wasi` 已重命名为 `wasm32-wasip1`；WASI Preview 2 目标为 `wasm32-wasip2`。

---

"""


def is_archive(path: Path) -> bool:
    parts = set(path.parts)
    return any(seg in parts for seg in ARCHIVE_SEGMENTS)


def has_old_refs(text: str) -> bool:
    return any(p.search(text) for p in PATTERNS)


def already_has_warning(text: str) -> bool:
    return "历史文档提示" in text[:500]


def collect_targets() -> list[Path]:
    targets: list[Path] = []
    for md in ROOT.rglob("*.md"):
        # 跳过 node_modules / target 等无关目录
        if any(part in {"target", "node_modules", ".git"} for part in md.parts):
            continue
        if not is_archive(md):
            continue
        if md.name in EXCLUDED_FILES:
            continue
        try:
            text = md.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        if has_old_refs(text) and not already_has_warning(text):
            targets.append(md)
    return sorted(targets)


def main() -> int:
    parser = argparse.ArgumentParser(description="Add historical warning headers to archived docs")
    parser.add_argument("--dry-run", action="store_true", help="只打印，不写入")
    args = parser.parse_args()

    targets = collect_targets()
    print(f"找到 {len(targets)} 个需要添加警告头的归档/报告文档")

    for path in targets:
        rel = path.relative_to(ROOT)
        print(f"  {'[预览]' if args.dry_run else '[写入]'} {rel}")
        if args.dry_run:
            continue
        text = path.read_text(encoding="utf-8")
        # 如果文件以 YAML frontmatter 开头（---...---），在 frontmatter 后插入
        if text.startswith("---\n"):
            end = text.find("\n---\n", 4)
            if end != -1:
                insert_pos = end + 5
                new_text = text[:insert_pos] + "\n" + WARNING_TEMPLATE + text[insert_pos:]
            else:
                new_text = WARNING_TEMPLATE + text
        else:
            new_text = WARNING_TEMPLATE + text
        path.write_text(new_text, encoding="utf-8")

    return 0


if __name__ == "__main__":
    sys.exit(main())
