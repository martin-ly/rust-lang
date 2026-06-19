#!/usr/bin/env python3
"""
为活跃文档中的 async-std / wasm32-wasi 旧引用添加说明，并更新目标名。

处理规则：
- 在文件顶部（YAML frontmatter 之后）添加一段生态状态说明。
- 将正文中独立的 `wasm32-wasi` 替换为 `wasm32-wasip1`（保留旧名注释）。
- 不修改 `async-std` 在正文中的具体措辞（上下文差异大），通过顶部说明统一提示。

用法：
    python scripts/maintenance/bulk_active_ecosystem_update.py [--dry-run]
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

# 被视为归档/报告/研究的路径片段，跳过
ARCHIVE_SEGMENTS = {
    "archive",
    "reports",
    ".kimi",
    "rust-ownership-decidability",
    "research_notes",
}

# 不需要处理的文件
EXCLUDED_FILES = {
    "CHANGELOG.md",
    "ARCHIVED_ECOSYSTEM_REFERENCES_CLEANUP_PLAN_2026_06_19.md",
}

ASYNC_STD_RE = re.compile(r"async-std|async_std", re.IGNORECASE)
WASI_RE = re.compile(r"wasm32-wasi(?!p1|p2)", re.IGNORECASE)

NOTE_TEMPLATE = """\
> **生态状态提示**：本文档提及 `async-std` 与/或旧目标 `wasm32-wasi`。请注意：
> - `async-std` 项目已进入维护模式，2024 年后不再活跃开发；新项目建议优先评估 **Tokio** 或 **smol**。
> - `wasm32-wasi` 旧目标名已重命名为 **`wasm32-wasip1`**；WASI Preview 2 对应目标为 **`wasm32-wasip2`**。

---

"""


def is_active(path: Path) -> bool:
    parts = set(path.parts)
    return not any(seg in parts for seg in ARCHIVE_SEGMENTS)


def already_has_note(text: str) -> bool:
    return "生态状态提示" in text[:600]


def collect_targets() -> list[Path]:
    targets: list[Path] = []
    for md in ROOT.rglob("*.md"):
        if any(part in {"target", "node_modules", ".git"} for part in md.parts):
            continue
        if not is_active(md):
            continue
        if md.name in EXCLUDED_FILES:
            continue
        try:
            text = md.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        if (ASYNC_STD_RE.search(text) or WASI_RE.search(text)) and not already_has_note(text):
            targets.append(md)
    return sorted(targets)


def add_note(text: str) -> str:
    if text.startswith("---\n"):
        end = text.find("\n---\n", 4)
        if end != -1:
            insert_pos = end + 5
            return text[:insert_pos] + "\n" + NOTE_TEMPLATE + text[insert_pos:]
    return NOTE_TEMPLATE + text


def update_wasi(text: str) -> str:
    # 替换独立的 wasm32-wasi 为 wasm32-wasip1，并在第一次出现时追加旧名注释
    def repl(m, state=[False]):
        if not state[0]:
            state[0] = True
            return "`wasm32-wasip1` (旧名 `wasm32-wasi`)"
        return "`wasm32-wasip1`"

    # 仅替换未在反引号内或代码块内的简单出现；通过正则限定为常见上下文
    # 先处理带反引号的
    text = re.sub(r"`wasm32-wasi`", repl, text)
    # 再处理不带反引号的独立词
    text = re.sub(r"\bwasm32-wasi\b", "wasm32-wasip1", text)
    return text


def main() -> int:
    parser = argparse.ArgumentParser(description="Update active docs with async-std / wasm32-wasi notes")
    parser.add_argument("--dry-run", action="store_true", help="只打印，不写入")
    args = parser.parse_args()

    targets = collect_targets()
    print(f"找到 {len(targets)} 个需要更新的活跃文档")

    for path in targets:
        rel = path.relative_to(ROOT)
        text = path.read_text(encoding="utf-8")
        new_text = update_wasi(text)
        new_text = add_note(new_text)

        if args.dry_run:
            print(f"  [预览] {rel}")
            continue

        path.write_text(new_text, encoding="utf-8")
        print(f"  [写入] {rel}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
