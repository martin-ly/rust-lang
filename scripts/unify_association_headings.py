#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""P3-3 关联区块标题统一 + 核心页上层/下层概念补全。

模式 1（默认）标题统一（仅改标题行，不动链接内容）：
    「相关概念文件」「关联概念」 → 「相关概念」
    保留标题层级（##/###）与编号前缀（如「七、」「10.」）。
    标题行含额外内容的（如行内链接）不改。

模式 2（--enrich-core）核心 30 页补全：
    对 L1-L3 旗舰页，若其「相关概念」区块缺少
    `- **上层概念**: ...` / `- **下层概念**: ...`，
    则从文件元数据的 前置概念/前置依赖、后置概念/后置延伸 行提取链接补全。
    无「相关概念」区块的页面新建一个（插入到尾部参考区块之前，否则追加到文末）。

用法：
    python scripts/unify_association_headings.py                 # dry-run 标题统一
    python scripts/unify_association_headings.py --apply         # 应用标题统一
    python scripts/unify_association_headings.py --enrich-core   # dry-run 核心页补全
    python scripts/unify_association_headings.py --enrich-core --apply
"""
from __future__ import annotations

import argparse
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CONCEPT = os.path.join(ROOT, "concept")

# 标题行：层级 + 可选编号前缀 + 变体关键词 + 行尾（不允许行内额外内容）
HEADING_RE = re.compile(
    r"^(#{1,6}\s+)((?:\d+|[一二三四五六七八九十]+)[、.．]\s*)?(相关概念文件|关联概念)\s*$"
)

LINK_RE = re.compile(r"\[[^\]]+\]\([^)]+\)")

CORE_PAGES = [
    "01_foundation/01_ownership_borrow_lifetime/01_ownership.md",
    "01_foundation/01_ownership_borrow_lifetime/02_borrowing.md",
    "01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md",
    "01_foundation/01_ownership_borrow_lifetime/23_move_semantics.md",
    "01_foundation/01_ownership_borrow_lifetime/30_lifetimes_advanced.md",
    "01_foundation/02_type_system/04_type_system.md",
    "01_foundation/03_values_and_references/05_reference_semantics.md",
    "01_foundation/04_control_flow/07_control_flow.md",
    "01_foundation/04_control_flow/40_patterns.md",
    "01_foundation/04_control_flow/41_statements_and_expressions.md",
    "01_foundation/05_collections/08_collections.md",
    "01_foundation/07_modules_and_items/11_modules_and_paths.md",
    "01_foundation/08_error_handling/32_error_handling_basics.md",
    "01_foundation/09_macros_basics/12_attributes_and_macros.md",
    "02_intermediate/00_traits/01_traits.md",
    "02_intermediate/01_generics/02_generics.md",
    "02_intermediate/02_memory_management/03_memory_management.md",
    "02_intermediate/02_memory_management/12_smart_pointers.md",
    "02_intermediate/02_memory_management/08_interior_mutability.md",
    "02_intermediate/03_error_handling/04_error_handling.md",
    "02_intermediate/05_modules_and_visibility/10_module_system.md",
    "02_intermediate/06_macros_and_metaprogramming/17_macro_patterns.md",
    "02_intermediate/07_iterators_and_closures/15_iterator_patterns.md",
    "02_intermediate/00_traits/19_advanced_traits.md",
    "02_intermediate/01_generics/32_const_generics.md",
    "03_advanced/00_concurrency/01_concurrency.md",
    "03_advanced/01_async/02_async.md",
    "03_advanced/02_unsafe/03_unsafe.md",
    "03_advanced/03_proc_macros/04_macros.md",
    "03_advanced/00_concurrency/11_atomics_and_memory_ordering.md",
]

# 关联区块标题（用于定位插入点）：标题文本（去编号前缀后）属于关联区块家族
ASSOC_HEADING_RE = re.compile(
    r"^(#{1,6})\s+(?:(?:\d+|[一二三四五六七八九十]+)[、.．]\s*)?"
    r"(相关概念|相关概念文件|关联概念|相关概念链接)\s*$"
)

# 新建区块时的插入位置：尾部参考/来源类区块之前
TAIL_SECTION_RE = re.compile(
    r"^##\s+(?:[一二三四五六七八九十]+、)?"
    r"(?:国际权威参考|参考来源|参考|来源与延伸阅读|附录|📚)",
)


def iter_concept_md():
    for root, dirs, files in os.walk(CONCEPT):
        dirs[:] = [d for d in dirs if d != "archive"]
        for f in files:
            if f.endswith(".md"):
                yield os.path.join(root, f)


def unify_headings(apply: bool) -> int:
    n_files = n_heads = 0
    for path in iter_concept_md():
        text = open(path, encoding="utf-8").read()
        out, cnt = [], 0
        for line in text.splitlines(keepends=True):
            m = HEADING_RE.match(line.rstrip("\n"))
            if m:
                line = line.replace(m.group(3), "相关概念", 1)
                cnt += 1
            out.append(line)
        if cnt:
            n_files += 1
            n_heads += cnt
            rel = os.path.relpath(path, ROOT)
            print(f"  [{cnt}] {rel}")
            if apply:
                open(path, "w", encoding="utf-8").write("".join(out))
    print(f"标题统一: {n_heads} 处 / {n_files} 文件 ({'已应用' if apply else 'dry-run'})")
    return n_heads


def extract_meta_links(text: str, keys: tuple[str, ...]) -> list[str]:
    """从元数据行 `> **key**: ...` 提取 markdown 链接，去重保序。"""
    links: list[str] = []
    for line in text.splitlines():
        m = re.match(r"^>\s*\*\*(.+?)\*\*\s*[:：]\s*(.*)$", line)
        if not m:
            continue
        if m.group(1).strip() not in keys:
            continue
        for ln in LINK_RE.findall(m.group(2)):
            if ln not in links:
                links.append(ln)
    return links


def meta_field_text(text: str, keys: tuple[str, ...]) -> str:
    for line in text.splitlines():
        m = re.match(r"^>\s*\*\*(.+?)\*\*\s*[:：]\s*(.*)$", line)
        if m and m.group(1).strip() in keys:
            return m.group(2)
    return ""


def enrich_core(apply: bool) -> int:
    changed = 0
    for rel in CORE_PAGES:
        path = os.path.join(CONCEPT, rel)
        if not os.path.exists(path):
            print(f"!! 缺失: {rel}")
            continue
        text = open(path, encoding="utf-8").read()
        if "**上层概念**" in text and "**下层概念**" in text:
            continue

        pre_links = extract_meta_links(text, ("前置概念", "前置依赖"))
        post_links = extract_meta_links(text, ("后置概念", "后置延伸"))

        bullets: list[str] = []
        if "**上层概念**" not in text:
            if pre_links:
                bullets.append("- **上层概念**: " + " · ".join(pre_links))
            else:
                pre_txt = meta_field_text(text, ("前置概念", "前置依赖"))
                if "无" in pre_txt or not pre_txt:
                    bullets.append("- **上层概念**: 无（入口概念，无前置依赖）")
        if "**下层概念**" not in text:
            if post_links:
                bullets.append("- **下层概念**: " + " · ".join(post_links))
        if not bullets:
            print(f"  -- {rel}: 无可补全数据")
            continue

        lines = text.splitlines(keepends=True)
        block = "\n".join(bullets) + "\n\n"

        # 找关联区块标题，插入其下
        insert_at = None
        for i, line in enumerate(lines):
            if ASSOC_HEADING_RE.match(line.rstrip("\n")):
                insert_at = i + 1
                break

        if insert_at is None:
            # 新建区块：插入到尾部参考区块之前，否则追加文末
            new_section = "## 相关概念\n\n" + block
            placed = False
            for i, line in enumerate(lines):
                if TAIL_SECTION_RE.match(line):
                    lines.insert(i, "\n" + new_section + "\n")
                    placed = True
                    break
            if not placed:
                if lines and not lines[-1].endswith("\n"):
                    lines[-1] += "\n"
                lines.append("\n" + new_section)
        else:
            lines.insert(insert_at, block)

        new_text = "".join(lines)
        print(f"  + {rel}: 补全 {len(bullets)} 项"
              f"（{'新建区块' if insert_at is None else '插入现有区块'}）")
        if apply:
            open(path, "w", encoding="utf-8").write(new_text)
        changed += 1
    print(f"核心页补全: {changed} 文件 ({'已应用' if apply else 'dry-run'})")
    return changed


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--apply", action="store_true", help="实际写入（默认 dry-run）")
    ap.add_argument("--enrich-core", action="store_true", help="核心 30 页上层/下层概念补全")
    args = ap.parse_args()

    if args.enrich_core:
        enrich_core(args.apply)
    else:
        unify_headings(args.apply)


if __name__ == "__main__":
    sys.exit(main())
