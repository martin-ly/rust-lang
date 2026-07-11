#!/usr/bin/env python3
"""将 concept/ 中尚未在 SUMMARY.md 中链接的文件按层补齐。"""
from __future__ import annotations

import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "scripts"))
import concept_config as cc

SUMMARY_PATH = cc.CONCEPT_DIR / "SUMMARY.md"


def parse_summary_links(text: str) -> list[str]:
    links = []
    i = 0
    n = len(text)
    while i < n:
        if text[i] == "[" and (i == 0 or text[i - 1] != "\\"):
            depth = 1
            i += 1
            in_code = False
            code_delim = ""
            while i < n and depth > 0:
                if not in_code:
                    if text[i] == "\\" and i + 1 < n:
                        i += 2
                        continue
                    if text[i] == "`":
                        j = i
                        while j < n and text[j] == "`":
                            j += 1
                        code_delim = text[i:j]
                        in_code = True
                        i = j
                        continue
                    if text[i] == "[":
                        depth += 1
                    elif text[i] == "]":
                        depth -= 1
                else:
                    if text[i : i + len(code_delim)] == code_delim:
                        in_code = False
                        i += len(code_delim)
                        continue
                i += 1
            if depth == 0 and i < n and text[i] == "(":
                j = i + 1
                pdepth = 1
                while j < n and pdepth > 0:
                    if text[j] == "\\" and j + 1 < n:
                        j += 2
                        continue
                    if text[j] == "(":
                        pdepth += 1
                    elif text[j] == ")":
                        pdepth -= 1
                    j += 1
                links.append(text[i + 1 : j - 1].strip())
                i = j
                continue
        i += 1
    return links


def collect_unlinked() -> list[Path]:
    summary_text = SUMMARY_PATH.read_text(encoding="utf-8")
    linked = set(Path(p) for p in parse_summary_links(summary_text) if p.endswith(".md"))
    unlinked = []
    for p in cc.iter_concept_files():
        rel = p.relative_to(cc.CONCEPT_DIR)
        if rel.name == "SUMMARY.md":
            continue
        if any(part in {"placeholders"} for part in rel.parts):
            continue
        if rel.name in {"bilingual_template.md", "template_deduplication_guide.md", "audit_checklist.md"}:
            continue
        if rel.name == "README.md" and len(rel.parts) == 1:
            continue
        if rel not in linked:
            unlinked.append(rel)
    return sorted(unlinked)


def title_for(rel: Path) -> str:
    txt = (cc.CONCEPT_DIR / rel).read_text(encoding="utf-8")
    m = re.search(r"^#\s+(.+)$", txt, re.MULTILINE)
    if m:
        return m.group(1).strip()
    return rel.stem.replace("_", " ")


def layer_dir_for(rel: Path) -> str:
    return rel.parts[0]


def make_entry(title: str, path: str, indent: int = 2) -> str:
    return " " * indent + f"- [{title}]({path})"


def build_insertions(unlinked: list[Path]) -> dict[str, list[str]]:
    """按层构建要插入的 SUMMARY 条目列表。"""
    groups: dict[str, list[str]] = {d: [] for d in cc.LAYER_DIRS}

    # L0 元信息：模板、TLO、知识拓扑图谱、学习路径
    l0 = [r for r in unlinked if r.parts[0] == "00_meta"]
    if l0:
        entries = []
        # 模板与权威对齐
        for rel in l0:
            if rel.name == "bilingual_template_v2.md":
                entries.append(make_entry(title_for(rel), rel.as_posix()))
        for rel in l0:
            if rel.name == "kg_tlo_alignment.md":
                entries.append(make_entry(title_for(rel), rel.as_posix()))
        for rel in l0:
            if rel.name == "topic_authority_alignment_map.md":
                entries.append(make_entry(title_for(rel), rel.as_posix()))
        # 知识拓扑图谱集
        topo = [r for r in l0 if "knowledge_topology" in r.parts]
        if topo:
            readme = next((r for r in topo if r.name == "README.md"), None)
            if readme:
                entries.append(make_entry(title_for(readme), readme.as_posix()))
                for r in topo:
                    if r.name != "README.md":
                        entries.append(make_entry(title_for(r), r.as_posix(), indent=4))
            else:
                for r in topo:
                    entries.append(make_entry(title_for(r), r.as_posix()))
        for rel in l0:
            if rel.name == "learning_mvp_path_en.md":
                entries.append(make_entry(title_for(rel), rel.as_posix()))
        groups["00_meta"] = entries

    # L1 基础概念：按文件名排序追加
    l1 = [r for r in unlinked if r.parts[0] == "01_foundation"]
    if l1:
        groups["01_foundation"] = [make_entry(title_for(r), r.as_posix()) for r in sorted(l1)]

    # L2 进阶概念
    l2 = [r for r in unlinked if r.parts[0] == "02_intermediate"]
    if l2:
        groups["02_intermediate"] = [make_entry(title_for(r), r.as_posix()) for r in sorted(l2)]

    # L3 高级概念
    l3 = [r for r in unlinked if r.parts[0] == "03_advanced"]
    if l3:
        groups["03_advanced"] = [make_entry(title_for(r), r.as_posix()) for r in sorted(l3)]

    # L4 形式化理论：Reference 系列
    l4 = [r for r in unlinked if r.parts[0] == "04_formal"]
    if l4:
        groups["04_formal"] = [make_entry(title_for(r), r.as_posix()) for r in sorted(l4)]

    # L6 生态工程：直接作为子节点追加，避免重复链接已有文件
    l6 = [r for r in unlinked if r.parts[0] == "06_ecosystem"]
    if l6:
        groups["06_ecosystem"] = [make_entry(title_for(r), r.as_posix()) for r in sorted(l6)]

    # L7 前沿趋势
    l7 = [r for r in unlinked if r.parts[0] == "07_future"]
    if l7:
        groups["07_future"] = [make_entry(title_for(r), r.as_posix()) for r in sorted(l7)]

    return groups


def insert_into_summary(insertions: dict[str, list[str]]) -> None:
    lines = SUMMARY_PATH.read_text(encoding="utf-8").splitlines()

    # 修复 cargo_script 链接文本
    for idx, line in enumerate(lines):
        if "[[derive(Parser)]]" in line:
            lines[idx] = line.replace("[[derive(Parser)]]", "[derive(Parser)]")

    # 定位各层主标题行索引
    layer_header_indices: dict[str, int] = {}
    for idx, line in enumerate(lines):
        for layer_dir in cc.LAYER_DIRS:
            if line.startswith(f"- [L{cc.LAYER_DIRS[layer_dir][1]} ") and f"]({layer_dir}/README.md)" in line:
                layer_header_indices[layer_dir] = idx

    # 计算每层插入位置：下一层标题的前一行，或文件末尾
    layer_order = ["00_meta", "01_foundation", "02_intermediate", "03_advanced",
                   "04_formal", "05_comparative", "06_ecosystem", "07_future"]
    insert_positions: dict[str, int] = {}
    for i, layer in enumerate(layer_order):
        if layer not in layer_header_indices:
            continue
        if i + 1 < len(layer_order):
            next_layer = layer_order[i + 1]
            if next_layer in layer_header_indices:
                insert_positions[layer] = layer_header_indices[next_layer]
            else:
                insert_positions[layer] = len(lines)
        else:
            insert_positions[layer] = len(lines)

    # 从后往前插入，避免索引偏移
    for layer in reversed(layer_order):
        entries = insertions.get(layer, [])
        if not entries:
            continue
        pos = insert_positions[layer]
        # 如果插入位置前一行非空，加一空行以分隔
        if pos > 0 and lines[pos - 1].strip():
            entries = [""] + entries
        lines[pos:pos] = entries

    SUMMARY_PATH.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    unlinked = collect_unlinked()
    if not unlinked:
        print("✅ 无需补充，SUMMARY 已完整")
        return 0
    print(f"发现 {len(unlinked)} 个未链接文件，准备补齐...")
    insertions = build_insertions(unlinked)
    insert_into_summary(insertions)
    print("✅ SUMMARY.md 已更新")
    return 0


if __name__ == "__main__":
    sys.exit(main())
