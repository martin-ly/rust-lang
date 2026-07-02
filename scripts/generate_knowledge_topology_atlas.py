#!/usr/bin/env python3
"""
Generate Knowledge Topology Atlas markdown files from tmp/concept_topology_raw.json.

Output: concept/00_meta/knowledge_topology/*.md
"""
from __future__ import annotations

import json
from collections import defaultdict
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
RAW_PATH = ROOT / "tmp" / "concept_topology_raw.json"
OUT_DIR = ROOT / "concept" / "00_meta" / "knowledge_topology"


def load_raw() -> dict[str, Any]:
    return json.loads(RAW_PATH.read_text(encoding="utf-8"))


def layer_label(layer: str) -> str:
    labels = {
        "L0": "L0 元信息层",
        "L1": "L1 基础概念层",
        "L2": "L2 进阶概念层",
        "L3": "L3 高级概念层",
        "L4": "L4 形式化理论层",
        "L5": "L5 对比分析层",
        "L6": "L6 生态工程层",
        "L7": "L7 前沿趋势层",
    }
    return labels.get(layer, layer)


def concept_link(c: dict[str, Any]) -> str:
    return f"[{c['zh_name']}](../../{c['path']})"


def escape_cell(text: str) -> str:
    return text.replace("|", "\\|").replace("\n", " ")


def header(title: str, en: str, summary: str) -> list[str]:
    return [
        f"# {title}",
        "",
        f"> **EN**: {en}",
        f"> **Summary**: {summary}",
        "> **受众**: [研究者]",
        "> **内容分级**: [元层]",
        "> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)",
        "",
        "---",
        "",
    ]


def footer() -> list[str]:
    return ["", "---", "", "> **内容分级**: [元层]"]


def write_readme(data: dict[str, Any]) -> None:
    total = data["metadata"]["total_files"]
    content = f"""# 知识体系拓扑图谱集（Knowledge Topology Atlas）

> **EN**: Knowledge Topology Atlas
> **Summary**: Rust 知识体系的全局拓扑视图：概念定义、属性关系、场景决策树、示例反例、逻辑推理、层间/层内映射、权威来源对齐。
>
> **受众**: [研究者]
> **内容分级**: [元层]
> **定位**: 本目录是 `concept/` 的元层索引，帮助学习者从多个维度（定义、属性、场景、推理、来源）快速定位和理解 Rust 概念。
>
> **来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [Rustonomicon](https://doc.rust-lang.org/nomicon/)

---

## 图谱集目录

| 文件 | 主题 | 覆盖范围 |
|:---|:---|:---|
| [01_concept_definition_atlas.md](01_concept_definition_atlas.md) | 概念定义图谱 | 全部 {total} 个核心概念的中英名称、层级、定义、同义/反义 |
| [02_attribute_relationship_atlas.md](02_attribute_relationship_atlas.md) | 属性关系图谱 | 概念属性矩阵与属性间约束 |
| [03_scenario_decision_tree_atlas.md](03_scenario_decision_tree_atlas.md) | 场景决策树图谱 | 开发场景 → 决策 → Rust 概念/工具 |
| [04_example_counterexample_atlas.md](04_example_counterexample_atlas.md) | 示例与反例图谱 | 按概念组织的示例、反例、边界示例 |
| [05_logical_reasoning_atlas.md](05_logical_reasoning_atlas.md) | 逻辑推理图谱 | 定理链、推理规则、形式化对应 |
| [06_inter_layer_mapping_atlas.md](06_inter_layer_mapping_atlas.md) | 层间映射图谱 | L0–L7 依赖、蕴含、反馈关系 |
| [07_intra_layer_mapping_atlas.md](07_intra_layer_mapping_atlas.md) | 层内映射图谱 | 每层内部模型/概念间关系 |
| [08_concept_source_alignment_atlas.md](08_concept_source_alignment_atlas.md) | 概念-权威来源对齐图谱 | 每个核心概念 ↔ 国际化权威来源 |
| [09_reasoning_judgment_tree_atlas.md](09_reasoning_judgment_tree_atlas.md) | 推理判定树图谱 | 编译错误/运行时问题 → 根因 → 修复策略 |
| [10_gap_and_action_plan.md](10_gap_and_action_plan.md) | 缺口与行动计划 | 当前缺口、优先级、修复任务 |

## 使用建议

1. **快速定位概念**：从 `01_concept_definition_atlas.md` 按层级或字母检索。
2. **理解概念关系**：查看 `06_inter_layer_mapping_atlas.md` 和 `07_intra_layer_mapping_atlas.md`。
3. **解决实际问题**：查看 `03_scenario_decision_tree_atlas.md` 和 `09_reasoning_judgment_tree_atlas.md`。
4. **验证权威来源**：查看 `08_concept_source_alignment_atlas.md`。

## 维护规则

- 本目录文件由 `scripts/generate_knowledge_topology_atlas.py` 从 `concept/**/*.md` 半自动生成。
- 人工策展内容以 `<!-- MANUAL -->` 标记。
- 当 `concept/` 文件更新后，应重新运行生成脚本并审阅变更。

---

> **权威来源**: [Rust Reference](https://doc.rust-lang.org/reference/) · [TRPL](https://doc.rust-lang.org/book/title-page.html)
> **内容分级**: [元层]
"""
    (OUT_DIR / "README.md").write_text(content, encoding="utf-8")


def write_concept_definition_atlas(concepts: list[dict[str, Any]]) -> None:
    lines = header(
        "概念定义图谱（Concept Definition Atlas）",
        "Concept Definition Atlas",
        "全部核心概念的中英名称、层级、一句话定义、权威来源、同义/近义/反义关系。",
    )

    lines.append("## 一、按层级索引")
    lines.append("")

    by_layer = defaultdict(list)
    for c in concepts:
        by_layer[c["layer"]].append(c)

    for layer in sorted(by_layer.keys()):
        label = layer_label(layer)
        lines.append(f"### {label}")
        lines.append("")
        lines.append("| 编号 | 中文名 | EN | 定义 | 来源数 |")
        lines.append("|:---|:---|:---|:---|:---:|")
        for c in sorted(by_layer[layer], key=lambda x: x["path"]):
            zh = escape_cell(c["zh_name"])
            en = escape_cell(c["en_name"])
            summary = escape_cell(c["summary"]) or "—"
            link = f"[{zh}](../../{c['path']})"
            lines.append(f"| `{c['id']}` | {link} | {en} | {summary} | {len(c['sources'])} |")
        lines.append("")

    # Concept cloud by A/S/P
    lines.append("## 二、按 A/S/P 维度分布")
    lines.append("")
    asp_groups = defaultdict(list)
    for c in concepts:
        asp = c["asp"] or "未标注"
        asp_groups[asp].append(c)

    lines.append("| A/S/P | 数量 | 代表概念 |")
    lines.append("|:---|:---:|:---|")
    for asp in sorted(asp_groups.keys()):
        samples = ", ".join(concept_link(c) for c in asp_groups[asp][:5])
        lines.append(f"| {asp} | {len(asp_groups[asp])} | {samples} |")
    lines.append("")

    # Top referenced concepts
    lines.append("## 三、核心枢纽概念（被引用最多）")
    lines.append("")
    ref_counts = defaultdict(int)
    id_to_concept = {c["id"]: c for c in concepts}
    for c in concepts:
        for p in c["postreqs"]:
            href = p.get("href", "")
            if href.endswith(".md"):
                target_id = Path(href).stem
                ref_counts[target_id] += 1
    top = sorted(ref_counts.items(), key=lambda x: -x[1])[:20]
    lines.append("| 概念 | 被引用次数 |")
    lines.append("|:---|:---:|")
    for tid, cnt in top:
        c = id_to_concept.get(tid)
        if c:
            lines.append(f"| [{c['zh_name']}](../../{c['path']}) | {cnt} |")
        else:
            lines.append(f"| `{tid}` | {cnt} |")
    lines.append("")

    lines.extend(footer())
    (OUT_DIR / "01_concept_definition_atlas.md").write_text("\n".join(lines), encoding="utf-8")


def write_attribute_relationship_atlas(concepts: list[dict[str, Any]]) -> None:
    lines = header(
        "属性关系图谱（Attribute Relationship Atlas）",
        "Attribute Relationship Atlas",
        "概念属性矩阵：每个核心概念的必备/可选属性、内容分级、A/S/P、Bloom 层级、定理链。",
    )

    lines.append("## 一、核心概念属性矩阵")
    lines.append("")
    lines.append("| 概念 | 层级 | 受众 | 分级 | A/S/P | Bloom | 定理链 |")
    lines.append("|:---|:---:|:---|:---|:---:|:---:|:---|")

    for c in sorted(concepts, key=lambda x: (x["layer"], x["path"])):
        name = f"[{escape_cell(c['zh_name'])}](../../{c['path']})"
        layer = layer_label(c["layer"])
        audience = escape_cell(c["audience"]) or "—"
        level = escape_cell(c["level"]) or "—"
        asp = c["asp"] or "—"
        bloom = escape_cell(c["bloom"]) or "—"
        theorem = escape_cell(c["theorem_chain"]) or "—"
        lines.append(f"| {name} | {layer} | {audience} | {level} | {asp} | {bloom} | {theorem} |")

    lines.append("")
    lines.append("## 二、属性分布统计")
    lines.append("")

    asp_counts = defaultdict(int)
    level_counts = defaultdict(int)
    bloom_counts = defaultdict(int)
    for c in concepts:
        asp_counts[c["asp"] or "未标注"] += 1
        level_counts[c["level"] or "未标注"] += 1
        bloom_counts[(c["bloom"] or "未标注").split("→")[0].strip()] += 1

    lines.append("### A/S/P 分布")
    lines.append("")
    lines.append("| A/S/P | 数量 |")
    lines.append("|:---|:---:|")
    for k, v in sorted(asp_counts.items(), key=lambda x: -x[1]):
        lines.append(f"| {k} | {v} |")
    lines.append("")

    lines.append("### 内容分级分布")
    lines.append("")
    lines.append("| 内容分级 | 数量 |")
    lines.append("|:---|:---:|")
    for k, v in sorted(level_counts.items(), key=lambda x: -x[1]):
        lines.append(f"| {k} | {v} |")
    lines.append("")

    lines.append("### Bloom 层级分布")
    lines.append("")
    lines.append("| Bloom | 数量 |")
    lines.append("|:---|:---:|")
    for k, v in sorted(bloom_counts.items(), key=lambda x: -x[1]):
        lines.append(f"| {k} | {v} |")
    lines.append("")

    lines.extend(footer())
    (OUT_DIR / "02_attribute_relationship_atlas.md").write_text("\n".join(lines), encoding="utf-8")


def write_inter_layer_mapping_atlas(concepts: list[dict[str, Any]]) -> None:
    lines = header(
        "层间映射图谱（Inter-Layer Mapping Atlas）",
        "Inter-Layer Mapping Atlas",
        "L0–L7 各层之间的依赖、蕴含、反馈关系，基于前置/后置概念引用统计。",
    )

    layers = [f"L{i}" for i in range(8)]
    matrix = {src: {dst: 0 for dst in layers} for src in layers}

    id_to_layer = {c["id"]: c["layer"] for c in concepts}
    for c in concepts:
        src_layer = c["layer"]
        for p in c["postreqs"]:
            href = p.get("href", "")
            if href.endswith(".md"):
                tid = Path(href).stem
                dst_layer = id_to_layer.get(tid)
                if dst_layer:
                    matrix[src_layer][dst_layer] += 1

    lines.append("## 一、层间引用矩阵（行 = 源层，列 = 目标层）")
    lines.append("")
    header_row = "| 源层 \\ 目标层 | " + " | ".join(layer_label(l) for l in layers) + " |"
    lines.append(header_row)
    lines.append("|" + "---|" * (len(layers) + 1))
    for src in layers:
        row = f"| {layer_label(src)} |"
        for dst in layers:
            row += f" {matrix[src][dst]} |"
        lines.append(row)
    lines.append("")

    lines.append("## 二、跨层关键桥接概念")
    lines.append("")
    lines.append("| 源层 | 概念 | 指向层 | 后置概念 |")
    lines.append("|:---|:---|:---|:---|")
    bridges = []
    for c in concepts:
        for p in c["postreqs"]:
            href = p.get("href", "")
            if href.endswith(".md"):
                tid = Path(href).stem
                dst = id_to_layer.get(tid)
                if dst and dst != c["layer"]:
                    src_label = layer_label(c["layer"])
                    dst_label = layer_label(dst)
                    bridges.append((c["layer"], c, dst_label, p["title"]))
    # Show a sample of important bridges (limit to avoid huge file)
    for _, c, dst_label, title in sorted(bridges, key=lambda x: x[0])[:60]:
        lines.append(f"| {layer_label(c['layer'])} | [{escape_cell(c['zh_name'])}](../../{c['path']}) | {dst_label} | {escape_cell(title)} |")
    lines.append("")

    lines.append("## 三、与现有元文件的关系")
    lines.append("")
    lines.append("- 更详细的层间依赖图见 [../inter_layer_map.md](../inter_layer_map.md)")
    lines.append("- 层内模型映射见 [../intra_layer_model_map.md](../intra_layer_model_map.md)")
    lines.append("- 形式化本体规范见 [../kg_ontology_v2.md](../kg_ontology_v2.md)")
    lines.append("")

    lines.extend(footer())
    (OUT_DIR / "06_inter_layer_mapping_atlas.md").write_text("\n".join(lines), encoding="utf-8")


def write_intra_layer_mapping_atlas(concepts: list[dict[str, Any]]) -> None:
    lines = header(
        "层内映射图谱（Intra-Layer Mapping Atlas）",
        "Intra-Layer Mapping Atlas",
        "每层内部核心模型/概念间的等价、蕴含、依赖、互斥关系，基于同层前置/后置引用。",
    )

    id_to_concept = {c["id"]: c for c in concepts}
    by_layer = defaultdict(list)
    for c in concepts:
        by_layer[c["layer"]].append(c)

    for layer in sorted(by_layer.keys()):
        label = layer_label(layer)
        layer_concepts = by_layer[layer]
        lines.append(f"## {label}")
        lines.append("")

        # Count intra-layer refs
        intra_refs = defaultdict(lambda: defaultdict(int))
        for c in layer_concepts:
            for p in c["postreqs"]:
                href = p.get("href", "")
                if href.endswith(".md"):
                    tid = Path(href).stem
                    target = id_to_concept.get(tid)
                    if target and target["layer"] == layer:
                        intra_refs[c["id"]][tid] += 1

        if not any(intra_refs.values()):
            lines.append("> 本层内部引用较少，主要作为独立主题存在。")
            lines.append("")
            continue

        lines.append("### 层内引用关系")
        lines.append("")
        lines.append("| 源概念 | 关系 | 目标概念 |")
        lines.append("|:---|:---:|:---|")
        for src_id, targets in sorted(intra_refs.items()):
            src = id_to_concept[src_id]
            for dst_id, cnt in sorted(targets.items(), key=lambda x: -x[1]):
                dst = id_to_concept[dst_id]
                lines.append(
                    f"| [{escape_cell(src['zh_name'])}](../../{src['path']}) | ⟹ | "
                    f"[{escape_cell(dst['zh_name'])}](../../{dst['path']}) |"
                )
        lines.append("")

    lines.extend(footer())
    (OUT_DIR / "07_intra_layer_mapping_atlas.md").write_text("\n".join(lines), encoding="utf-8")


def write_concept_source_alignment_atlas(concepts: list[dict[str, Any]]) -> None:
    lines = header(
        "概念-权威来源对齐图谱（Concept-Source Alignment Atlas）",
        "Concept-Source Alignment Atlas",
        "每个核心概念与国际化权威来源的对齐：Rust Reference、TRPL、RFCs、学术、课程、工业、标准。",
    )

    tier_names = {
        "L1_specification": "Rust Reference",
        "L1_trpl": "TRPL",
        "L1_rfc": "RFCs",
        "L1_rustonomicon": "Rustonomicon",
        "L1_cargo": "Cargo Book",
        "L1_std": "std docs",
        "L1_github": "Rust GitHub",
        "L1_blog": "Rust Blog",
        "L2_academic": "学术论文",
        "L3_course": "顶尖课程",
        "L4_industrial": "工业实践",
        "L5_standard": "国际标准",
        "L0_wikipedia": "Wikipedia",
        "Lx_other": "其他",
    }

    # Global tier stats
    tier_counts = defaultdict(int)
    for c in concepts:
        for tier, cnt in c["source_tiers"].items():
            tier_counts[tier] += cnt

    lines.append("## 一、权威来源覆盖统计")
    lines.append("")
    lines.append("| 来源层级 | 来源类型 | 引用次数 | 涉及概念数 |")
    lines.append("|:---|:---|:---:|:---:|")

    tier_concept_counts = defaultdict(int)
    for c in concepts:
        for tier in c["source_tiers"]:
            tier_concept_counts[tier] += 1

    for tier in sorted(tier_counts.keys(), key=lambda t: -tier_counts[t]):
        name = tier_names.get(tier, tier)
        lines.append(f"| {tier} | {name} | {tier_counts[tier]} | {tier_concept_counts[tier]} |")
    lines.append("")

    # Per-layer coverage
    lines.append("## 二、各层级权威来源覆盖度")
    lines.append("")
    by_layer = defaultdict(list)
    for c in concepts:
        by_layer[c["layer"]].append(c)

    lines.append("| 层级 | 概念数 | Rust Reference | TRPL | RFCs | 学术 | 课程 | 标准 |")
    lines.append("|:---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|")
    for layer in sorted(by_layer.keys()):
        cs = by_layer[layer]
        total = len(cs)
        ref = sum(1 for c in cs if "L1_specification" in c["source_tiers"])
        trpl = sum(1 for c in cs if "L1_trpl" in c["source_tiers"])
        rfc = sum(1 for c in cs if "L1_rfc" in c["source_tiers"])
        acad = sum(1 for c in cs if "L2_academic" in c["source_tiers"])
        course = sum(1 for c in cs if "L3_course" in c["source_tiers"])
        std = sum(1 for c in cs if "L5_standard" in c["source_tiers"])
        lines.append(f"| {layer_label(layer)} | {total} | {ref} | {trpl} | {rfc} | {acad} | {course} | {std} |")
    lines.append("")

    # Low-source concepts
    lines.append("## 三、缺少权威来源的概念（需补全）")
    lines.append("")
    lines.append("| 概念 | 层级 | 当前来源数 | 建议补全来源 |")
    lines.append("|:---|:---:|:---:|:---|")
    low_source = [c for c in concepts if len(c["sources"]) <= 2 and not c["path"].startswith("00_meta/")]
    for c in sorted(low_source, key=lambda x: (x["layer"], x["path"]))[:50]:
        suggestion = "Rust Reference / TRPL"
        if c["layer"] == "L4":
            suggestion = "Rust Reference + POPL/PLDI/RustBelt"
        elif c["layer"] in ("L6", "L7"):
            suggestion = "RFCs + 工业/标准来源"
        lines.append(
            f"| [{escape_cell(c['zh_name'])}](../../{c['path']}) | {layer_label(c['layer'])} | {len(c['sources'])} | {suggestion} |"
        )
    lines.append("")

    lines.extend(footer())
    (OUT_DIR / "08_concept_source_alignment_atlas.md").write_text("\n".join(lines), encoding="utf-8")


def write_gap_and_action_plan(concepts: list[dict[str, Any]]) -> None:
    lines = header(
        "缺口与行动计划（Gap and Action Plan）",
        "Gap and Action Plan",
        "基于拓扑抽取结果识别的当前缺口：来源覆盖、表征完整性、层间/层内映射、定义一致性。",
    )

    # Gaps
    no_sources = [c for c in concepts if not c["sources"] and not c["path"].startswith("00_meta/")]
    low_sources = [c for c in concepts if 1 <= len(c["sources"]) <= 2 and not c["path"].startswith("00_meta/")]
    no_theorem = [c for c in concepts if not c["theorem_chain"] and not c["path"].startswith("00_meta/")]
    no_asp = [c for c in concepts if not c["asp"] and not c["path"].startswith("00_meta/")]
    no_sections = [c for c in concepts if not any(c["sections"].values()) and not c["path"].startswith("00_meta/")]

    lines.append("## 一、当前缺口概览")
    lines.append("")
    lines.append("| 缺口类型 | 数量 | 说明 |")
    lines.append("|:---|:---:|:---|")
    lines.append(f"| 无权威来源标注 | {len(no_sources)} | 概念文件未引用任何外部权威来源 |")
    lines.append(f"| 来源标注薄弱（≤2） | {len(low_sources)} | 概念文件仅引用 1–2 个来源 |")
    lines.append(f"| 无定理链 | {len(no_theorem)} | 概念文件缺少定理链 |")
    lines.append(f"| 无 A/S/P 标记 | {len(no_asp)} | 概念文件缺少 A/S/P 维度标记 |")
    lines.append(f"| 无知识表征章节 | {len(no_sections)} | 概念文件无决策树/矩阵/示例等表征 |")
    lines.append("")

    lines.append("## 二、优先修复任务")
    lines.append("")
    lines.append("### P0：补全权威来源（L1–L4 核心概念）")
    lines.append("")
    lines.append("| 概念 | 层级 | 当前来源数 | 建议行动 |")
    lines.append("|:---|:---:|:---:|:---|")
    for c in sorted(low_sources, key=lambda x: (x["layer"], x["path"]))[:30]:
        lines.append(
            f"| [{escape_cell(c['zh_name'])}](../../{c['path']}) | {layer_label(c['layer'])} | {len(c['sources'])} | 补充 Rust Reference / TRPL / 学术来源 |"
        )
    lines.append("")

    lines.append("### P1：增强知识表征")
    lines.append("")
    lines.append("| 概念 | 层级 | 缺失表征 | 建议行动 |")
    lines.append("|:---|:---:|:---|:---|")
    for c in sorted(no_sections, key=lambda x: (x["layer"], x["path"]))[:30]:
        lines.append(
            f"| [{escape_cell(c['zh_name'])}](../../{c['path']}) | {layer_label(c['layer'])} | 决策树/矩阵/示例 | 补充属性矩阵或示例反例 |"
        )
    lines.append("")

    lines.append("### P2：对齐国际标准")
    lines.append("")
    lines.append("针对以下主题补充 Unicode / ISO / IEEE / IETF / ABI 标准引用：")
    lines.append("")
    lines.append("- 字符串与编码：`concept/01_foundation/18_strings_and_encoding.md` → Unicode Standard")
    lines.append("- 内联汇编：`concept/03_advanced/13_inline_assembly.md` → Intel/ARM 架构手册")
    lines.append("- 网络编程：`concept/03_advanced/18_network_programming.md` → IETF RFCs")
    lines.append("- ABI：`concept/04_formal/38_application_binary_interface.md` → Itanium C++ ABI / System V AMD64 ABI")
    lines.append("- 交叉编译/嵌入式：`concept/06_ecosystem/17_cross_compilation.md` / `22_embedded_systems.md` → 目标平台规范")
    lines.append("")

    lines.append("## 三、自动化建议")
    lines.append("")
    lines.append("1. 在 `kb_auditor.py` 中增加：概念文件必须引用至少一个 L1 来源。")
    lines.append("2. 每月运行 `extract_concept_topology.py` + `generate_knowledge_topology_atlas.py` 生成图谱集。")
    lines.append("3. 对新增文件自动检测是否包含决策树/矩阵/示例反例中的一种表征。")
    lines.append("")

    lines.extend(footer())
    (OUT_DIR / "10_gap_and_action_plan.md").write_text("\n".join(lines), encoding="utf-8")


def write_remaining_stubs() -> None:
    stubs = {
        "03_scenario_decision_tree_atlas.md": (
            "场景决策树图谱（Scenario Decision Tree Atlas）",
            "Scenario Decision Tree Atlas",
            "典型开发场景 → 决策问题 → 候选方案 → Rust 概念/工具选择。",
        ),
        "04_example_counterexample_atlas.md": (
            "示例与反例图谱（Example and Counterexample Atlas）",
            "Example and Counterexample Atlas",
            "按概念组织的正确示例、错误示例、边界示例与反例分析。",
        ),
        "05_logical_reasoning_atlas.md": (
            "逻辑推理图谱（Logical Reasoning Atlas）",
            "Logical Reasoning Atlas",
            "定理链（⟹/⟸）、推理规则、证明/验证路径、形式化对应。",
        ),
        "09_reasoning_judgment_tree_atlas.md": (
            "推理判定树图谱（Reasoning Judgment Tree Atlas）",
            "Reasoning Judgment Tree Atlas",
            "编译错误/运行时问题 → 判定问题 → 根因 → 修复策略的概念路径。",
        ),
    }

    for filename, (title, en, summary) in stubs.items():
        path = OUT_DIR / filename
        lines = header(title, en, summary)
        lines.append("## 一、待构建内容")
        lines.append("")
        lines.append("<!-- MANUAL: 本文件需要人工策展，从各 concept 文件中抽取场景、示例、推理链、判定树。 -->")
        lines.append("")
        lines.append("本图谱将按以下维度组织：")
        lines.append("")
        if "Scenario" in en:
            lines.append("- 内存管理场景：栈 vs 堆、所有权转移、借用选择")
            lines.append("- 并发场景：共享状态 vs 消息传递、同步 vs 异步")
            lines.append("- 错误处理场景：Result vs panic、自定义错误类型")
            lines.append("- FFI 场景：安全封装、ABI 选择、生命周期桥接")
        elif "Example" in en:
            lines.append("- 正确示例：展示概念的标准用法")
            lines.append("- 错误示例：展示常见误用及编译器报错")
            lines.append("- 边界示例：展示边界条件和特殊情形")
            lines.append("- 反例分析：解释为何某些写法不成立")
        elif "Logical" in en:
            lines.append("- 所有权推理链：Ownership → Borrowing → Lifetimes")
            lines.append("- 类型系统推理链：Type → Trait → Generic → Lifetime")
            lines.append("- 并发安全推理链：Send/Sync → Mutex → Atomic → Memory Ordering")
            lines.append("- 形式化对应：Rust 概念 ↔ 线性逻辑 / 分离逻辑 / 类型论")
        elif "Judgment" in en:
            lines.append("- Borrow checker 错误判定树")
            lines.append("- 生命周期错误判定树")
            lines.append("- 类型不匹配错误判定树")
            lines.append("- 运行时 panic 根因判定树")
        lines.append("")
        lines.extend(footer())
        path.write_text("\n".join(lines), encoding="utf-8")


def main() -> None:
    data = load_raw()
    concepts = data["concepts"]
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    write_readme(data)
    write_concept_definition_atlas(concepts)
    write_attribute_relationship_atlas(concepts)
    write_inter_layer_mapping_atlas(concepts)
    write_intra_layer_mapping_atlas(concepts)
    write_concept_source_alignment_atlas(concepts)
    write_gap_and_action_plan(concepts)
    write_remaining_stubs()

    print(f"Generated atlas files in {OUT_DIR}")


if __name__ == "__main__":
    main()
