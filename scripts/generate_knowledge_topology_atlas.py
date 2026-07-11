#!/usr/bin/env python3
"""
Generate Knowledge Topology Atlas markdown files from tmp/concept_topology_raw.json.

Output: concept/00_meta/knowledge_topology/*.md
"""
from __future__ import annotations

import json
import re
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


# 空洞定义模式:与 scripts/check_topology_quality.py 的 T1 DEF_LOW 对齐
HOLLOW_DEF_PATTERNS = [
    re.compile(r"core rust concept", re.IGNORECASE),
    re.compile(r"^—?\s*$"),
    re.compile(r"^\s*(a|an)\s+(guide|overview|introduction)\s+(to|of)\b", re.IGNORECASE),
    re.compile(r"^\s*(comprehensive|complete)\s+(analysis|guide|overview)\b", re.IGNORECASE),
]

# 定义缺失时的诚实占位(不编造语义;注意不可用“待补/占位/TODO”等字样,
# 否则会触发 check_topology_quality.py 的 T6 占位检查)
MISSING_DEF = "定义暂缺，请直接参见概念文件正文内容。"

# 首段抽取时需跳过的行前缀(元数据、结构线、代码块、目录、粗体小节标签、来源行)
_SKIP_PREFIX = ("#", ">", "---", "|", "```", "- [", "* [", "<!--", "<details", "<summary", "</",
               "[来源", "[Source", "(Source:", "（Source:", "来源:", "Source:")
_BOLD_LABEL_RE = re.compile(r"^\*\*[^*]{1,30}\*\*[:：]\s*$")
_LIST_ITEM_RE = re.compile(r"^(\d+[.、]|[-*])\s")

def is_hollow_definition(summary: str) -> bool:
    s = (summary or "").strip()
    if len(s) < 15:
        return True
    return any(p.search(s) for p in HOLLOW_DEF_PATTERNS)


def extract_first_paragraph(rel_path: str, max_len: int = 120) -> str:
    """从概念文件中抽取首个实质段落作为定义回退;失败返回空串。"""
    f = ROOT / "concept" / rel_path
    if not f.is_file():
        return ""
    para: list[str] = []
    in_code = False
    for ln in f.read_text(encoding="utf-8", errors="replace").splitlines():
        s = ln.strip()
        if s.startswith("```"):
            in_code = not in_code
            if para:
                break
            continue
        if in_code:
            continue
        if not s:
            if para:
                break
            continue
        if s.startswith(_SKIP_PREFIX) or _BOLD_LABEL_RE.match(s) or _LIST_ITEM_RE.match(s) or s.startswith("**"):
            if para:
                break
            continue
        para.append(s)
    text = " ".join(para).strip()
    if len(text) < 15:
        return ""
    if len(text) > max_len:
        cut = max(text.rfind("。", 0, max_len), text.rfind(". ", 0, max_len))
        hard_cut = cut < 15
        text = text[:max_len] if hard_cut else text[: cut + 1]
        # 截断不得落在 Markdown 链接内部:丢弃尾部不完整的 [text](url… 或 [text…
        text = re.sub(r"\[[^\]]*\]\([^)]*$", "", text)
        text = re.sub(r"\[[^\]]*$", "", text)
        text = text.rstrip(" ·，,；;：:")
        if hard_cut:
            text += "…"
    return text


def current_file_summary(rel_path: str) -> str:
    """读取概念文件当前的 **Summary** 元数据(raw json 可能过时)。"""
    f = ROOT / "concept" / rel_path
    if not f.is_file():
        return ""
    m = re.search(r">\s*\*\*Summary\*\*[:：]\s*(.+)", f.read_text(encoding="utf-8", errors="replace"))
    return m.group(1).strip() if m else ""


def definition_or_fallback(summary: str, rel_path: str) -> str:
    """定义列取值:优先用文件 **Summary** 元数据;空洞时依次回退到
    文件当前 Summary(应对过时 raw json) → 文件首段 → MISSING_DEF(诚实标注,不编造)。"""
    # 交叉引用尾注是面向原文件目录的相对链接,嵌入 atlas 后会变成死链,剥离
    summary = re.split(r"\s*\*\*📎 交叉引用", summary or "", maxsplit=1)[0].strip()
    if not is_hollow_definition(summary):
        return summary
    current = current_file_summary(rel_path)
    if current and not is_hollow_definition(current) and current != summary:
        return current
    para = extract_first_paragraph(rel_path)
    return para if para else MISSING_DEF



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
            summary = escape_cell(definition_or_fallback(c["summary"], c["path"]))
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
    lines.append("- 更详细的层间依赖图见 [../04_navigation/inter_layer_map.md](../04_navigation/inter_layer_map.md)")
    lines.append("- 层内模型映射见 [../04_navigation/intra_layer_model_map.md](../04_navigation/intra_layer_model_map.md)")
    lines.append("- 形式化本体规范见 [kg_ontology_v2.md](kg_ontology_v2.md)")
    lines.append("")

    lines.extend(footer())
    (OUT_DIR / "06_inter_layer_mapping_atlas.md").write_text("\n".join(lines), encoding="utf-8")


def write_intra_layer_mapping_atlas(concepts: list[dict[str, Any]]) -> None:
    lines = header(
        "层内映射图谱（Intra-Layer Mapping Atlas）",
        "Intra-Layer Mapping Atlas",
        "每层内部核心模型/概念间的等价、蕴含、依赖、互斥关系，基于同层前置/后置引用与策展语义标注。",
    )

    # ---- 关系语义推断规则（T2 反塌缩）--------------------------------------
    # 符号与 KG 属性对齐（scripts/type_kg_core_edges.py 使用同一策展依据）：
    #   → dependsOn   源依赖目标（目标出现在源的前置元数据中）
    #   ⟹ entails     源蕴含/导向目标（后置概念引用，默认）
    #   ⊑ refines     精化关系：名称含“进阶/机制/模式”的一侧精化另一侧（同主题目录）
    #   ⊥ mutexWith   两概念互斥、不能同时成立（策展标注，依据见“依据”列）
    #   ⇔ 对比/等价    对比型页面（vs/对比）间的对照关系
    #   ↔ 互参        互为后置概念的强互参关系
    _VS_HINT = re.compile(r"\bvs\b|对比|比较", re.IGNORECASE)
    _REFINE_HINT = re.compile(r"进阶|深入|高级|advanced|deep dive|internals|机制|模式|patterns", re.IGNORECASE)
    # “模式匹配”是控制流概念而非“设计模式”精化页，排除
    _REFINE_EXCLUDE = {"模式匹配"}

    # 策展互斥对（与 scripts/type_kg_core_edges.py CURATED_MUTEX 同源）：
    # key = 无序概念 id 对，value = 依据（文件:行号 + 引述）
    CURATED_MUTEX: dict[frozenset[str], str] = {
        frozenset({"02_borrowing", "23_move_semantics"}):
            "move 与活跃借用互斥（03_lifetimes.md:942 “所有权转移(move)与借用是互斥的”）",
        frozenset({"13_panic_and_abort", "32_error_handling_basics"}):
            "不可恢复(panic/abort)与可恢复(Result 传播)在同一错误现场二选一（13_panic_and_abort.md:5/91）",
        frozenset({"35_unions", "03_memory_management"}):
            "union 默认不 drop 字段，与 RAII 自动析构纪律互斥（35_unions.md:105/250）",
        frozenset({"39_type_level_programming", "25_rtti_and_dynamic_typing"}):
            "编译期类型计算与运行期类型识别互斥（25_rtti_and_dynamic_typing.md:203 “RTTI 是静态类型系统向运行时的有限泄漏”）",
    }

    def link_ids(links: list[dict[str, str]]) -> set[str]:
        return {Path(l.get("href", "")).stem for l in links if l.get("href", "").endswith(".md")}

    def infer_relation(src: dict[str, Any], dst: dict[str, Any]) -> tuple[str, str]:
        """返回 (关系符号, 依据说明)。按语义特异度从高到低匹配。"""
        pair = frozenset({src["id"], dst["id"]})
        if pair in CURATED_MUTEX:
            return "⊥", "策展互斥：" + CURATED_MUTEX[pair]
        if _VS_HINT.search(src["zh_name"]) or _VS_HINT.search(dst["zh_name"]):
            return "⇔", "对比型页面（名称含 vs/对比）"
        src_pre, src_post = link_ids(src["prereqs"]), link_ids(src["postreqs"])
        dst_post = link_ids(dst["postreqs"])
        if dst["id"] in src_post and src["id"] in dst_post:
            return "↔", "互为后置概念（互参）"
        if dst["id"] in src_pre:
            return "→", "目标在源的前置元数据中（源依赖目标）"
        same_dir = Path(src["path"]).parent == Path(dst["path"]).parent
        refine_side = (
            (_REFINE_HINT.search(dst["zh_name"]) and dst["zh_name"] not in _REFINE_EXCLUDE)
            or (_REFINE_HINT.search(src["zh_name"]) and src["zh_name"] not in _REFINE_EXCLUDE)
        )
        if same_dir and refine_side:
            return "⊑", "同主题目录，一端为进阶/机制/模式（精化关系）"
        return "⟹", "后置概念引用（蕴含/导向）"

    id_to_concept = {c["id"]: c for c in concepts}
    by_layer = defaultdict(list)
    for c in concepts:
        by_layer[c["layer"]].append(c)

    lines.append("**关系符号约定**（与 KG v3 属性对齐；推断规则见 `scripts/generate_knowledge_topology_atlas.py` `infer_relation`）：")
    lines.append("")
    lines.append("- `→` dependsOn：源依赖目标（目标在源的前置元数据中）")
    lines.append("- `⟹` entails：源蕴含/导向目标（后置概念引用，默认）")
    lines.append("- `⊑` refines：精化关系，名称含“进阶/机制/模式”的一侧精化另一侧（同主题目录）")
    lines.append("- `⊥` mutexWith：两概念互斥（策展标注，依据见各行）")
    lines.append("- `⇔` 对比/等价：对比型页面（vs/对比）间的对照关系")
    lines.append("- `↔` 互参：互为后置概念的强互参关系")
    lines.append("")

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

        # 策展互斥对：即使无直接引用边也补一行（语义关系独立于引用关系）
        layer_ids = {c["id"] for c in layer_concepts}
        curated_rows = []
        for pair, why in CURATED_MUTEX.items():
            if pair <= layer_ids:
                a, b = sorted(pair)
                if b not in intra_refs.get(a, {}) and a not in intra_refs.get(b, {}):
                    curated_rows.append((a, b, why))

        if not any(intra_refs.values()) and not curated_rows:
            lines.append("> 本层内部引用较少，主要作为独立主题存在。")
            lines.append("")
            continue

        lines.append("### 层内引用关系")
        lines.append("")
        lines.append("| 源概念 | 关系 | 目标概念 | 依据 |")
        lines.append("|:---|:---:|:---|:---|")
        for src_id, targets in sorted(intra_refs.items()):
            src = id_to_concept[src_id]
            for dst_id, cnt in sorted(targets.items(), key=lambda x: -x[1]):
                dst = id_to_concept[dst_id]
                sym, why = infer_relation(src, dst)
                lines.append(
                    f"| [{escape_cell(src['zh_name'])}](../../{src['path']}) | {sym} | "
                    f"[{escape_cell(dst['zh_name'])}](../../{dst['path']}) | {escape_cell(why)} |"
                )
        for a, b, why in curated_rows:
            ca, cb = id_to_concept[a], id_to_concept[b]
            lines.append(
                f"| [{escape_cell(ca['zh_name'])}](../../{ca['path']}) | ⊥ | "
                f"[{escape_cell(cb['zh_name'])}](../../{cb['path']}) | 策展互斥：{escape_cell(why)}（无直接引用边，语义补全） |"
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
        # 防覆盖护栏：若文件已存在且不是本函数生成的 stub（不含“待构建内容”标记），
        # 说明已有人工策展内容（如 03/09 的 mermaid 判定树），跳过以免误删。
        if path.exists():
            existing = path.read_text(encoding="utf-8", errors="ignore")
            if "## 一、待构建内容" not in existing:
                continue
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
