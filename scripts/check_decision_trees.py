#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""决策树机器可读层校验：concept/00_meta/knowledge_topology/decision_trees.yaml。

背景：KG v3 (concept/00_meta/kg_data_v3.json) 中 decision_trees 只是
{concept, tree} 指针 stub，不可遍历。decision_trees.yaml 为
09_reasoning_judgment_tree_atlas.md 的判定树与
concept_definition_decision_forest.md 的判定树提供可遍历结构。

校验内容：
  S1 结构完整性 —— 必填字段、节点 id 唯一、type ∈ {decision, conclusion, condition}、
      decision 节点必须有 condition 文本，quantitative=true 必须有 threshold、
      边的 from/to 必须引用已声明节点。（结构错误：始终 exit 1）
  S2 无死端 —— 每个 decision 节点 ≥1 条出边；每个无出边的叶子必须是 conclusion。
      （质量问题：默认 warning；--strict 时死端 > 0 ⟹ exit 1）
  S3 概念引用 —— covered_concepts 必须存在于 KG v3 entities 的 @id 中。
      （质量问题：默认 warning；--strict 时缺失 > 0 ⟹ exit 1）
  S4 判定定量占比 —— quantitative=true 的 decision 节点占比，报告并与 50% 基线对比。
      （质量问题：默认 warning；--strict 时 < 50% ⟹ exit 1）
  S5 rustc 错误码 —— tree/节点级别的 rustc_error_codes（可选）格式须为 E\d{4}；
      节点级跨节点重复映射视为「歧义」并阻断；tree 级跨树重复仍视为「合并」并报告。
      同时报告 Top 30 常见 rustc 错误码的覆盖率。

用法：
    python scripts/check_decision_trees.py            # 默认 warning，exit 0（结构错误除外）
    python scripts/check_decision_trees.py --strict   # 死端/缺失概念/定量占比<50%/节点歧义 ⟹ exit 1
    python scripts/check_decision_trees.py --file path/to/other.yaml
    python scripts/check_decision_trees.py --generate-index tmp/decision_tree_error_code_index.json
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_YAML = os.path.join(ROOT, "concept", "00_meta", "knowledge_topology", "decision_trees.yaml")
KG_JSON = os.path.join(ROOT, "concept", "00_meta", "kg_data_v3.json")
DEFAULT_INDEX = os.path.join(ROOT, "concept", "00_meta", "knowledge_topology", "decision_tree_error_code_index.json")

NODE_TYPES = {"decision", "conclusion", "condition"}
QUANT_BASELINE = 0.50
RUSTC_ERROR_CODE_RE = re.compile(r"^E\d{4}$")

# 常见 rustc 错误码 Top 30 候选集（覆盖借用、所有权、生命周期、异步、类型、名称解析等）
TOP30_RUSTC_ERROR_CODES = [
    "E0308", "E0277", "E0433", "E0425", "E0597", "E0382", "E0502",
    "E0499", "E0501", "E0373", "E0412", "E0282", "E0061", "E0106",
    "E0119", "E0301", "E0023", "E0026", "E0027", "E0063", "E0220",
    "E0283", "E0609", "E0621", "E0700", "E0733", "E0759", "E0505",
    "E0117", "E0531",
]


def load_yaml(path: str):
    try:
        import yaml  # PyYAML
    except ImportError:
        print("ERROR: 需要 PyYAML（pip install pyyaml）")
        sys.exit(2)
    with open(path, encoding="utf-8") as f:
        return yaml.safe_load(f)


def load_kg_ids(path: str) -> set[str]:
    try:
        with open(path, encoding="utf-8") as f:
            data = json.load(f)
        return {e.get("@id") for e in data.get("entities", []) if e.get("@id")}
    except Exception as exc:  # KG 缺失时退化为跳过 S3
        print(f"WARN: 无法加载 KG v3（{exc}），跳过概念引用校验")
        return set()


def validate_tree(tree: dict, kg_ids: set[str], errors: list[str], warnings: list[str]) -> dict:
    """校验单棵树，返回统计信息。结构错误进 errors，质量问题进 warnings。"""
    tid = tree.get("id", "<no-id>")
    stats = {"id": tid, "nodes": 0, "edges": 0, "decisions": 0, "quant": 0,
             "dead_ends": [], "unknown_concepts": [],
             "rustc_codes": [], "invalid_rustc_codes": [],
             "node_rustc_codes": {},  # node_id -> list[code]
             "source": tree.get("source", {})}

    for field in ("id", "title_zh", "title_en", "source", "covered_concepts", "nodes", "edges"):
        if field not in tree:
            errors.append(f"[{tid}] 缺少必填字段: {field}")
    if errors and tid == "<no-id>":
        return stats

    src = tree.get("source", {})
    if not isinstance(src, dict) or "file" not in src or "anchor" not in src:
        errors.append(f"[{tid}] source 必须含 file 与 anchor")
    else:
        src_path = os.path.join(ROOT, src["file"])
        if not os.path.isfile(src_path):
            errors.append(f"[{tid}] source.file 不存在: {src['file']}")

    nodes = tree.get("nodes", []) or []
    edges = tree.get("edges", []) or []
    node_ids: dict[str, dict] = {}
    for n in nodes:
        nid = n.get("id")
        ntype = n.get("type")
        if not nid:
            errors.append(f"[{tid}] 存在无 id 的节点")
            continue
        if nid in node_ids:
            errors.append(f"[{tid}] 节点 id 重复: {nid}")
        node_ids[nid] = n
        if ntype not in NODE_TYPES:
            errors.append(f"[{tid}] 节点 {nid} type 非法: {ntype!r}（须 ∈ {sorted(NODE_TYPES)}）")
        if ntype == "decision":
            stats["decisions"] += 1
            if not n.get("condition"):
                errors.append(f"[{tid}] decision 节点 {nid} 缺少 condition 判定条件文本")
            if n.get("quantitative") is True:
                stats["quant"] += 1
                if not n.get("threshold"):
                    errors.append(f"[{tid}] decision 节点 {nid} quantitative=true 但缺少 threshold 定量阈值")

        # S5 节点级 rustc 错误码格式校验
        node_codes = n.get("rustc_error_codes", []) or []
        if node_codes:
            valid_node_codes = []
            invalid_node_codes = []
            for code in node_codes:
                if isinstance(code, str) and RUSTC_ERROR_CODE_RE.match(code):
                    valid_node_codes.append(code)
                else:
                    invalid_node_codes.append(code)
            stats["node_rustc_codes"][nid] = valid_node_codes
            if invalid_node_codes:
                errors.append(f"[{tid}] 节点 {nid} rustc_error_codes 格式错误: {invalid_node_codes!r}（须为 E\\d{{4}}）")

    stats["nodes"] = len(node_ids)

    out_edges: dict[str, int] = {}
    for e in edges:
        frm, to = e.get("from"), e.get("to")
        if frm not in node_ids:
            errors.append(f"[{tid}] 边引用未声明节点 from={frm!r}")
        if to not in node_ids:
            errors.append(f"[{tid}] 边引用未声明节点 to={to!r}")
        if not e.get("label"):
            errors.append(f"[{tid}] 边 {frm!r}->{to!r} 缺少 label（是/否/条件:...）")
        if frm in node_ids:
            out_edges[frm] = out_edges.get(frm, 0) + 1
    stats["edges"] = len(edges)

    # S2 无死端
    for nid, n in node_ids.items():
        outs = out_edges.get(nid, 0)
        if n.get("type") == "decision" and outs == 0:
            stats["dead_ends"].append(f"{nid}（decision 无出边）")
        elif outs == 0 and n.get("type") != "conclusion":
            stats["dead_ends"].append(f"{nid}（叶子非 conclusion: {n.get('type')}）")
    if stats["dead_ends"]:
        warnings.append(f"[{tid}] 死端 {len(stats['dead_ends'])}: {stats['dead_ends'][:5]}")

    # S3 概念引用存在性
    if kg_ids:
        for c in tree.get("covered_concepts", []) or []:
            if c not in kg_ids:
                stats["unknown_concepts"].append(c)
        if stats["unknown_concepts"]:
            warnings.append(f"[{tid}] KG v3 中不存在的概念引用: {stats['unknown_concepts']}")

    # S5 tree 级 rustc 错误码格式校验
    rustc_codes = tree.get("rustc_error_codes", []) or []
    for code in rustc_codes:
        if not isinstance(code, str) or not RUSTC_ERROR_CODE_RE.match(code):
            stats["invalid_rustc_codes"].append(code)
        else:
            stats["rustc_codes"].append(code)
    if stats["invalid_rustc_codes"]:
        errors.append(f"[{tid}] rustc_error_codes 格式错误: {stats['invalid_rustc_codes']!r}（须为 E\\d{{4}}）")
    return stats


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0] if __doc__ else "")
    ap.add_argument("--file", default=DEFAULT_YAML, help="决策树 YAML 路径")
    ap.add_argument("--strict", action="store_true", help="死端/缺失概念/定量占比<50%/节点歧义 ⟹ exit 1")
    ap.add_argument("--generate-index", nargs="?", const=DEFAULT_INDEX, metavar="PATH",
                    help="生成错误码 → 决策树索引 JSON（默认路径：%s）" % DEFAULT_INDEX)
    args = ap.parse_args()

    if not os.path.isfile(args.file):
        print(f"ERROR: 文件不存在: {args.file}")
        return 1

    data = load_yaml(args.file)
    if not isinstance(data, dict) or "trees" not in data:
        print("ERROR: YAML 顶层必须是含 trees 列表的 mapping")
        return 1

    kg_ids = load_kg_ids(KG_JSON)
    errors: list[str] = []
    warnings: list[str] = []
    all_stats = []
    seen_tree_ids: set[str] = set()
    for tree in data["trees"]:
        if not isinstance(tree, dict):
            errors.append("存在非 mapping 的 tree 条目")
            continue
        if tree.get("id") in seen_tree_ids:
            errors.append(f"树 id 重复: {tree.get('id')}")
        seen_tree_ids.add(tree.get("id"))
        all_stats.append(validate_tree(tree, kg_ids, errors, warnings))

    total_dec = sum(s["decisions"] for s in all_stats)
    total_quant = sum(s["quant"] for s in all_stats)
    total_dead = sum(len(s["dead_ends"]) for s in all_stats)
    total_unknown = sum(len(s["unknown_concepts"]) for s in all_stats)
    quant_rate = (total_quant / total_dec) if total_dec else 1.0

    # 构建 tree 级错误码索引与跨树重复检测（合并语义）
    code_to_trees: dict[str, list[str]] = {}
    for s in all_stats:
        for code in s.get("rustc_codes", []):
            code_to_trees.setdefault(code, []).append(s["id"])
    total_tree_codes = sum(len(s.get("rustc_codes", [])) for s in all_stats)
    duplicate_tree_codes = {code: trees for code, trees in code_to_trees.items() if len(trees) > 1}

    # 构建节点级错误码索引与跨节点重复检测（歧义）
    code_to_nodes: dict[str, list[tuple[str, str]]] = {}
    for s in all_stats:
        tid = s["id"]
        for nid, codes in s.get("node_rustc_codes", {}).items():
            for code in codes:
                code_to_nodes.setdefault(code, []).append((tid, nid))
    total_node_codes = sum(len(codes) for codes in code_to_nodes.values())
    duplicate_node_codes = {code: pairs for code, pairs in code_to_nodes.items() if len(pairs) > 1}
    if duplicate_node_codes:
        for code, pairs in sorted(duplicate_node_codes.items()):
            errors.append(f"rustc error code {code} 映射到多个节点: {pairs}（节点级歧义）")

    # Top 30 覆盖率统计（tree 级 + 节点级并集）
    all_mapped_codes = set(code_to_trees) | set(code_to_nodes)
    top30_covered = [code for code in TOP30_RUSTC_ERROR_CODES if code in all_mapped_codes]
    top30_coverage = len(top30_covered)

    print(f"[decision-trees] file={os.path.relpath(args.file, ROOT).replace(chr(92), '/')}")
    print(f"  trees={len(all_stats)} nodes={sum(s['nodes'] for s in all_stats)} edges={sum(s['edges'] for s in all_stats)}")
    print(f"  decisions={total_dec} quantitative={total_quant} quant_rate={quant_rate*100:.1f}% (基线 ≥{QUANT_BASELINE*100:.0f}%)")
    print(f"  dead_ends={total_dead} unknown_concepts={total_unknown}")
    print(f"  tree_rustc_codes={total_tree_codes} unique={len(code_to_trees)} merged={len(duplicate_tree_codes)}")
    print(f"  node_rustc_codes={total_node_codes} unique={len(code_to_nodes)} ambiguous={len(duplicate_node_codes)}")
    print(f"  top30_coverage={top30_coverage}/{len(TOP30_RUSTC_ERROR_CODES)} ({top30_coverage*100//len(TOP30_RUSTC_ERROR_CODES)}%)")
    for s in all_stats:
        qr = f"{s['quant']}/{s['decisions']}" if s["decisions"] else "n/a"
        codes = s.get("rustc_codes", [])
        node_codes_flat = [c for codes in s.get("node_rustc_codes", {}).values() for c in codes]
        code_str = ""
        if codes:
            code_str += f" tree_codes={codes}"
        if node_codes_flat:
            code_str += f" node_codes={node_codes_flat}"
        print(f"    - {s['id']}: nodes={s['nodes']} edges={s['edges']} quant={qr} dead={len(s['dead_ends'])}{code_str}")

    for e in errors:
        print(f"  ERROR: {e}")
    for w in warnings:
        print(f"  WARN: {w}")
    if duplicate_tree_codes:
        print("  INFO: 以下 rustc error code 跨多棵决策树合并映射（共享语义域）：")
        for code in sorted(duplicate_tree_codes):
            print(f"    {code} -> {duplicate_tree_codes[code]}")

    if errors:
        print(f"[decision-trees] FAIL（结构/节点歧义错误 {len(errors)}）")
        return 1
    quality_fail = []
    if total_dead > 0:
        quality_fail.append(f"死端 {total_dead} > 0")
    if total_unknown > 0:
        quality_fail.append(f"KG 缺失概念引用 {total_unknown} > 0")
    if total_dec >= 3 and quant_rate < QUANT_BASELINE:
        quality_fail.append(f"判定定量占比 {quant_rate*100:.1f}% < {QUANT_BASELINE*100:.0f}%")
    if quality_fail:
        print(f"[decision-trees] {'FAIL' if args.strict else 'WARN'}（质量问题）: {'; '.join(quality_fail)}")
        return 1 if args.strict else 0

    if args.generate_index:
        index = {
            "version": data.get("version", "1.0"),
            "date": data.get("date", ""),
            "description": "rustc error code -> decision tree lookup index",
            "validator": os.path.relpath(__file__, ROOT).replace(chr(92), "/"),
            "source": os.path.relpath(args.file, ROOT).replace(chr(92), "/"),
            "index": {
                code: [
                    {"tree_id": tid, "source_file": next(s.get("source", {}).get("file", "") for s in all_stats if s["id"] == tid),
                     "source_anchor": next(s.get("source", {}).get("anchor", "") for s in all_stats if s["id"] == tid)}
                    for tid in trees
                ]
                for code, trees in sorted(code_to_trees.items())
            },
            "merged_codes": {code: trees for code, trees in sorted(duplicate_tree_codes.items())},
        }
        os.makedirs(os.path.dirname(args.generate_index), exist_ok=True)
        with open(args.generate_index, "w", encoding="utf-8") as f:
            json.dump(index, f, ensure_ascii=False, indent=2)
        print(f"  generated index: {os.path.relpath(args.generate_index, ROOT).replace(chr(92), '/')}")

    print("[decision-trees] PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
