#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""rustc error code -> decision tree entry lookup.

Usage:
    python scripts/rustc_error_to_decision_tree.py E0502
    python scripts/rustc_error_to_decision_tree.py --list
    python scripts/rustc_error_to_decision_tree.py --generate-index tmp/error_code_index.json

加载 concept/00_meta/knowledge_topology/decision_trees.yaml，优先匹配节点级
rustc_error_codes（无歧义），回退到树级 rustc_error_codes。输出决策树入口、
简短描述与对应 concept/ 权威页路径。
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEFAULT_YAML = os.path.join(ROOT, "concept", "00_meta", "knowledge_topology", "decision_trees.yaml")

RUSTC_ERROR_CODE_RE = re.compile(r"^E\d{4}$")

# rustc error code 简短描述与对应 concept/ 权威页
ERROR_CODE_DESCRIPTIONS: dict[str, str] = {
    "E0106": "missing lifetime specifier（函数/结构体签名缺少生命周期标注）",
    "E0119": "conflicting implementations of trait（trait 实现冲突）",
    "E0277": "the trait bound `T: Trait` is not satisfied（trait bound 未满足）",
    "E0282": "type annotations needed（需要更多类型标注）",
    "E0283": "type annotations needed: cannot resolve `T: Trait`（类型推断歧义）",
    "E0308": "mismatched types（类型不匹配）",
    "E0373": "async fn may outlive the current lifetime（async 状态机捕获引用跨 await）",
    "E0382": "use of moved value（使用已移动值）",
    "E0433": "failed to resolve use of undeclared crate/module（未解析的 crate/module）",
    "E0499": "cannot borrow `X` as mutable more than once at a time（重复可变借用）",
    "E0501": "cannot borrow `X` as mutable because it is also borrowed as immutable",
    "E0502": "cannot borrow `X` as immutable because it is also borrowed as mutable",
    "E0503": "cannot use `X` because it was mutably borrowed",
    "E0505": "cannot move out of `X` because it is borrowed",
    "E0597": "`X` does not live long enough（值生命周期不足）",
    "E0609": "no field named `X` on type `Y`（字段访问失败）",
    "E0621": "explicit lifetime required in function signature（函数签名需要显式生命周期）",
    "E0700": "hidden type for `impl Trait` captures lifetime that does not appear in bounds",
    "E0729": "feature `async_await` is required（async/await 特性门）",
    "E0733": "recursive async function（递归 async fn）",
    "E0759": "function cannot return a value referencing data owned by the current function",
}

# rustc error code -> concept/ 权威页路径（相对仓库根目录）
ERROR_CODE_AUTHORITY_PAGES: dict[str, str] = {
    "E0106": "concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md",
    "E0119": "concept/02_intermediate/00_traits/04_advanced_traits.md",
    "E0277": "concept/02_intermediate/00_traits/01_traits.md",
    "E0282": "concept/02_intermediate/01_generics/01_generics.md",
    "E0283": "concept/02_intermediate/01_generics/01_generics.md",
    "E0308": "concept/01_foundation/02_type_system/01_type_system.md",
    "E0373": "concept/03_advanced/01_async/01_async.md",
    "E0382": "concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md",
    "E0433": "concept/02_intermediate/05_modules_and_visibility/01_module_system.md",
    "E0499": "concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md",
    "E0501": "concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md",
    "E0502": "concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md",
    "E0503": "concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md",
    "E0505": "concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md",
    "E0597": "concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md",
    "E0609": "concept/01_foundation/07_modules_and_items/04_structs.md",
    "E0621": "concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md",
    "E0700": "concept/03_advanced/01_async/02_async_advanced.md",
    "E0729": "concept/03_advanced/01_async/01_async.md",
    "E0733": "concept/03_advanced/01_async/01_async.md",
    "E0759": "concept/01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md",
}


def load_yaml(path: str):
    try:
        import yaml
    except ImportError:
        print("ERROR: 需要 PyYAML（pip install pyyaml）")
        sys.exit(2)
    with open(path, encoding="utf-8") as f:
        return yaml.safe_load(f)


def build_indexes(data: dict):
    """构建节点级和树级错误码索引。"""
    node_index: dict[str, list[dict]] = {}
    tree_index: dict[str, list[dict]] = {}
    for tree in data.get("trees", []):
        tid = tree.get("id")
        title_zh = tree.get("title_zh", "")
        title_en = tree.get("title_en", "")
        source = tree.get("source", {})
        for node in tree.get("nodes", []):
            for code in node.get("rustc_error_codes", []) or []:
                if isinstance(code, str) and RUSTC_ERROR_CODE_RE.match(code):
                    node_index.setdefault(code, []).append({
                        "tree_id": tid,
                        "node_id": node.get("id"),
                        "tree_title_zh": title_zh,
                        "tree_title_en": title_en,
                        "node_label": node.get("label", node.get("condition", "")),
                        "source_file": source.get("file", ""),
                        "source_anchor": source.get("anchor", ""),
                    })
        for code in tree.get("rustc_error_codes", []) or []:
            if isinstance(code, str) and RUSTC_ERROR_CODE_RE.match(code):
                tree_index.setdefault(code, []).append({
                    "tree_id": tid,
                    "tree_title_zh": title_zh,
                    "tree_title_en": title_en,
                    "source_file": source.get("file", ""),
                    "source_anchor": source.get("anchor", ""),
                })
    return node_index, tree_index


def lookup(code: str, node_index: dict, tree_index: dict) -> dict | None:
    """优先返回节点级匹配，回退树级匹配。"""
    entries = node_index.get(code)
    level = "node"
    if not entries:
        entries = tree_index.get(code)
        level = "tree"
    if not entries:
        return None
    return {"level": level, "entries": entries}


def format_entry(code: str, result: dict) -> str:
    lines = [f"Error code: {code}"]
    desc = ERROR_CODE_DESCRIPTIONS.get(code)
    if desc:
        lines.append(f"Description: {desc}")
    else:
        lines.append("Description: （暂无描述，请补充到 ERROR_CODE_DESCRIPTIONS）")

    level = result["level"]
    entries = result["entries"]
    if level == "node":
        entry = entries[0]  # 节点级经校验无歧义
        lines.append(f"Decision tree: {entry['tree_id']}")
        lines.append(f"Entry node: {entry['node_id']}")
        lines.append(f"Tree title: {entry['tree_title_zh']} / {entry['tree_title_en']}")
        source = entry["source_file"]
        if entry["source_anchor"]:
            source += entry["source_anchor"]
        lines.append(f"Source: {source}")
    else:
        lines.append(f"Decision tree(s) (tree-level mapping):")
        for entry in entries:
            lines.append(f"  - {entry['tree_id']}: {entry['tree_title_zh']} / {entry['tree_title_en']}")
        source = entries[0]["source_file"]
        if entries[0]["source_anchor"]:
            source += entries[0]["source_anchor"]
        lines.append(f"Source: {source}")

    authority = ERROR_CODE_AUTHORITY_PAGES.get(code)
    if authority:
        lines.append(f"Authority page: {authority}")
    else:
        lines.append("Authority page: （暂无映射，请补充到 ERROR_CODE_AUTHORITY_PAGES）")
    return "\n".join(lines)


def list_codes(node_index: dict, tree_index: dict) -> str:
    all_codes = sorted(set(node_index) | set(tree_index))
    lines = [f"Total mapped rustc error codes: {len(all_codes)}", ""]
    lines.append(f"{'Code':<8} {'Level':<6} {'Tree ID':<16} {'Node':<8} Authority page")
    for code in all_codes:
        result = lookup(code, node_index, tree_index)
        level = result["level"] if result else "?"
        if level == "node":
            entry = result["entries"][0]
            tree_id = entry["tree_id"]
            node_id = entry["node_id"]
        else:
            entry = result["entries"][0] if result else {}
            tree_id = entry.get("tree_id", "")
            node_id = "-"
        authority = ERROR_CODE_AUTHORITY_PAGES.get(code, "")
        lines.append(f"{code:<8} {level:<6} {tree_id:<16} {node_id:<8} {authority}")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0] if __doc__ else "")
    ap.add_argument("code", nargs="?", help="rustc error code, e.g. E0502")
    ap.add_argument("--file", default=DEFAULT_YAML, help="决策树 YAML 路径")
    ap.add_argument("--list", action="store_true", help="列出所有已映射错误码")
    ap.add_argument("--generate-index", nargs="?", const="", metavar="PATH",
                    help="生成错误码索引 JSON（默认输出到 stdout）")
    args = ap.parse_args()

    if not os.path.isfile(args.file):
        print(f"ERROR: 文件不存在: {args.file}")
        return 1

    data = load_yaml(args.file)
    node_index, tree_index = build_indexes(data)

    if args.list:
        print(list_codes(node_index, tree_index))
        return 0

    if args.generate_index is not None:
        index = {
            "version": data.get("version", "1.0"),
            "date": data.get("date", ""),
            "description": "rustc error code -> decision tree/node lookup",
            "source": os.path.relpath(args.file, ROOT).replace(chr(92), "/"),
            "node_index": {
                code: entries for code, entries in sorted(node_index.items())
            },
            "tree_index": {
                code: entries for code, entries in sorted(tree_index.items())
            },
            "descriptions": ERROR_CODE_DESCRIPTIONS,
            "authority_pages": ERROR_CODE_AUTHORITY_PAGES,
        }
        if args.generate_index:
            os.makedirs(os.path.dirname(args.generate_index) or ".", exist_ok=True)
            with open(args.generate_index, "w", encoding="utf-8") as f:
                json.dump(index, f, ensure_ascii=False, indent=2)
            print(f"generated index: {os.path.relpath(args.generate_index, ROOT).replace(chr(92), '/')}")
        else:
            json.dump(index, sys.stdout, ensure_ascii=False, indent=2)
            print()
        return 0

    if not args.code:
        ap.print_help()
        return 1

    code = args.code.upper()
    if not RUSTC_ERROR_CODE_RE.match(code):
        print(f"ERROR: invalid rustc error code format: {args.code!r}（expected E\d{{4}}）")
        return 1

    result = lookup(code, node_index, tree_index)
    if not result:
        print(f"No decision tree mapping found for {code}.")
        print(f"Currently mapped codes: {', '.join(sorted(set(node_index) | set(tree_index)))}")
        return 2

    print(format_entry(code, result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
