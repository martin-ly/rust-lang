#!/usr/bin/env python3
"""
知识图谱推理脚本：调用 c14_semantic_web crate 的 kg_query example。

用法:
    python scripts/kg_reasoning.py --kg concept/00_meta/kg_data_v3.json
    python scripts/kg_reasoning.py --kg concept/00_meta/kg_data_v3.json --validate
    python scripts/kg_reasoning.py --kg concept/00_meta/kg_data_v3.json --prerequisites ex:Lifetimes
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def run_validate(kg_path: Path) -> bool:
    cmd = ["cargo", "run", "--example", "kg_validate", "--", str(kg_path)]
    result = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    print(result.stdout)
    if result.returncode != 0:
        print(result.stderr, file=sys.stderr)
        return False
    return True


def run_query(kg_path: Path) -> dict:
    cmd = ["cargo", "run", "--example", "kg_query", "--", str(kg_path)]
    result = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    if result.returncode != 0:
        print(result.stderr, file=sys.stderr)
        raise RuntimeError("kg_query failed")
    # 示例输出是文本，不是 JSON；这里仅打印
    print(result.stdout)
    return {}


def load_kg(kg_path: Path) -> dict:
    with kg_path.open("r", encoding="utf-8") as f:
        return json.load(f)


def find_prerequisites(kg: dict, target: str, transitive: bool = True) -> set[str]:
    """计算目标概念的前置概念（基于 dependsOn）。"""
    relations = [
        (r["ex:subject"], r["ex:object"])
        for r in kg.get("relations", [])
        if r.get("ex:predicate") == "ex:dependsOn"
    ]

    direct = {obj for subj, obj in relations if subj == target}
    if not transitive:
        return direct

    all_deps = set(direct)
    changed = True
    while changed:
        changed = False
        for subj, obj in relations:
            if subj in all_deps and obj not in all_deps:
                all_deps.add(obj)
                changed = True
    return all_deps


def label_of(kg: dict, entity_id: str, lang: str = "zh") -> str:
    raw = kg.get("entities", [])
    items = raw if isinstance(raw, list) else [i for group in raw.values() for i in group]
    for item in items:
        if item.get("@id") == entity_id:
            labels = item.get("skos:prefLabel", [])
            # v3 部分实体 zh 标签为空字符串，回退到 en
            for wanted in (lang, "en"):
                for lbl in labels:
                    if lbl.get("@language") == wanted and lbl.get("@value"):
                        return lbl["@value"]
            return entity_id
    return entity_id


def main() -> None:
    parser = argparse.ArgumentParser(description="KG reasoning wrapper")
    parser.add_argument("--kg", default="concept/00_meta/kg_data_v3.json", help="KG JSON-LD v3 path")
    parser.add_argument("--validate", action="store_true", help="run validation")
    parser.add_argument("--prerequisites", help="find prerequisites for an entity (e.g. ex:Lifetimes)")
    args = parser.parse_args()

    kg_path = ROOT / args.kg

    if args.validate:
        ok = run_validate(kg_path)
        sys.exit(0 if ok else 1)

    if args.prerequisites:
        kg = load_kg(kg_path)
        deps = find_prerequisites(kg, args.prerequisites)
        print(f"学习「{label_of(kg, args.prerequisites)}」之前需掌握:")
        for dep in sorted(deps):
            print(f"  - {label_of(kg, dep)} ({dep})")
        return

    # 默认：运行完整查询示例
    run_query(kg_path)


if __name__ == "__main__":
    main()
