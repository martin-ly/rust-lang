#!/usr/bin/env python3
"""
OWL 2 一致性检查（P2-4）

读取 concept/00_meta/kg_data_v2.json，检查以下 OWL 语义约束：
- ``ex:mutexWith``：对称（Symmetric）、反自反（Irreflexive）
- ``ex:dependsOn``：传递闭包中无环
- ``ex:equivalentTo``：对称（Symmetric）、传递（Transitive）

用法：
    python scripts/owl_consistency_check.py
"""
from __future__ import annotations

import json
import sys
from collections import defaultdict
from datetime import datetime
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parent.parent
KG_PATH = ROOT / "concept" / "00_meta" / "kg_data_v2.json"
REPORT_PATH = ROOT / "reports" / "OWL_CONSISTENCY_CHECK_2026_06_27.md"


def load_kg(path: Path) -> dict[str, Any]:
    with open(path, "r", encoding="utf-8") as f:
        return json.load(f)


def iter_entities(kg: dict[str, Any]) -> list[dict[str, Any]]:
    entities: list[dict[str, Any]] = []
    for category, items in kg.get("entities", {}).items():
        for item in items:
            item["_category"] = category
            entities.append(item)
    return entities


def short_id(uri: str) -> str:
    return uri.removeprefix("ex:")


def relation_graph(kg: dict[str, Any], predicate: str) -> tuple[set[tuple[str, str]], set[str]]:
    """Return (edges, nodes) for the given predicate."""
    edges: set[tuple[str, str]] = set()
    nodes: set[str] = set()
    for rel in kg.get("relations", []):
        if rel.get("ex:predicate") == predicate:
            subj = rel.get("ex:subject", "")
            obj = rel.get("ex:object", "")
            if subj and obj:
                edges.add((subj, obj))
                nodes.add(subj)
                nodes.add(obj)
    return edges, nodes


def check_symmetry(
    predicate: str,
    edges: set[tuple[str, str]],
    nodes: set[str],
) -> tuple[bool, list[str]]:
    """Check whether ``predicate`` is symmetric over the explicit edges."""
    violations: list[str] = []
    for a, b in edges:
        if (b, a) not in edges:
            violations.append(f"{short_id(a)} {short_id(predicate)} {short_id(b)} 缺少反向边")
    return len(violations) == 0, violations


def check_irreflexivity(
    predicate: str,
    edges: set[tuple[str, str]],
) -> tuple[bool, list[str]]:
    """Check whether ``predicate`` has no self-loops."""
    violations: list[str] = []
    for a, b in edges:
        if a == b:
            violations.append(f"{short_id(a)} {short_id(predicate)} {short_id(a)} 是自环")
    return len(violations) == 0, violations


def check_transitivity(
    predicate: str,
    edges: set[tuple[str, str]],
    nodes: set[str],
) -> tuple[bool, list[str]]:
    """Check whether the explicit graph violates transitivity."""
    adj: dict[str, set[str]] = defaultdict(set)
    for a, b in edges:
        adj[a].add(b)

    # Compute transitive closure with Floyd-Warshall-like BFS.
    closure: dict[str, set[str]] = {n: set() for n in nodes}
    for start in nodes:
        stack = list(adj[start])
        while stack:
            cur = stack.pop()
            if cur in closure[start]:
                continue
            closure[start].add(cur)
            stack.extend(adj[cur])

    violations: list[str] = []
    for a in nodes:
        for c in closure[a]:
            if (a, c) not in edges and a != c:
                # This is only a *violation* if we expect explicit edges for all
                # inferred transitive pairs. In OWL this is usually acceptable as
                # inferred knowledge, but for the KG audit we report missing
                # explicit links as warnings.
                violations.append(
                    f"{short_id(a)} {short_id(predicate)} {short_id(c)} 可由传递性推出但未显式声明"
                )
    return len(violations) == 0, violations


def detect_cycles(
    predicate: str,
    edges: set[tuple[str, str]],
    nodes: set[str],
) -> list[list[str]]:
    """Detect directed cycles for the given predicate (Tarjan/DFS)."""
    adj: dict[str, list[str]] = defaultdict(list)
    for a, b in edges:
        adj[a].append(b)

    WHITE, GRAY, BLACK = 0, 1, 2
    color: dict[str, int] = {n: WHITE for n in nodes}
    parent: dict[str, str | None] = {n: None for n in nodes}
    cycles: list[list[str]] = []

    def dfs(u: str, stack: list[str]) -> None:
        color[u] = GRAY
        for v in adj[u]:
            if color[v] == GRAY:
                # Found a cycle: extract from stack.
                if v in stack:
                    idx = stack.index(v)
                    cycle = stack[idx:] + [v]
                    cycles.append([short_id(x) for x in cycle])
            elif color[v] == WHITE:
                parent[v] = u
                dfs(v, stack + [v])
        color[u] = BLACK

    for n in nodes:
        if color[n] == WHITE:
            dfs(n, [n])

    # De-duplicate cycles.
    unique: list[list[str]] = []
    seen: set[tuple[str, ...]] = set()
    for c in cycles:
        key = tuple(c)
        if key not in seen:
            seen.add(key)
            unique.append(c)
    return unique


def main() -> int:
    print(f"[owl_consistency_check] Loading KG from {KG_PATH}", file=sys.stderr)
    kg = load_kg(KG_PATH)
    entities = iter_entities(kg)
    entity_ids = {e["@id"] for e in entities}

    # Build graphs.
    mutex_edges, mutex_nodes = relation_graph(kg, "ex:mutexWith")
    depends_edges, depends_nodes = relation_graph(kg, "ex:dependsOn")
    equiv_edges, equiv_nodes = relation_graph(kg, "ex:equivalentTo")

    # mutexWith checks.
    mutex_sym_ok, mutex_sym_violations = check_symmetry("ex:mutexWith", mutex_edges, mutex_nodes)
    mutex_irr_ok, mutex_irr_violations = check_irreflexivity("ex:mutexWith", mutex_edges)

    # dependsOn cycle check.
    depends_cycles = detect_cycles("ex:dependsOn", depends_edges, depends_nodes)
    depends_ok = len(depends_cycles) == 0

    # equivalentTo checks.
    equiv_sym_ok, equiv_sym_violations = check_symmetry("ex:equivalentTo", equiv_edges, equiv_nodes)
    equiv_trans_ok, equiv_trans_violations = check_transitivity("ex:equivalentTo", equiv_edges, equiv_nodes)

    # Check dangling relation endpoints.
    dangling: list[str] = []
    for rel in kg.get("relations", []):
        subj = rel.get("ex:subject", "")
        obj = rel.get("ex:object", "")
        pred = rel.get("ex:predicate", "")
        if subj not in entity_ids:
            dangling.append(f"主体不存在: {short_id(subj)} ({short_id(pred)})")
        if obj not in entity_ids:
            dangling.append(f"客体不存在: {short_id(obj)} ({short_id(pred)})")

    overall_ok = (
        mutex_sym_ok
        and mutex_irr_ok
        and depends_ok
        and equiv_sym_ok
        and equiv_trans_ok
        and not dangling
    )

    # Build report.
    lines: list[str] = [
        "# OWL 2 一致性检查报告",
        "",
        f"- 生成时间：{datetime.now().isoformat(timespec='seconds')}",
        f"- 知识图谱：{KG_PATH}",
        f"- 实体总数：{len(entities)}",
        "",
        f"## 总体结果：{'✅ 通过' if overall_ok else '❌ 失败'}",
        "",
        "| 检查项 | 状态 | 说明 |",
        "| --- | --- | --- |",
        f"| mutexWith 对称性 | {'✅' if mutex_sym_ok else '❌'} | {len(mutex_sym_violations)} 条违反 |",
        f"| mutexWith 反自反性 | {'✅' if mutex_irr_ok else '❌'} | {len(mutex_irr_violations)} 条违反 |",
        f"| dependsOn 无环性 | {'✅' if depends_ok else '❌'} | {len(depends_cycles)} 个环 |",
        f"| equivalentTo 对称性 | {'✅' if equiv_sym_ok else '❌'} | {len(equiv_sym_violations)} 条违反 |",
        f"| equivalentTo 传递性 | {'✅' if equiv_trans_ok else '❌'} | {len(equiv_trans_violations)} 条缺失 |",
        f"| 关系端点存在性 | {'✅' if not dangling else '❌'} | {len(dangling)} 条悬空 |",
        "",
    ]

    def section(title: str, items: list[str]) -> None:
        lines.append(f"## {title}")
        lines.append("")
        if items:
            for item in items:
                lines.append(f"- {item}")
        else:
            lines.append("✅ 无问题。")
        lines.append("")

    section("mutexWith 对称性违反", mutex_sym_violations)
    section("mutexWith 反自反性违反", mutex_irr_violations)

    lines.extend([
        "## dependsOn 循环依赖",
        "",
    ])
    if depends_cycles:
        for cycle in depends_cycles:
            lines.append(f"- {' -> '.join(cycle)}")
    else:
        lines.append("✅ 未发现 dependsOn 循环依赖。")
    lines.append("")

    section("equivalentTo 对称性违反", equiv_sym_violations)
    section("equivalentTo 传递性缺失", equiv_trans_violations)
    section("关系端点悬空", dangling)

    lines.extend([
        "## 检查方法说明",
        "",
        "1. **对称性**：对每条 `A R B`，检查是否存在 `B R A`。",
        "2. **反自反性**：检查是否存在 `A R A` 的自环。",
        "3. **传递性**：计算传递闭包，检查所有 `A R C` 是否已在图中显式声明。",
        "4. **无环性**：使用 DFS 检测有向图中的环。",
        "5. **端点存在性**：检查关系的主体/客体是否都在实体列表中。",
        "",
    ])

    report = "\n".join(lines)
    REPORT_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(REPORT_PATH, "w", encoding="utf-8") as f:
        f.write(report)

    print(report)
    print(f"[owl_consistency_check] Report written to {REPORT_PATH}", file=sys.stderr)
    return 0 if overall_ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
