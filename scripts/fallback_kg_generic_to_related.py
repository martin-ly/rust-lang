#!/usr/bin/env python3
"""把 KG v3 中未被语义谓词实例化脚本分类的 ex:RelationAnnotation 边
回退标记为 ex:relatedTo（弱语义兜底谓词）。

背景：scripts/apply_kg_semantic_predicates.py 处理全部批次后仍会残留少量
ex:RelationAnnotation（来自链接关系但缺少 atlas 符号或强前置/后置信号）。
按 AGENTS.md 与 schema 设计，ex:relatedTo 是导航/弱关联的兜底谓词，
因此将残留通用谓词统一降级为 ex:relatedTo，并附加证据说明。

用法：
    python scripts/fallback_kg_generic_to_related.py [--apply]

默认 dry-run；--apply 写回 concept/00_meta/kg_data_v3.json。
"""
from __future__ import annotations

import argparse
import datetime
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
KG_PATH = ROOT / "concept" / "00_meta" / "kg_data_v3.json"
REPORT_PATH = ROOT / "reports" / f"KG_FALLBACK_GENERIC_TO_RELATED_{datetime.date.today().isoformat().replace('-', '_')}.md"


def main() -> int:
    ap = argparse.ArgumentParser(description="Fallback generic KG relations to ex:relatedTo")
    ap.add_argument("--apply", action="store_true", help="写回 kg_data_v3.json（默认 dry-run）")
    args = ap.parse_args()

    kg = json.loads(KG_PATH.read_text(encoding="utf-8"))
    relations = kg.get("relations", [])
    changed = 0
    for r in relations:
        if r.get("@type") == "ex:RelationAnnotation":
            r["@type"] = "ex:relatedTo"
            r["ex:predicate"] = "ex:relatedTo"
            r.setdefault("ex:evidence", "fallback: residual generic RelationAnnotation retyped as weak semantic relatedTo during KG refresh")
            r.setdefault("ex:rule", "F1-fallback-to-relatedTo")
            r.setdefault("ex:confidence", 0.5)
            changed += 1

    report_lines = [
        "# KG 通用谓词回退报告\n",
        f"**日期**: {datetime.date.today().isoformat()}\n\n",
        f"- 回退关系数: {changed}\n",
        f"- 操作: 将 `ex:RelationAnnotation` 改为 `ex:relatedTo`（schema 兜底弱语义谓词）\n",
        "- 原因: apply_kg_semantic_predicates.py 全部批次处理后仍有残留通用谓词，\n",
        "  这些边缺乏 atlas 符号或强前置/后置信号，不宜强制指定为 dependsOn/entails/refines 等强谓词。\n",
    ]

    REPORT_PATH.write_text("".join(report_lines), encoding="utf-8")
    print(f"[fallback] changed={changed} residual ex:RelationAnnotation -> ex:relatedTo")
    print(f"[fallback] report: {REPORT_PATH}")

    if args.apply:
        KG_PATH.write_text(json.dumps(kg, ensure_ascii=False, indent=2), encoding="utf-8")
        print("[fallback] kg_data_v3.json 已写回")
    else:
        print("[fallback] dry-run：未写回 kg_data_v3.json（使用 --apply 执行）")

    return 0


if __name__ == "__main__":
    sys.exit(main())
