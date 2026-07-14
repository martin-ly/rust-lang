#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""KG v3 关系语义精化 Phase 2：进一步压低 ex:relatedTo 到 <20%。

在 `scripts/refine_kg_relations.py` 的 R0-R5 基础上，针对残留的 1559 条
ex:relatedTo 增加高置信度精化规则 R6-R12：

  R6   index→meta hasPart         SUMMARY/README/atlas/navigation 指向 00_meta 内
                                  非索引/非映射页 → hasPart
  R6b  index→mapping hasPart      索引页指向 roadmap/gap_and_action_plan 等 mapping 页 → hasPart
  R7   atlas-hub→atlas hasPart    00_meta/knowledge_topology/01_concept_definition_atlas.md
                                  指向同目录 02-09 atlas 页 → hasPart
  R8   hub→content hasPart        同目录同层内容页：00_*_knowledge_map.md 或 01_* 概览
                                  指向更高编号内容页 → hasPart
  R9   quiz appliesTo             同目录同层测验页指向非测验概念页 → appliesTo
  R10  L0 atlas adjacent refines  00_meta/knowledge_topology/ 内相邻编号 atlas 文件 → refines
  R11  curated appliesTo          人工策展的技术/概念 → 领域 appliesTo（仅重标现存 relatedTo）
  R12  cross-layer README entails 跨层 README.md → README.md（低层→高层）→ entails

约束：
  - 不新增 partOf 逆关系；
  - 不新增 dependsOn，因此不会破坏 dependsOn 有向无环性；
  - 不动 mutexWith；
  - 仅当 (subject,object) 当前为 ex:relatedTo 时才重标，避免覆盖已有精确谓词。

输出：
  - concept/00_meta/kg_data_v3.json（写回，--dry-run 时跳过）
  - reports/KG_RELATION_REFINEMENT_PHASE2_<date>.{md,json}

用法：
  python scripts/refine_kg_relations_phase2.py [--dry-run] [--date YYYY-MM-DD]
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONCEPT = ROOT / "concept"
KG_PATH = CONCEPT / "00_meta" / "kg_data_v3.json"

PRED_REL = "ex:relatedTo"
PRED_DEP = "ex:dependsOn"
PRED_ENT = "ex:entails"
PRED_MUTEX = "ex:mutexWith"
PRED_CEX = "ex:counterExample"
PRED_REF = "ex:refines"
PRED_EQ = "ex:equivalentTo"
PRED_INST = "ex:instanceOf"
PRED_APP = "ex:appliesTo"
PRED_HASPART = "ex:hasPart"
PRED_PARTOF = "ex:partOf"


# ---------------------------------------------------------------------------
# 工具函数
# ---------------------------------------------------------------------------


def source_kind(path: str) -> str:
    name = Path(path).name.lower()
    parent = Path(path).parent.name.lower()
    if name == "summary.md":
        return "summary"
    if name == "readme.md":
        return "readme"
    if "atlas" in name:
        return "atlas"
    if "navigation" in name or name in {
        "learning_mvp_path.md",
        "concept_index.md",
        "foundations_gap_closure_index.md",
        "boundary_extension_tree.md",
    }:
        return "navigation"
    if "mapping" in name or "roadmap" in name or "gap_and_action_plan" in name:
        return "mapping"
    if path.startswith("00_meta/"):
        return "meta"
    return "content"


def is_index_like(path: str) -> bool:
    return source_kind(path) in {"summary", "readme", "atlas", "navigation", "mapping"}


def entity_layer(path: str) -> int:
    m = re.match(r"(\d\d)_", path.split("/")[0])
    return int(m.group(1)) if m else 0


def file_number(name: str) -> int | None:
    m = re.match(r"(\d\d)_", name)
    return int(m.group(1)) if m else None


# ---------------------------------------------------------------------------
# R11：人工策展 appliesTo（仅当 (s,o) 当前为 relatedTo 时重标）
# ---------------------------------------------------------------------------

CURATED_APPLIES: list[tuple[str, str, str]] = [
    ("ex:MicroservicePatterns", "ex:DistributedSystems",
     "06_ecosystem/03_design_patterns/05_microservice_patterns.md 微服务模式应用于分布式系统"),
    ("ex:EventDrivenArchitecture", "ex:CloudNative",
     "06_ecosystem/03_design_patterns/06_event_driven_architecture.md 事件驱动架构应用于云原生"),
    ("ex:CqrsEventSourcing", "ex:DistributedSystems",
     "06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md CQRS/事件溯源应用于分布式系统"),
    ("ex:CqrsEventSourcing", "ex:CloudNative",
     "06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md CQRS/事件溯源应用于云原生"),
    ("ex:AdvancedWebAssemblyDevelopmentWithRust", "ex:WebAssembly",
     "06_ecosystem/11_domain_applications/17_webassembly_advanced.md 高级 WebAssembly 开发应用于 WebAssembly 领域"),
    ("ex:Robotics", "ex:EmbeddedSystems",
     "06_ecosystem/11_domain_applications/06_robotics.md 机器人开发应用于嵌入式系统"),
    ("ex:EmbeddedGraphicsDevelopmentWithRust", "ex:EmbeddedSystems",
     "06_ecosystem/11_domain_applications/07_embedded_graphics.md 嵌入式图形开发应用于嵌入式系统"),
    ("ex:GameEngineInternals", "ex:GameDevelopment",
     "06_ecosystem/11_domain_applications/15_game_engine_internals.md 游戏引擎内部机制应用于游戏开发"),
    ("ex:CrossPlatformConcurrency", "ex:Concurrency",
     "03_advanced/00_concurrency/04_cross_platform_concurrency.md 跨平台并发应用于并发领域"),
    ("ex:AsyncProcessManagementInRust", "ex:AsyncProgramming",
     "03_advanced/08_process_ipc/03_async_process_management.md 异步进程管理应用于异步编程"),
    ("ex:InterProcessCommunicationMechanismsInRust", "ex:Concurrency",
     "03_advanced/08_process_ipc/05_ipc_mechanisms.md 进程间通信机制应用于并发领域"),
    ("ex:DataEngineering", "ex:MachineLearningEcosystem",
     "06_ecosystem/11_domain_applications/05_data_engineering.md 数据工程应用于机器学习生态"),
    ("ex:ZeroCopyParsing", "ex:SafeAndEffectiveUnsafeRust",
     "03_advanced/06_low_level_patterns/02_zero_copy_parsing.md 零拷贝解析应用于 unsafe Rust 实践"),
]


# ---------------------------------------------------------------------------
# 主流程
# ---------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true", help="只输出报告，不写回 kg_data_v3.json")
    ap.add_argument("--date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    data = json.loads(KG_PATH.read_text(encoding="utf-8"))
    entities = data["entities"]
    relations = data["relations"]
    id_to_entity = {e["@id"]: e for e in entities}

    before = Counter(r["ex:predicate"] for r in relations)

    def pair_key(r: dict) -> tuple[str, str]:
        return (r["ex:subject"], r["ex:object"])

    def find_rel(s: str, o: str, pred: str):
        for r in relations:
            if r["ex:subject"] == s and r["ex:object"] == o and r["ex:predicate"] == pred:
                return r
        return None

    changes: list[dict] = []

    def add_change(rule: str, action: str, r: dict, evidence: str, old: str = PRED_REL) -> None:
        changes.append({
            "rule": rule,
            "action": action,
            "subject": r["ex:subject"],
            "predicate": r["ex:predicate"],
            "object": r["ex:object"],
            "old_predicate": old,
            "evidence": evidence,
        })

    def retype_to(r: dict, pred: str, rule: str, evidence: str, confidence: float) -> None:
        r["ex:predicate"] = pred
        r["ex:evidence"] = evidence
        r["ex:rule"] = rule
        r["ex:confidence"] = confidence
        r["ex:reviewed"] = True
        if "ex:source" not in r or not r["ex:source"]:
            r["ex:source"] = f"refined:{rule}"
        add_change(rule, "retyped relatedTo", r, evidence)

    # =====================================================================
    # R11：策展 appliesTo（最先执行，避免被更宽规则覆盖标签）
    # =====================================================================
    for s, o, ev in CURATED_APPLIES:
        if s not in id_to_entity or o not in id_to_entity:
            continue
        rel = find_rel(s, o, PRED_REL)
        if not rel:
            continue
        retype_to(rel, PRED_APP, "R11-curated-appliesTo", ev, 1.0)

    # =====================================================================
    # R12：跨层 README.md → README.md entails
    # =====================================================================
    for r in relations:
        if r["ex:predicate"] != PRED_REL:
            continue
        s, o = pair_key(r)
        if s not in id_to_entity or o not in id_to_entity:
            continue
        sp = id_to_entity[s].get("ex:path", "")
        op = id_to_entity[o].get("ex:path", "")
        if Path(sp).name.lower() != "readme.md" or Path(op).name.lower() != "readme.md":
            continue
        sl = entity_layer(sp)
        ol = entity_layer(op)
        if sl == 0 or ol == 0 or sl >= ol:
            continue
        retype_to(r, PRED_ENT, "R12-readme-entails",
                  f"跨层 README 导航：L{sl} {sp} → L{ol} {op}", 0.9)

    # =====================================================================
    # R9：quiz → 同目录非测验概念 appliesTo
    # =====================================================================
    for r in relations:
        if r["ex:predicate"] != PRED_REL:
            continue
        s, o = pair_key(r)
        if s not in id_to_entity or o not in id_to_entity:
            continue
        sp = id_to_entity[s].get("ex:path", "")
        op = id_to_entity[o].get("ex:path", "")
        sl = entity_layer(sp)
        ol = entity_layer(op)
        if Path(sp).parent != Path(op).parent or sl != ol or sl == 0:
            continue
        sname = Path(sp).name
        oname = Path(op).name
        if "quiz" not in sname.lower() or "quiz" in oname.lower():
            continue
        retype_to(r, PRED_APP, "R9-quiz-appliesTo",
                  f"测验 {sname} 应用于评估概念 {oname}", 0.9)

    # =====================================================================
    # R10：L0 atlas 相邻文件 refines
    # =====================================================================
    for r in relations:
        if r["ex:predicate"] != PRED_REL:
            continue
        s, o = pair_key(r)
        if s not in id_to_entity or o not in id_to_entity:
            continue
        sp = id_to_entity[s].get("ex:path", "")
        op = id_to_entity[o].get("ex:path", "")
        if not (sp.startswith("00_meta/knowledge_topology/") and op.startswith("00_meta/knowledge_topology/")):
            continue
        if "atlas" not in Path(sp).name.lower() or "atlas" not in Path(op).name.lower():
            continue
        sn = file_number(Path(sp).name)
        on = file_number(Path(op).name)
        if sn is None or on is None or abs(sn - on) != 1:
            continue
        retype_to(r, PRED_REF, "R10-atlas-adjacent-refines",
                  f"L0 atlas 相邻文件：{Path(sp).name} → {Path(op).name}", 0.85)

    # =====================================================================
    # R7：atlas hub → 同目录其他 atlas hasPart
    # =====================================================================
    hub_id = "ex:ConceptDefinitionAtlas"
    for r in relations:
        if r["ex:predicate"] != PRED_REL:
            continue
        s, o = pair_key(r)
        if s != hub_id or o not in id_to_entity:
            continue
        op = id_to_entity[o].get("ex:path", "")
        if not op.startswith("00_meta/knowledge_topology/"):
            continue
        oname = Path(op).name
        if "atlas" not in oname.lower() or oname.lower() == "01_concept_definition_atlas.md":
            continue
        on = file_number(oname)
        if on is None:
            continue
        retype_to(r, PRED_HASPART, "R7-atlas-hub-hasPart",
                  f"概念定义图谱包含专题图谱：01 → {on:02d}", 0.95)

    # =====================================================================
    # R8：目录内 hub → 内容页 hasPart
    # =====================================================================
    for r in relations:
        if r["ex:predicate"] != PRED_REL:
            continue
        s, o = pair_key(r)
        if s not in id_to_entity or o not in id_to_entity:
            continue
        sp = id_to_entity[s].get("ex:path", "")
        op = id_to_entity[o].get("ex:path", "")
        sl = entity_layer(sp)
        ol = entity_layer(op)
        if Path(sp).parent != Path(op).parent or sl != ol or sl == 0:
            continue
        sname = Path(sp).name
        oname = Path(op).name
        sn = file_number(sname)
        on = file_number(oname)
        if sn is None or on is None or on <= sn:
            continue
        is_hub = False
        if sname.startswith("00_") and "knowledge_map" in sname.lower():
            is_hub = True
        elif sn == 1:
            is_hub = True
        if not is_hub:
            continue
        retype_to(r, PRED_HASPART, "R8-hub-content-hasPart",
                  f"同目录同层概览/知识图谱 {sname} 包含子主题 {oname}", 0.85)

    # =====================================================================
    # R6：索引页 → 00_meta 内非索引/非映射页 hasPart
    # =====================================================================
    for r in relations:
        if r["ex:predicate"] != PRED_REL:
            continue
        s, o = pair_key(r)
        if s not in id_to_entity or o not in id_to_entity:
            continue
        sp = id_to_entity[s].get("ex:path", "")
        op = id_to_entity[o].get("ex:path", "")
        if not is_index_like(sp):
            continue
        if not op.startswith("00_meta/"):
            continue
        ok = source_kind(op)
        if ok in {"summary", "atlas", "mapping"}:
            continue
        retype_to(r, PRED_HASPART, "R6-index-meta-hasPart",
                  f"索引页 {Path(sp).name} 包含元数据页 {Path(op).name}", 0.9)

    # =====================================================================
    # R6b：索引页 → mapping/roadmap/gap_and_action_plan hasPart
    # =====================================================================
    for r in relations:
        if r["ex:predicate"] != PRED_REL:
            continue
        s, o = pair_key(r)
        if s not in id_to_entity or o not in id_to_entity:
            continue
        sp = id_to_entity[s].get("ex:path", "")
        op = id_to_entity[o].get("ex:path", "")
        if not is_index_like(sp):
            continue
        if source_kind(op) != "mapping":
            continue
        retype_to(r, PRED_HASPART, "R6b-index-mapping-hasPart",
                  f"索引页 {Path(sp).name} 包含映射/路线图 {Path(op).name}", 0.9)

    # =====================================================================
    # 后处理：元数据与报告
    # =====================================================================
    after = Counter(r["ex:predicate"] for r in relations)

    data["relations"] = relations
    meta = data.get("metadata")
    if isinstance(meta, dict):
        meta["relation_count"] = len(relations)
        meta["refined"] = args.date
        rules = set(meta.get("refinement_rules", []))
        rules.update([
            "R6-index-meta-hasPart",
            "R6b-index-mapping-hasPart",
            "R7-atlas-hub-hasPart",
            "R8-hub-content-hasPart",
            "R9-quiz-appliesTo",
            "R10-atlas-adjacent-refines",
            "R11-curated-appliesTo",
            "R12-readme-entails",
        ])
        meta["refinement_rules"] = sorted(rules)

    # 写回
    if not args.dry_run:
        KG_PATH.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")

    # 报告
    out_md = ROOT / "reports" / f"KG_RELATION_REFINEMENT_PHASE2_{args.date}.md"
    out_json = ROOT / "reports" / f"KG_RELATION_REFINEMENT_PHASE2_{args.date}.json"

    def dist_table(title: str, before: Counter, after: Counter) -> list[str]:
        keys = sorted(set(before) | set(after), key=lambda k: -after.get(k, 0))
        rows = [f"### {title}", "", "| 谓词 | 前 | 后 | Δ |", "|:---|---:|---:|---:|"]
        for k in keys:
            b, a = before.get(k, 0), after.get(k, 0)
            rows.append(f"| {k} | {b} | {a} | {a - b:+d} |")
        rows.append("")
        return rows

    total_before = sum(before.values())
    total_after = sum(after.values())
    rt_before = before.get(PRED_REL, 0)
    rt_after = after.get(PRED_REL, 0)

    lines = [
        "# KG 关系语义精化报告 Phase 2",
        "",
        f"**日期**: {args.date}  **模式**: {'dry-run（未写回）' if args.dry_run else '已写回 kg_data_v3.json'}",
        f"**实体数**: {len(entities)}  **关系数**: {total_before} → {total_after}",
        f"**改动数**: {len(changes)}",
        "",
        "## 目标",
        "",
        f"将 `ex:relatedTo` 占比从 {rt_before/total_before:.1%} 进一步压到 <20%。",
        f"精化后：`ex:relatedTo` = {rt_after} / {total_after} = **{rt_after/total_after:.1%}**",
        "",
        "## 规则",
        "",
        "| 规则 | 语义 | 说明 |",
        "|:---|:---|:---|",
        "| R6-index-meta-hasPart | hasPart | SUMMARY/README/atlas/navigation 指向 00_meta 内非索引/非映射页 |",
        "| R6b-index-mapping-hasPart | hasPart | 索引页指向 roadmap/gap_and_action_plan 等 mapping 页 |",
        "| R7-atlas-hub-hasPart | hasPart | 01_concept_definition_atlas.md 指向同目录 02-09 atlas |",
        "| R8-hub-content-hasPart | hasPart | 同目录同层：00_*_knowledge_map 或 01_* 概览指向更高编号内容 |",
        "| R9-quiz-appliesTo | appliesTo | 同目录同层测验页指向非测验概念页 |",
        "| R10-atlas-adjacent-refines | refines | 00_meta/knowledge_topology/ 内相邻编号 atlas 文件 |",
        "| R11-curated-appliesTo | appliesTo | 人工策展的技术/概念 → 领域对 |",
        "| R12-readme-entails | entails | 跨层 README.md → README.md（低层→高层） |",
        "",
        "## 谓词分布前后对比",
        "",
    ]
    lines += dist_table("全局 KG", before, after)
    lines += ["## 关键指标", "",
              f"- `ex:relatedTo` 占比：{rt_before/total_before:.1%} → {rt_after/total_after:.1%}",
              f"- `ex:relatedTo` 数量：{rt_before} → {rt_after} (Δ {rt_after - rt_before:+d})",
              f"- 新增/转换谓词：hasPart / refines / appliesTo / entails",
              "",
              "## 逐边改动摘要（前 200 条）",
              "",
              "| 规则 | 动作 | 主语 | 谓词 | 宾语 | 依据 |",
              "|:---|:---|:---|:---|:---|:---|"]
    for c in changes[:200]:
        ev = c["evidence"].replace("|", "\\|")[:200]
        lines.append(f"| {c['rule']} | {c['action']} | {c['subject']} | {c['predicate']} "
                     f"| {c['object']} | {ev} |")
    if len(changes) > 200:
        lines.append(f"| ... | ... | ... | ... | ... | 共 {len(changes)} 条，详见 JSON |")
    lines += ["", "## 机器可读", "",
                f"- JSON: `reports/KG_RELATION_REFINEMENT_PHASE2_{args.date}.json`"]

    report = {
        "date": args.date,
        "dry_run": args.dry_run,
        "phase": "phase2",
        "entities": len(entities),
        "relations_before": total_before,
        "relations_after": total_after,
        "changes": len(changes),
        "before": dict(before),
        "after": dict(after),
        "related_to_ratio_before": round(rt_before / total_before, 4),
        "related_to_ratio_after": round(rt_after / total_after, 4),
        "changes_detail": changes,
    }

    out_json.write_text(json.dumps(report, ensure_ascii=False, indent=2), encoding="utf-8")
    out_md.write_text("\n".join(lines), encoding="utf-8")

    print(f"[refine_kg_relations_phase2] dry_run={args.dry_run} changes={len(changes)}")
    print(f"  relatedTo: {rt_before}/{total_before} ({rt_before/total_before:.1%}) "
          f"→ {rt_after}/{total_after} ({rt_after/total_after:.1%})")
    print(f"  report: {out_md.relative_to(ROOT)}")

    if rt_after / total_after >= 0.20:
        print("WARNING: relatedTo ratio still >= 20%; further curation may be needed.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
