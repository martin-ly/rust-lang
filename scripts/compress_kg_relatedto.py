#!/usr/bin/env python3
"""把 KG v3 中大量无差别的 ex:relatedTo 边按启发式规则压缩为精确谓词。

启发式（按优先级，命中即定；每处改动附 ex:evidence / ex:rule / ex:confidence）：

  H1 hasPart        源为 SUMMARY.md / README.md / registry / index / atlas 导航页
                    → ex:hasPart（表示源页组织/包含目标概念）
  H2 partOf         目标是 SUMMARY.md / README.md / registry / index / atlas 导航页
                    → ex:partOf（表示源概念被目标页组织）
  H3 refines        源与目标在同一目录，且源文件序号 > 目标文件序号
                    → ex:refines（同主题进阶/细分）
  H4 dependsOn      源层 > 目标层（按 00_meta/01_foundation/.../07_future 的数值顺序）
                    → ex:dependsOn（高阶概念依赖基础概念）
  H5 entails        源层 < 目标层
                    → ex:entails（基础概念蕴含/导出高阶应用）
  H6 equivalentTo   源路径与目标路径相同（重复节点）或标题相同
                    → ex:equivalentTo

未命中任何规则的 relatedTo 保持原状（作为兜底弱语义边）。

用法：
    python scripts/compress_kg_relatedto.py [--apply]

默认 dry-run；--apply 写回 concept/00_meta/kg_data_v3.json。
"""
from __future__ import annotations

import argparse
import datetime
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
KG_PATH = ROOT / "concept" / "00_meta" / "kg_data_v3.json"
KG_INDEX_PATH = ROOT / "concept" / "00_meta" / "kg_index.json"
REPORT_PATH = ROOT / "reports" / f"KG_RELATEDTO_COMPRESSION_{datetime.date.today().isoformat().replace('-', '_')}.md"

# Directory order for layer inference
LAYER_ORDER = {
    "00_meta": 0,
    "01_foundation": 1,
    "02_intermediate": 2,
    "03_advanced": 3,
    "04_formal": 4,
    "05_comparative": 5,
    "06_ecosystem": 6,
    "07_future": 7,
}

INDEX_RE = re.compile(r"(SUMMARY\.md|README\.md|registry|index|atlas|navigation|mapping|glossary|roadmap|matrix)", re.I)
META_ORGANIZER_TERMS = [
    "framework", "roadmap", "taxonomy", "mindmap", "space", "matrix", "atlas",
    "glossary", "registry", "mapping", "theory", "guide", "checklist", "dashboard",
    "navigation", "index", "consistency", "audit", "terminology", "sources", "authority",
]


def is_meta_organizer(path: str, title: str | None) -> bool:
    low = (path + " " + (title or "")).lower()
    return any(t in low for t in META_ORGANIZER_TERMS)
NUM_RE = re.compile(r"(\d+)")


def layer_of(path: str) -> int:
    parts = path.split("/")
    return LAYER_ORDER.get(parts[0], -1)


def dir_of(path: str) -> str:
    parts = path.split("/")
    return "/".join(parts[:2]) if len(parts) >= 2 else parts[0]


def file_prefix(path: str) -> tuple[int, ...]:
    """Extract leading numeric sequences from filename for ordering."""
    name = Path(path).name
    nums = [int(n) for n in NUM_RE.findall(name)]
    return tuple(nums)


def is_index(path: str, en_title: str | None) -> bool:
    if INDEX_RE.search(path):
        return True
    if en_title and INDEX_RE.search(en_title):
        return True
    return False


def main() -> int:
    ap = argparse.ArgumentParser(description="Compress generic KG relatedTo edges to semantic predicates")
    ap.add_argument("--apply", action="store_true", help="写回 kg_data_v3.json（默认 dry-run）")
    args = ap.parse_args()

    kg = json.loads(KG_PATH.read_text(encoding="utf-8"))
    entities = {e["@id"]: e for e in kg.get("entities", [])}
    relations = kg.get("relations", [])

    # Load kg_index prerequisites/postrequisites for semantic signal
    prereq_map: dict[str, set[str]] = {}
    postreq_map: dict[str, set[str]] = {}
    try:
        idx = json.loads(KG_INDEX_PATH.read_text(encoding="utf-8"))
        for ent in idx.get("entities", []):
            eid = ent.get("id", "").replace("concept:", "ex:")
            # Convert relative paths in kg_index to absolute concept/ paths
            base_dir = str(Path(ent.get("path", "")).parent).replace("\\", "/")
            prereq_paths = set()
            for pre in ent.get("prerequisites", []):
                p = pre.get("path", "")
                if p.startswith("../") or p.startswith("./"):
                    prereq_paths.add(str((Path(ent["path"]).parent / p).resolve()).replace("\\", "/"))
                else:
                    prereq_paths.add(p)
            postreq_paths = set()
            for post in ent.get("postrequisites", []):
                p = post.get("path", "")
                if p.startswith("../") or p.startswith("./"):
                    postreq_paths.add(str((Path(ent["path"]).parent / p).resolve()).replace("\\", "/"))
                else:
                    postreq_paths.add(p)
            if eid:
                prereq_map[eid] = prereq_paths
                postreq_map[eid] = postreq_paths
    except FileNotFoundError:
        pass

    stats = {
        "hasPart": 0,
        "partOf": 0,
        "refines": 0,
        "dependsOn": 0,
        "entails": 0,
        "equivalentTo": 0,
        "appliesTo": 0,
        "unchanged": 0,
    }

    def target_path_matches(eid: str, target_path: str, path_set: set[str]) -> bool:
        # Match either exact path or normalized absolute path under concept/
        candidates = {target_path}
        if not target_path.startswith("concept/"):
            candidates.add(f"concept/{target_path}")
        else:
            candidates.add(target_path.replace("concept/", "", 1))
        return bool(candidates & path_set)

    for r in relations:
        if r.get("@type") != "ex:relatedTo":
            continue
        subject = r.get("ex:subject", "")
        obj = r.get("ex:object", "")
        subj_path = entities.get(subject, {}).get("ex:path", "")
        obj_path = entities.get(obj, {}).get("ex:path", "")
        subj_en = entities.get(subject, {}).get("ex:enTitle", "")
        obj_en = entities.get(obj, {}).get("ex:enTitle", "")

        new_type = None
        rule = None
        evidence = None
        confidence = 0.7

        # H0: any SUMMARY.md / README.md organizes its sibling concept space
        if subj_path and subj_path.split("/")[-1].lower() in ("summary.md", "readme.md"):
            new_type = "ex:hasPart"
            rule = "H0-readme-summary-hasPart"
            evidence = f"{subj_path} is a navigation/README page and organizes {obj_path}"
        elif is_index(subj_path, subj_en) and not is_index(obj_path, obj_en):
            new_type = "ex:hasPart"
            rule = "H1-index-hasPart"
            evidence = f"{subj_path} is a navigation/index page that organizes {obj_path}"
        elif not is_index(subj_path, subj_en) and is_index(obj_path, obj_en):
            new_type = "ex:partOf"
            rule = "H2-index-partOf"
            evidence = f"{subj_path} is categorized/organized by index page {obj_path}"
        elif subj_path and obj_path and subj_path == obj_path:
            new_type = "ex:equivalentTo"
            rule = "H6-same-path-equivalentTo"
            evidence = "same concept path treated as equivalent entity"
        elif subj_path and obj_path and dir_of(subj_path) == dir_of(obj_path):
            sp = file_prefix(subj_path)
            op = file_prefix(obj_path)
            if sp and op and sp > op:
                new_type = "ex:refines"
                rule = "H3-same-dir-refines"
                evidence = f"{subj_path} is a more specific/advanced topic in the same directory as {obj_path}"

        if new_type is None and is_meta_organizer(subj_path, subj_en) and not is_meta_organizer(obj_path, obj_en):
            new_type = "ex:hasPart"
            rule = "H7-meta-organizer-hasPart"
            evidence = f"{subj_path} is a meta/organizer page that references {obj_path}"

        if new_type is None and "quiz" in subj_path.lower() and "quiz" not in obj_path.lower():
            new_type = "ex:appliesTo"
            rule = "H8-quiz-appliesTo"
            evidence = f"quiz page {subj_path} applies to concept {obj_path}"

        if new_type is None:
            sl = layer_of(subj_path)
            ol = layer_of(obj_path)
            if sl >= 0 and ol >= 0 and sl != ol:
                if sl > ol:
                    new_type = "ex:dependsOn"
                    rule = "H4-higher-layer-dependsOn"
                    evidence = f"higher layer {subj_path.split('/')[0]} depends on lower layer {obj_path.split('/')[0]}"
                else:
                    new_type = "ex:entails"
                    rule = "H5-lower-layer-entails"
                    evidence = f"lower layer {subj_path.split('/')[0]} entails higher layer {obj_path.split('/')[0]}"

        # H12/H13: use kg_index prerequisites/postrequisites as strong semantic signal
        if new_type is None:
            pre_paths = prereq_map.get(subject, set())
            post_paths = postreq_map.get(subject, set())
            if target_path_matches(subject, obj_path, pre_paths):
                new_type = "ex:dependsOn"
                rule = "H12-prerequisite-dependsOn"
                evidence = f"{subj_path} lists {obj_path} as prerequisite in kg_index"
            elif target_path_matches(subject, obj_path, post_paths):
                new_type = "ex:entails"
                rule = "H13-postrequisite-entails"
                evidence = f"{subj_path} lists {obj_path} as postrequisite in kg_index"

        # H14/H15: meta-framework / atlas pages organize sub-meta pages
        META_ORGANIZER_DIRS = {
            "00_meta/00_framework",
            "00_meta/knowledge_topology",
        }
        META_SUB_DIRS = {
            "00_meta/01_terminology",
            "00_meta/02_sources",
            "00_meta/03_audit",
            "00_meta/04_navigation",
            "00_meta/05_quizzes",
            "00_meta/06_trpl_3rd_ed_mapping",
            "00_meta/07_placeholders",
        }
        if new_type is None and subj_path and obj_path:
            sd = "/".join(subj_path.split("/")[:2])
            od = "/".join(obj_path.split("/")[:2])
            if sd in META_ORGANIZER_DIRS and od in META_SUB_DIRS:
                new_type = "ex:hasPart"
                rule = "H14-meta-organizer-hasPart-subsystem"
                evidence = f"{subj_path} is a meta-framework/atlas that organizes subsystem {obj_path}"
            elif od in META_ORGANIZER_DIRS and sd in META_SUB_DIRS:
                new_type = "ex:partOf"
                rule = "H15-meta-subsystem-partOf-framework"
                evidence = f"{subj_path} is a subsystem that is part of meta-framework/atlas {obj_path}"

        if new_type:
            r["@type"] = new_type
            r["ex:predicate"] = new_type
            r.setdefault("ex:evidence", evidence)
            r.setdefault("ex:rule", rule)
            r.setdefault("ex:confidence", confidence)
            stats[new_type.replace("ex:", "")] += 1
        else:
            stats["unchanged"] += 1

    total_changed = sum(v for k, v in stats.items() if k != "unchanged")
    report_lines = [
        "# KG relatedTo 压缩报告\n",
        f"**日期**: {datetime.date.today().isoformat()}\n\n",
        "将无差别的 `ex:relatedTo` 按启发式规则迁移为精确谓词：\n\n",
        "| 谓词 | 数量 |\n",
        "|---|---:|\n",
    ]
    for k, v in stats.items():
        report_lines.append(f"| {k} | {v} |\n")
    report_lines.append(f"\n- 修改总数: {total_changed}\n")
    report_lines.append(f"- 未变更（仍 relatedTo）: {stats['unchanged']}\n")
    report_lines.append("\n规则说明：H1/H2 导航页 hasPart/partOf；H3 同目录进阶 refines；H4/H5 跨层 dependsOn/entails；H6 同路径 equivalentTo。\n")

    REPORT_PATH.write_text("".join(report_lines), encoding="utf-8")
    print(f"[compress] changed={total_changed} relatedTo -> precise predicates")
    print(f"[compress] unchanged={stats['unchanged']}")
    print(f"[compress] report: {REPORT_PATH}")

    if args.apply:
        KG_PATH.write_text(json.dumps(kg, ensure_ascii=False, indent=2), encoding="utf-8")
        print("[compress] kg_data_v3.json 已写回")
    else:
        print("[compress] dry-run：未写回 kg_data_v3.json（使用 --apply 执行）")

    return 0


if __name__ == "__main__":
    sys.exit(main())
