#!/usr/bin/env python3
"""plan_renumber_phase2.py — N1 阶段映射合成器（docs / knowledge / crates）。

读取 plan_renumber.py 生成的 auto 映射（tmp/renumber/mapping_*_auto.csv），
叠加本阶段人工裁定：
- docs/  顶层目录两位连续重编号（目录级行 dir_rename）+ 根散落文件归位
         （relocate）+ research_notes 147 个扁平文件分 8 组归子目录；
- knowledge/  01_fundamentals 教学顺序换号 + INDEX.md 保持原名；
- crates/  c07 viewNN/11_practical_examples 清理、c04 双 tier_02 合并、
         *_supplement/*_final/*_expanded 变体标记（variant_merge_review）。

本脚本**只写 tmp/renumber/*.csv 与统计 JSON**，不移动任何文件、不执行 git。

用法：
    python scripts/plan_renumber_phase2.py
"""

from __future__ import annotations

import csv
import json
import posixpath
import re
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
OUT_DIR = REPO_ROOT / "tmp" / "renumber"

LEADING_NUM_RE = re.compile(r"^(\d+)_")

# ---------------------------------------------------------------------------
# docs/ 目录重编号裁定（2026-07-12 用户确认：不改结构，只改编号使顶层连续）
# ---------------------------------------------------------------------------
# 顶层：00_meta/01_core 保持不变；其余重排为两位连续不撞号。
DOCS_TOP_DIR_MAP = [
    ("docs/01_learning", "docs/02_learning"),
    ("docs/02_reference", "docs/03_reference"),
    ("docs/03_guides", "docs/04_guides"),
    ("docs/03_practice", "docs/05_practice"),
    ("docs/04_research", "docs/06_research"),
    ("docs/04_thinking", "docs/07_thinking"),
    ("docs/05_guides", "docs/08_guides"),
    ("docs/06_toolchain", "docs/09_toolchain"),
    ("docs/07_future", "docs/10_future"),
    ("docs/07_project", "docs/11_project"),
    ("docs/research_notes", "docs/12_research_notes"),
    ("docs/templates", "docs/13_templates"),
    ("docs/content", "docs/14_content"),
    ("docs/rust-formal-engineering-system", "docs/15_rust_formal_engineering_system"),
]
# research_notes 内部子目录重编号（含 formal_modules 改名消除同义歧义）
RN_SUB_DIR_MAP = [
    ("docs/research_notes/formal_methods", "docs/12_research_notes/02_formal_methods"),
    ("docs/research_notes/formal_modules", "docs/12_research_notes/04_formal_module_system"),
    ("docs/research_notes/type_theory", "docs/12_research_notes/05_type_theory"),
    ("docs/research_notes/software_design_theory", "docs/12_research_notes/08_software_design_theory"),
    ("docs/research_notes/experiments", "docs/12_research_notes/09_experiments"),
]
# software_design_theory 内部同号/跳号子目录重排
SDT_DIR_MAP = [
    ("docs/research_notes/software_design_theory/02_workflow_safe_complete_models",
     "docs/12_research_notes/08_software_design_theory/03_workflow_safe_complete_models"),
    ("docs/research_notes/software_design_theory/03_execution_models",
     "docs/12_research_notes/08_software_design_theory/04_execution_models"),
    ("docs/research_notes/software_design_theory/04_compositional_engineering",
     "docs/12_research_notes/08_software_design_theory/05_compositional_engineering"),
    ("docs/research_notes/software_design_theory/05_boundary_system",
     "docs/12_research_notes/08_software_design_theory/06_boundary_system"),
    ("docs/research_notes/software_design_theory/05_distributed",
     "docs/12_research_notes/08_software_design_theory/07_distributed"),
    ("docs/research_notes/software_design_theory/07_crate_architectures",
     "docs/12_research_notes/08_software_design_theory/08_crate_architectures"),
]
# rust-formal-engineering-system 内部同号/跳号子目录重排
RFES_DIR_MAP = [
    ("docs/rust-formal-engineering-system/02_practical_applications",
     "docs/15_rust_formal_engineering_system/03_practical_applications"),
    ("docs/rust-formal-engineering-system/03_compiler_theory",
     "docs/15_rust_formal_engineering_system/04_compiler_theory"),
    ("docs/rust-formal-engineering-system/03_design_patterns",
     "docs/15_rust_formal_engineering_system/05_design_patterns"),
    ("docs/rust-formal-engineering-system/05_software_engineering",
     "docs/15_rust_formal_engineering_system/06_software_engineering"),
    ("docs/rust-formal-engineering-system/06_toolchain_ecosystem",
     "docs/15_rust_formal_engineering_system/07_toolchain_ecosystem"),
    ("docs/rust-formal-engineering-system/09_research_agenda",
     "docs/15_rust_formal_engineering_system/08_research_agenda"),
    ("docs/rust-formal-engineering-system/10_quality_assurance",
     "docs/15_rust_formal_engineering_system/09_quality_assurance"),
]
# 全部目录映射（用于把 auto 行的 new_path 目录前缀改写为新位置），长前缀优先
ALL_DIR_MAP = sorted(
    RFES_DIR_MAP + SDT_DIR_MAP + RN_SUB_DIR_MAP + DOCS_TOP_DIR_MAP,
    key=lambda kv: -len(kv[0]),
)
# 需要写入 CSV 的目录级行（old != new 的全部）
DIR_ROWS = [(o, n) for o, n in ALL_DIR_MAP if o != n]


def apply_dir_map(path: str) -> str:
    for old, new in ALL_DIR_MAP:
        if path == old or path.startswith(old + "/"):
            return new + path[len(old):]
    return path


def read_rows(p: Path) -> list[dict]:
    with p.open(encoding="utf-8", newline="") as fh:
        return list(csv.DictReader(fh))


def write_rows(p: Path, rows: list[dict]) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=("old_path", "new_path", "reason", "order_in_dir"))
        w.writeheader()
        for r in sorted(rows, key=lambda r: (r["old_path"], r["new_path"])):
            w.writerow(r)


def used_nn_by_dir(rows: list[dict]) -> dict[str, set[int]]:
    used: dict[str, set[int]] = defaultdict(set)
    for r in rows:
        d = posixpath.dirname(r["new_path"])
        m = LEADING_NUM_RE.match(posixpath.basename(r["new_path"]))
        if m:
            used[d].add(int(m.group(1)))
    return used


def next_nn(used: dict[str, set[int]], d: str) -> int:
    nn = 1
    while nn in used[d]:
        nn += 1
    used[d].add(nn)
    return nn


# ---------------------------------------------------------------------------
# docs/ 根散落文件归位（依据 tmp/docs_root_files_classification.md N0 登记）
# new_slug 为去掉旧序号后的规范名；NN 在目标目录内追加。
# ---------------------------------------------------------------------------
ROOT_RELOCATE = [
    ("docs/00_master_index.md", "docs/00_meta", "master_index.md"),
    ("docs/01_cargo_build_optimization.md", "docs/09_toolchain", "cargo_build_optimization.md"),
    ("docs/01_nix_setup.md", "docs/09_toolchain", "nix_setup.md"),
    ("docs/04_rust_language_feature_comprehensive_inventory_2026.md", "docs/06_research",
     "rust_language_feature_comprehensive_inventory_2026.md"),
    ("docs/05_miri_integration_summary.md", "docs/09_toolchain", "miri_integration_summary.md"),
    ("docs/06_docker_guide.md", "docs/08_guides", "docker_guide.md"),
    ("docs/10_2026_rust_ecosystem_comprehensive_review_with_citations.md", "docs/06_research",
     "rust_ecosystem_comprehensive_review_2026.md"),
    ("docs/10_api_guide.md", "docs/04_guides", "api_guide.md"),
    ("docs/10_architecture.md", "docs/11_project", "architecture.md"),
    ("docs/10_authoritative_sources_and_citations.md", "docs/00_meta",
     "authoritative_sources_and_citations.md"),
    ("docs/10_dependency_graph.md", "docs/11_project", "dependency_graph.md"),
    ("docs/10_deployment.md", "docs/08_guides", "deployment.md"),
    ("docs/10_migration_guide_2026.md", "docs/04_guides", "migration_guide_2026.md"),
    ("docs/10_miri_guide.md", "docs/09_toolchain", "miri_guide.md"),
    ("docs/10_sccache_setup.md", "docs/09_toolchain", "sccache_setup.md"),
    ("docs/10_terminology_standard.md", "docs/00_meta", "terminology_standard.md"),
    # link_check_report.md 为机器生成报告 → reports/（见计划文档备注）
    ("docs/link_check_report.md", "reports", "link_check_report.md"),
    ("docs/trpl_3rd_ed_diff.md", "docs/03_reference", "trpl_3rd_ed_diff.md"),
]

# ---------------------------------------------------------------------------
# research_notes 147 个扁平 10_ 文件 → 8 个新子目录（关键词分类）
# ---------------------------------------------------------------------------
RN_NEW_DIRS = {
    "alignment": "docs/12_research_notes/01_alignment_matrices",
    "formal": "docs/12_research_notes/03_formal_proofs",
    "concept": "docs/12_research_notes/06_concept_models",
    "distributed": "docs/12_research_notes/07_distributed_and_workflow",
    "guides": "docs/12_research_notes/10_tutorials_and_guides",
    "cheatsheets": "docs/12_research_notes/11_cheatsheets",
    "version": "docs/12_research_notes/12_version_research",
    "meta": "docs/12_research_notes/13_meta_reports",
}

FORMAL_PREFIXES = (
    "formal_", "proof_", "theorem", "core_theorems", "core_features_full_chain",
    "const_eval", "coq_", "aeneas", "rustsem", "language_semantics",
    "safe_decidable", "safe_unsafe", "l3_machine", "executable_semantics",
    "international_formal", "verification_tools", "concept_axiom",
    "counter_examples", "rfc_to_counterexample", "version_evolution_counterexamples",
)
CONCEPT_PREFIXES = (
    "concept_", "design_mechanism", "domain_analysis", "cognitive_argumentation",
    "argumentation_", "theoretical_and_argumentation", "unified_systematic",
    "hierarchical_mapping", "cross_reference", "knowledge_graph",
    "ownership_concept_mindmap", "application_trees", "visualization_index",
    "system_integration", "code_doc_formal_mapping",
)
GUIDE_PREFIXES = (
    "faq", "learning_path", "interview", "quick_", "resources", "glossary",
    "best_practices", "practical_applications", "research_methodology",
    "advanced_data_structures", "algorithm_exercises", "cache_eviction",
    "lock_free", "tools_guide", "user_guide",
)


def classify_rn(slug: str) -> str:
    """slug = 去掉 10_ 前缀的文件名。返回 RN_NEW_DIRS 的 key。"""
    if "cheatsheet" in slug:
        return "cheatsheets"
    if slug.startswith("tutorial_"):
        return "guides"
    if slug == "i18n_translation_gap_analysis.md":
        return "meta"
    if "alignment" in slug or slug.startswith(("rfc_", "authoritative", "i18n_")):
        return "alignment"
    if slug.startswith(FORMAL_PREFIXES):
        return "formal"
    if slug.startswith(("distributed_", "workflow_")):
        return "distributed"
    if slug.startswith("rust_19"):
        return "version"
    if slug.startswith(CONCEPT_PREFIXES):
        return "concept"
    if slug.startswith(GUIDE_PREFIXES) or "_guide" in slug:
        return "guides"
    return "meta"


def build_docs() -> tuple[list[dict], dict]:
    auto = read_rows(OUT_DIR / "mapping_docs_auto.csv")

    # research_notes 扁平文件（直接位于 research_notes/ 下的 10_*.md）
    rn_flat = [r for r in auto
               if posixpath.dirname(r["old_path"]) == "docs/research_notes"
               and posixpath.basename(r["old_path"]).startswith("10_")]
    rn_flat_olds = {r["old_path"] for r in rn_flat}
    drop_olds = {o for o, _, _ in ROOT_RELOCATE} | rn_flat_olds
    drop_olds.add("docs/research_notes/00_archive_link_audit_report.md")

    kept: list[dict] = []
    for r in auto:
        if r["old_path"] in drop_olds:
            continue
        r = dict(r)
        r["new_path"] = apply_dir_map(r["new_path"])
        kept.append(r)

    # 目录级行
    for old_d, new_d in DIR_ROWS:
        kept.append(dict(old_path=old_d, new_path=new_d,
                         reason="dir_rename", order_in_dir=""))

    used = used_nn_by_dir(kept)

    # 根散落文件归位
    for old, tgt_dir, slug in ROOT_RELOCATE:
        nn = next_nn(used, tgt_dir)
        kept.append(dict(old_path=old, new_path=f"{tgt_dir}/{nn:02d}_{slug}",
                         reason="relocate", order_in_dir=str(nn)))

    # research_notes 扁平文件分组
    groups: dict[str, list[tuple[str, str]]] = defaultdict(list)  # key -> [(old, slug)]
    rn_special: list[dict] = []
    for r in sorted(rn_flat, key=lambda r: r["old_path"]):
        name = posixpath.basename(r["old_path"])[len("10_"):]
        if name == "00_organization_and_navigation.md":
            rn_special.append(dict(old_path=r["old_path"],
                                   new_path="docs/12_research_notes/00_organization_and_navigation.md",
                                   reason="relocate", order_in_dir="0"))
            continue
        if name == "00_comprehensive_summary.md":
            groups["meta"].append((r["old_path"], "comprehensive_summary.md"))
            continue
        groups[classify_rn(name)].append((r["old_path"], name))
    # 00_archive_link_audit_report → meta_reports
    groups["meta"].append(("docs/research_notes/00_archive_link_audit_report.md",
                           "archive_link_audit_report.md"))
    for key, items in groups.items():
        tgt_dir = RN_NEW_DIRS[key]
        for old, slug in sorted(items, key=lambda t: t[1]):
            nn = next_nn(used, tgt_dir)
            kept.append(dict(old_path=old, new_path=f"{tgt_dir}/{nn:02d}_{slug}",
                             reason="relocate", order_in_dir=str(nn)))
    kept.extend(rn_special)

    stats = {
        "total_rows": len(kept),
        "dir_rows": len(DIR_ROWS),
        "relocate_root": len(ROOT_RELOCATE),
        "relocate_rn_flat": sum(len(v) for v in groups.values()) + len(rn_special),
        "rn_group_sizes": {k: len(v) for k, v in sorted(groups.items())},
    }
    return kept, stats


# ---------------------------------------------------------------------------
# knowledge/
# ---------------------------------------------------------------------------
def build_knowledge() -> tuple[list[dict], dict]:
    auto = read_rows(OUT_DIR / "mapping_knowledge_auto.csv")
    rows: list[dict] = []
    swap = {
        "knowledge/01_fundamentals/01_borrowing.md": ("knowledge/01_fundamentals/02_borrowing.md", "2"),
        "knowledge/01_fundamentals/02_iterators.md": ("knowledge/01_fundamentals/04_iterators.md", "4"),
        "knowledge/01_fundamentals/04_ownership.md": ("knowledge/01_fundamentals/01_ownership.md", "1"),
    }
    for r in auto:
        r = dict(r)
        old = r["old_path"]
        if old == "knowledge/INDEX.md":
            r["new_path"] = old
            r["reason"] = "unchanged"
            r["order_in_dir"] = ""
        elif old in swap:
            r["new_path"], r["order_in_dir"] = swap[old]
            r["reason"] = "collision_resolve"
        rows.append(r)
    changed = sum(1 for r in rows if r["old_path"] != r["new_path"])
    return rows, {"total_rows": len(rows), "changed": changed}


# ---------------------------------------------------------------------------
# crates/
# ---------------------------------------------------------------------------
VARIANT_RE = re.compile(r"_(supplement|final|expanded)\.md$")


def build_crates() -> tuple[list[dict], dict]:
    auto = [r for r in read_rows(OUT_DIR / "mapping_crates_auto.csv")
            if re.match(r"^crates/[^/]+/docs/", r["old_path"])]
    rows: list[dict] = []
    variant_flagged = 0
    c07_root = "crates/c07_process/docs"
    drop_olds: set[str] = set()
    extra: list[dict] = []

    # c07: 11_practical_examples/ 扁平化到 docs/ 根（11_practical_examples 非 tier 目录）
    pe_rows = [r for r in auto if r["old_path"].startswith(c07_root + "/11_practical_examples/")]
    drop_olds |= {r["old_path"] for r in pe_rows}
    # c04: 双 tier_02 → tier_02_applications/01_advanced_patterns.md 并入 tier_02_guides
    c04_merge_old = "crates/c04_generic/docs/tier_02_applications/01_advanced_patterns.md"
    drop_olds.add(c04_merge_old)

    for r in auto:
        if r["old_path"] in drop_olds:
            continue
        r = dict(r)
        base = posixpath.basename(r["new_path"])
        # c07 viewNN 散名 → 规范名并标记变体裁定
        m = re.match(r"^(\d+)_view(\d+)\.md$", base)
        if r["old_path"].startswith(c07_root + "/view") and m:
            r["new_path"] = posixpath.join(
                posixpath.dirname(r["new_path"]),
                f"{m.group(1)}_formal_analysis_view_{int(m.group(2)):02d}.md")
            r["reason"] = "variant_merge_review"
            variant_flagged += 1
        elif VARIANT_RE.search(base):
            r["reason"] = "variant_merge_review"
            variant_flagged += 1
        rows.append(r)

    used = used_nn_by_dir(rows)
    # c07 practical examples → 根目录连续 NN（保持 11→18 原顺序）
    for r in sorted(pe_rows, key=lambda r: posixpath.basename(r["old_path"])):
        slug = LEADING_NUM_RE.sub("", posixpath.basename(r["old_path"]))
        nn = next_nn(used, c07_root)
        extra.append(dict(old_path=r["old_path"],
                          new_path=f"{c07_root}/{nn:02d}_{slug}",
                          reason="relocate", order_in_dir=str(nn)))
    # c04 合并行
    nn = next_nn(used, "crates/c04_generic/docs/tier_02_guides")
    extra.append(dict(old_path=c04_merge_old,
                      new_path=f"crates/c04_generic/docs/tier_02_guides/{nn:02d}_advanced_patterns.md",
                      reason="relocate", order_in_dir=str(nn)))
    rows.extend(extra)

    changed = sum(1 for r in rows if r["old_path"] != r["new_path"])
    return rows, {"total_rows": len(rows), "changed": changed,
                  "variant_flagged": variant_flagged,
                  "relocate": len(extra)}


def main() -> int:
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    stats: dict = {}

    docs_rows, stats["docs"] = build_docs()
    write_rows(OUT_DIR / "mapping_docs.csv", docs_rows)

    kn_rows, stats["knowledge"] = build_knowledge()
    write_rows(OUT_DIR / "mapping_knowledge.csv", kn_rows)

    cr_rows, stats["crates"] = build_crates()
    write_rows(OUT_DIR / "mapping_crates.csv", cr_rows)

    # 全局校验：每个 CSV 内 new_path 唯一（unchanged 行自身除外冲突无意义，仍检查）
    for name, rows in (("docs", docs_rows), ("knowledge", kn_rows), ("crates", cr_rows)):
        seen: dict[str, str] = {}
        for r in rows:
            n = r["new_path"]
            if n in seen and seen[n] != r["old_path"]:
                print(f"ERROR [{name}]: new_path 冲突 {n}（{seen[n]} / {r['old_path']}）")
                return 2
            seen[n] = r["old_path"]
        # old_path 也必须唯一（一行一文件/目录）
        olds = [r["old_path"] for r in rows]
        if len(olds) != len(set(olds)):
            print(f"ERROR [{name}]: old_path 重复")
            return 2

    with (OUT_DIR / "phase2_stats.json").open("w", encoding="utf-8") as fh:
        json.dump(stats, fh, ensure_ascii=False, indent=2)
    print(json.dumps(stats, ensure_ascii=False, indent=2))
    print("[phase2] mapping_docs.csv / mapping_knowledge.csv / mapping_crates.csv 已生成")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
