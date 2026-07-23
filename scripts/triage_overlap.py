#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""P1 前置：对 CONTENT_OVERLAP_V2 的命中对做分类（triage），产出可执行改写清单。

输入：reports/CONTENT_OVERLAP_V2_<date>.json（由 detect_content_overlap_v2.py 生成）
分类规则：
  SERIES  合理系列重复（保留但标注）：路径/标题含版本快照/分章（rust_1NN、readme_rust_、_partN、_vN、
          _19N、_comprehensive_enhancement_report 等），或同一 crate 的版本序列。
  MERGE   应合并近克隆：sim>=0.85 且非 SERIES（模板复制，如 design_patterns_formal 多 README）。
  DOCS_INTERNAL  docs/ 内同主题互抄：两文件都在 docs/ 且 sim>=0.7（指南/研究笔记间重复）。
  REVIEW  其余需人工复核。
输出：reports/OVERLAP_TRIAGE_<date>.{md,json}
"""
from __future__ import annotations

import argparse
import datetime as _dt
import glob
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

SERIES_RE = re.compile(
    r"rust_1\d{2,3}|rust_19\d|readme_rust_|_part\d|_v\d+|_19\d\d|20\d\d_\d\d_\d\d|"
    r"comprehensive_enhancement_report|examples_collection|snapshot", re.IGNORECASE)

# 显式 SERIES 白名单（人工复核登记的误报对；路径为仓库相对路径，正斜杠）。
# 登记格式：frozenset({file1, file2})，匹配时同时按完整路径与 basename 对判定（容忍 NN_ 重编号）。
SERIES_PAIRS = {
    # 复核 2026-07-24：1.99+ 与 1.100+ 版本跟踪页为同系列周期跟踪模板，内容差异化（版本号、
    # 日期、预计稳定时间、周期清单来源日期）随 nightly 滚动更新，非重复。
    frozenset({
        "concept/07_future/00_version_tracking/rust_1_99_preview.md",
        "concept/07_future/00_version_tracking/rust_1_100_preview.md",
    }),
    # 复核 2026-07-12：rust 1.90 网络示例分章文件（Part1/Part2），实测正文相似度 12.7%，
    # 内容为不同章节（基础示例 vs 进阶协议），非重复，保留分章结构。
    frozenset({
        "crates/c10_networks/docs/07_rust_190_examples_collection.md",
        "crates/c10_networks/docs/08_rust_190_examples_part2.md",
    }),
    # 复核 2026-07-12：c02_type_system 版本系列 README（rust 1.89 / 1.90），
    # 57% 独特内容（各自版本特性清单），属版本快照系列，保留。
    frozenset({
        "crates/c02_type_system/readme_rust_189.md",
        "crates/c02_type_system/readme_rust_190.md",
    }),
}

# 显式 SERIES 路径族白名单（人工复核登记的系列目录；两文件路径均命中同一正则时判 SERIES）。
# 登记格式：compiled regex，作用于仓库相对路径（正斜杠）。每条必须附复核证据注释。
SERIES_PATH_RE = [
    # 复核 2026-07-12：docs/05_practice 实践项目指南系列（04_project_03 … 16_project_15，共 48 对命中，
    # kw jaccard 0.71–0.82）。逐文件通读（每文件 86–135 行，全部读完 13 个命中文件的正文）：
    # 共享内容 = 统一模板骨架（目录/项目目标/功能需求/学习要点/参考实现/权威来源索引节 + Batch 8
    # 权威来源对齐页脚）；独特内容 = 各项目主题、功能需求清单与学习要点代码（递归下降解析 / 随机密码 /
    # 迭代器词频 / 多线程+异步下载 / TCP 聊天 / RwLock 缓存 / 流式日志 / 管道模式 / HTTP 解析 /
    # wasm-bindgen / B-Tree / 自定义 Future poll / Raft 状态机），无正文互抄。属同系列模板化结构，登记 SERIES。
    re.compile(r"docs/05_practice/\d\d_project_"),
    # 复核 2026-07-12：docs/12_research_notes/08_software_design_theory 子目录索引 README 系列
    # （01_design_patterns_formal 下 creational/structural/behavioral 三份 + 02_workflow + 07_distributed，
    # 共 4 对命中，kw jaccard 0.75–0.949）。逐文件通读（119–152 行/份）：共享 ~85% 为模板样板
    # （元数据头、Rust 1.94 深度整合节、权威来源索引、Batch 8 页脚）；独特内容为各目录模式清单与
    # 对齐状态表行（创建型 5 模式 / 结构型 7 模式 / 行为型 11 模式 / 工作流 3 模式 / 分布式 9 模式，
    # 清单互不重叠）。均为子目录导航索引，合并或 stub 化会破坏目录导航，登记 SERIES。
    re.compile(r"docs/12_research_notes/08_software_design_theory/(\d\d_[^/]+/)+README\.md"),
]

# ---------------------------------------------------------------------------
# REVIEWED 白名单（2026-07-12 批量复核加固，见 reports/OVERLAP_REVIEW_SWEEP_2026_07_12.md）。
# 语义：经人工分层复核确认非重复（stub/模板系列相似或同领域术语共现），登记后不再计入 REVIEW。
# 判定顺序在 MERGE / DOCS_INTERNAL 之后：docs/ 内 sim>=0.7 仍会进入 DOCS_INTERNAL（阻断），
# sim>=0.85 仍进入 MERGE（阻断），故本白名单不会掩盖高相似真重复。
# REVIEWED_PATH_RE： (rx1, rx2) 二元组，两文件路径分别命中 rx1/rx2（顺序无关）即判 REVIEWED。
# REVIEWED_PAIRS： 显式对（完整路径或 basename 对，容忍 NN_ 重编号）。每条必须附复核证据注释。
# ---------------------------------------------------------------------------
REVIEWED_PATH_RE = [
    # 复核 2026-07-12（族 A）：crates/*/docs/ 治理 stub 家族。0.5–0.9 三桶命中对全部落在 crate docs 内。
    # 逐文件核验：命中文件 48/50 为 ≤45 行 canonical 重定向 stub 或统一生成器 orientation stub
    # （"权威来源"+主题导航表，指向各自不同的 concept/ 权威页，如 03_lifetimes vs 04_lifetimes_advanced
    # vs 01_concurrency vs 01_control_flow vs 01_generics；或 "This file previously contained ... Per
    # AGENTS.md §6.4" 仅保留 Quick links；2026-07-12 权威覆盖扩展任务追加的「国际权威来源」节不改变
    # stub 性质）；唯一非 stub 对 c05/c06 tier_02_guides/07_hands_on_projects.md（sim 0.65）为项目模板相似：
    # 共享知识结构骨架（概念定义/属性特征/关系连接/思维导图节 + 项目说明/核心代码模板），
    # 正文独特内容 67%/61%（线程池/并发队列/生产者-消费者 vs 异步文件批处理/HTTP 客户端/任务调度器）。
    # 共享部分均为 stub/模板骨架，无概念正文互抄。登记 REVIEWED。
    (re.compile(r"crates/[^/]+(?:/[^/]+)?/docs/.+\.md$"),
     re.compile(r"crates/[^/]+(?:/[^/]+)?/docs/.+\.md$")),
    # 复核 2026-07-12（族 B）：knowledge/ 模块索引 README 模板家族（含与 content/ecosystem/deep_dives/
    # README.md 的交叉对），0.5–0.8 桶共 46 对。逐文件通读 9 个命中 README（72–139 行）：
    # 共享 = 模块索引模板（EN/Summary/Bloom/受众/内容分级头 + 📚内容表 + 🎯学习目标/前置要求 +
    # 🚀下一步 + Batch 8 权威来源对齐页脚 + 模块 8 国际化对齐节）；独特 = 各模块文档清单表、
    # 学习目标、检查清单（专家主题/生态工具/学术/Miri/部署/前沿特性/参考/入门 主题互不重叠）。
    # 无正文互抄，属学习入口索引模板相似。登记 REVIEWED。
    (re.compile(r"knowledge/.+\.md$"), re.compile(r"knowledge/.+\.md$")),
    (re.compile(r"knowledge/.+\.md$"),
     re.compile(r"content/ecosystem/deep_dives/README\.md$")),
    # 复核 2026-07-12（族 C+D）：docs/12_research_notes/ 研究笔记模板家族，0.5–0.7 桶共 271 对
    # （含 01_design_patterns_formal 三子目录 248 对、07_distributed 12 对、08_crate_architectures 4 对、
    # 03_formal_proofs/07_distributed_and_workflow/04_formal_module_system/02_formal_methods 交叉 19 对、
    # 10_tutorials_and_guides / 01_alignment_matrices 各 1 对）。抽样验证 14 对（每族 ≥2 对）：
    # - 设计模式形式化文档（800+ 行/份，State/Visitor/Mediator/Observer/AbstractFactory/Adapter/
    #   Builder/Bridge 等）：共享 ~60% 为形式化文档骨架（目录/权威来源对照/形式化定义/所有权约束分析/
    #   不变式规约/决策树节标题）+ Batch 8 来源页脚 + 代码围栏等排版行；去除排版行后正文独特内容
    #   38–58%，为各模式专属公理/定理/证明/代码（ST-T1 枚举穷尽 vs VI-T1 单分发完备，互不重叠）。
    # - 分布式模式（saga/cqrs/circuit_breaker/timeout/retry/outbox）：正文独特 39–50%，模式互不重叠。
    # - crate 架构分析（askama/maud/ort/tract）：正文独特 49–58%。
    # - 证明树（borrow/ownership/type_safety）：正文独特 41–52%，证明对象不同。
    # - 思维导图/决策树交叉对：共享为「Rust 1.94 深度整合更新」模板节 + 权威来源页脚 + TOC 锚点，
    #   主题各异（Coq 集成计划/形式化生态/分布式架构/异步运行时/工作流）。
    # - 10_tutorials 对为 AGENTS.md §4.3 学习入口 stub（借用检查器 vs 所有权安全，速查要点不同）。
    # 均为同系列模板化结构或同领域术语共现，无正文互抄。登记 REVIEWED。
    # 注意：本族登记在 DOCS_INTERNAL 之后，docs/ 内 sim>=0.7 仍阻断，不受此豁免。
    (re.compile(r"docs/12_research_notes/.+\.md$"),
     re.compile(r"docs/12_research_notes/.+\.md$")),
]

REVIEWED_PAIRS = {
    # 复核 2026-07-23（族 J）：crates/c02_type_system 两个 stub 入口页（sim 0.526）。
    # best_practices_guide.md（28 行）与 tutorial_guide.md（38 行）均为 AGENTS.md §2/§6.4 规范的
    # crate 学习/最佳实践入口 stub，正文仅含「权威来源」重定向块 + 主题导航表 + 实践入口说明。
    # 共享内容为 stub 模板骨架；独特内容为各自主题导航目标（基础/泛型/trait/错误处理 vs
    # 高级类型/GAT/TAIT/生命周期/模式匹配/异步）。非概念正文互抄，登记 REVIEWED。
    frozenset({
        "crates/c02_type_system/best_practices_guide.md",
        "crates/c02_type_system/tutorial_guide.md",
    }),
    # 复核 2026-07-12（族 E）：concept 网络域同领域术语共现（sim 0.500）。逐文件比对（747 vs 886 行）：
    # 06_websocket 主题为 WebSocket 应用协议（握手/tokio-tungstenite/聊天室实战），
    # 05_networking_basics 主题为 TCP/IP 网络基础；正文独特内容 64%/67%，
    # 共享为 concept 权威页元数据头模板 + 网络领域通用术语。非重复，登记 REVIEWED。
    frozenset({
        "concept/06_ecosystem/04_web_and_networking/06_websocket_realtime_communication.md",
        "concept/06_ecosystem/12_networking/05_networking_basics.md",
    }),
    # 复核 2026-07-12（族 F）：content/safety_critical 同套件跨主题（sim 0.522）。
    # 08_glossary_and_definitions（术语表，119 行）vs 02_rust_ecosystem_mind_map（思维导图，99 行）：
    # 正文独特 69%/56%，共享为安全关键套件通用术语（ISO 26262/内存安全等）与元数据头。非重复。
    frozenset({
        "content/safety_critical/09_reference/08_glossary_and_definitions.md",
        "content/safety_critical/01_mind_maps/02_rust_ecosystem_mind_map.md",
    }),
    # 复核 2026-07-12（族 G）：docs/15_rust_formal_engineering_system 子主题索引（sim 0.510）。
    # 01_type_system/README（257 行）vs 03_ownership_borrowing/README（331 行）：
    # 共享为形式化工程系统统一章节模板；正文独特 66%/70%（类型系统 vs 所有权借用 主题清单互不重叠）。
    frozenset({
        "docs/15_rust_formal_engineering_system/01_theoretical_foundations/01_type_system/README.md",
        "docs/15_rust_formal_engineering_system/01_theoretical_foundations/03_ownership_borrowing/README.md",
    }),
    # 复核 2026-07-17（族 H）：content/safety_critical 套件目录索引与 README（sim 0.500）。
    # 02_rust_safety_critical_ecosystem_master_index.md（目录内文件清单索引）vs README.md（套件使用指南与角色路径）：
    # 共享为目录结构列表；正文独特 80%+（master_index 为文件清单，README 为使用指南/统计/标准覆盖）。
    # 两者功能不同，属同一专题套件的导航骨架共现，非重复。
    frozenset({
        "content/safety_critical/02_rust_safety_critical_ecosystem_master_index.md",
        "content/safety_critical/README.md",
    }),
    # 复核 2026-07-17（族 I）：concept/SUMMARY.md 与属性关系图谱（sim 0.500）。
    # SUMMARY.md 为 mdBook 目录导航清单；02_attribute_relationship_atlas.md 为概念属性矩阵。
    # 共享为概念文件列表与元数据头模板；正文独特 90%+（目录 vs 属性矩阵）。非重复。
    frozenset({
        "concept/SUMMARY.md",
        "concept/00_meta/knowledge_topology/02_attribute_relationship_atlas.md",
    }),
}


def _in_reviewed_pairs(f1: str, f2: str) -> bool:
    f1, f2 = _norm(f1), _norm(f2)
    if frozenset({f1, f2}) in REVIEWED_PAIRS:
        return True
    b1, b2 = f1.rsplit("/", 1)[-1], f2.rsplit("/", 1)[-1]
    for pair in REVIEWED_PAIRS:
        bases = {p.rsplit("/", 1)[-1] for p in pair}
        if frozenset({b1, b2}) == bases:
            return True
    return False


def _in_reviewed_path_family(f1: str, f2: str) -> bool:
    f1, f2 = _norm(f1), _norm(f2)
    for rx1, rx2 in REVIEWED_PATH_RE:
        if (rx1.search(f1) and rx2.search(f2)) or (rx1.search(f2) and rx2.search(f1)):
            return True
    return False


def is_reviewed(o):
    return _in_reviewed_pairs(o["f1"], o["f2"]) or _in_reviewed_path_family(o["f1"], o["f2"])


def _norm(p: str) -> str:
    return p.replace("\\", "/")


def _in_series_pairs(f1: str, f2: str) -> bool:
    f1, f2 = _norm(f1), _norm(f2)
    if frozenset({f1, f2}) in SERIES_PAIRS:
        return True
    # 容忍 NN_ 重编号：按 basename 对匹配
    b1, b2 = f1.rsplit("/", 1)[-1], f2.rsplit("/", 1)[-1]
    for pair in SERIES_PAIRS:
        bases = {p.rsplit("/", 1)[-1] for p in pair}
        if frozenset({b1, b2}) == bases:
            return True
    return False


def _in_series_path_family(f1: str, f2: str) -> bool:
    f1, f2 = _norm(f1), _norm(f2)
    return any(rx.search(f1) and rx.search(f2) for rx in SERIES_PATH_RE)


def is_series(o):
    if _in_series_pairs(o["f1"], o["f2"]):
        return True
    if _in_series_path_family(o["f1"], o["f2"]):
        return True
    if SERIES_RE.search(o["f1"]) or SERIES_RE.search(o["f2"]):
        return True
    if SERIES_RE.search(o.get("t1", "")) or SERIES_RE.search(o.get("t2", "")):
        return True
    # 同一 crate 内的版本序列
    p1 = o["f1"].split("/")
    p2 = o["f2"].split("/")
    if p1[0] == "crates" and p2[0] == "crates" and len(p1) > 1 and p1[1] == p2[1]:
        if re.search(r"19\d|1\d\d|part", o["f1"] + o["f2"]):
            return True
    return False


def triage(o):
    top1 = o["f1"].split("/")[0]
    top2 = o["f2"].split("/")[0]
    if is_series(o):
        return "SERIES"
    if o["sim"] >= 0.85:
        return "MERGE"
    if top1 == "docs" and top2 == "docs" and o["sim"] >= 0.7:
        return "DOCS_INTERNAL"
    if is_reviewed(o):
        return "REVIEWED"
    return "REVIEW"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    src = os.path.join(ROOT, "reports", f"CONTENT_OVERLAP_V2_{args.date}.json")
    if not os.path.exists(src):
        # 取最新
        cands = sorted(glob.glob(os.path.join(ROOT, "reports", "CONTENT_OVERLAP_V2_*.json")))
        if not cands:
            print("no CONTENT_OVERLAP_V2 json found; run detect_content_overlap_v2.py first")
            return 2
        src = cands[-1]
    data = json.load(open(src, encoding="utf-8"))
    overlaps = data.get("overlaps", [])

    buckets = {"SERIES": [], "MERGE": [], "DOCS_INTERNAL": [], "REVIEWED": [], "REVIEW": []}
    for o in overlaps:
        buckets[triage(o)].append(o)

    summary = {k: len(v) for k, v in buckets.items()}
    summary["total"] = len(overlaps)
    summary["source"] = os.path.relpath(src, ROOT).replace("\\", "/")

    out_md = os.path.join(ROOT, "reports", f"OVERLAP_TRIAGE_{args.date}.md")
    out_json = os.path.join(ROOT, "reports", f"OVERLAP_TRIAGE_{args.date}.json")
    with open(out_json, "w", encoding="utf-8") as f:
        json.dump({"summary": summary, "buckets": buckets}, f, ensure_ascii=False, indent=2)

    with open(out_md, "w", encoding="utf-8") as f:
        f.write(f"# 重叠对分类（P1 改写执行清单）\n\n")
        f.write(f"**来源**: `{summary['source']}`  **总对数**: {summary['total']}\n\n")
        f.write("| 分类 | 数量 | 处置 |\n|---|:---:|:---|\n")
        disp = {"SERIES": "保留但标注为版本系列/分章（白名单）", "MERGE": "应合并近克隆（留一删余或 stub 化）",
                "DOCS_INTERNAL": "docs/ 内同主题互抄（合并或互链）",
                "REVIEWED": "已批量复核确认非重复（stub/模板系列/同领域术语共现，白名单）", "REVIEW": "人工复核"}
        for k in ["MERGE", "DOCS_INTERNAL", "SERIES", "REVIEWED", "REVIEW"]:
            f.write(f"| {k} | {summary[k]} | {disp[k]} |\n")
        for k in ["MERGE", "DOCS_INTERNAL", "SERIES", "REVIEWED", "REVIEW"]:
            f.write(f"\n## {k}（{summary[k]}）Top 25\n\n")
            f.write("| sim | 文件1 | 文件2 |\n|:---:|:---|:---|\n")
            for o in buckets[k][:25]:
                f.write(f"| {o['sim']} | `{o['f1']}` | `{o['f2']}` |\n")
        f.write(f"\n## 机器可读\n\n- JSON: `reports/OVERLAP_TRIAGE_{args.date}.json`\n")

    print(f"[P1-triage] total={summary['total']} MERGE={summary['MERGE']} DOCS_INTERNAL={summary['DOCS_INTERNAL']} "
          f"SERIES={summary['SERIES']} REVIEWED={summary['REVIEWED']} REVIEW={summary['REVIEW']}")
    print(f"[P1-triage] report: {os.path.relpath(out_md, ROOT).replace(chr(92),'/')}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
