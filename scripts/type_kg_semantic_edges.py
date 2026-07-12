#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""为 KG v3 实例化 equivalentTo / instanceOf / appliesTo 三种零实例化关系。

背景：concept/00_meta/kg_data_v3.json 的 schema 声明了 9 种关系，其中
equivalentTo / instanceOf / appliesTo 长期零实例化（relatedTo 占 ~76%）。
本脚本以策展方式（每条边附 ex:evidence 页面依据 + ex:rule）落地三类边：

  equivalentTo（schema: Symmetric+Transitive+Reflexive，按惯例只落单向边）
    跨层同概念不同表述的实体对：同 ex:path 双节点、显式合并/重定向声明、
    相同 prefLabel + 相同 scopeNote 的跨层副本。
  instanceOf（inverseOf hasInstance）
    “概念是某范畴的实例”：范畴节点须已存在，否则记入缺口清单不建边。
  appliesTo（inverseOf governedBy）
    “技术/方法应用于领域”：目标领域节点须已存在。

规则编号：
  E1 same-path-dup     两实体 ex:path 完全相同（抽取重复节点）
  E2 explicit-merge    页面显式声明合并/重定向到另一权威页
  E3 same-concept-xlayer 跨层同概念（同 prefLabel 或同 scopeNote 表述）
  I1 category-listed   范畴页正文/Summary 明确列出该实例
  I2 category-section  实例页被范畴页作为章节/下层概念收录
  I3 self-evident-kind 实例页标题/定位自述其为该范畴的一种
  A1 page-application  技术页正文明确其应用于目标领域
  A2 prereq-domain     技术页前置依赖即目标领域，且正文阐述应用关系

- 同向同谓词边已存在时不重复添加；优先改已有的 relatedTo 边，其次补新边。
- 输出 reports/KG_SEMANTIC_EDGE_TYPING_<date>.{md,json}。
- 范畴缺口（实体不存在导致无法建边）输出到报告的“范畴节点缺口清单”。

用法：
  python scripts/type_kg_semantic_edges.py [--dry-run] [--date YYYY-MM-DD]
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
KG_PATH = ROOT / "concept" / "00_meta" / "kg_data_v3.json"

PRED_EQ = "ex:equivalentTo"
PRED_INST = "ex:instanceOf"
PRED_APPL = "ex:appliesTo"
PRED_REL = "ex:relatedTo"

# ---------------------------------------------------------------------------
# 策展 equivalentTo（跨层同概念不同表述；schema 为对称关系，按工具惯例落单向边）
# ---------------------------------------------------------------------------
CURATED_EQUIV: list[tuple[str, str, str, str]] = [
    ("ex:LifetimesAdvanced", "ex:Lifetimes_00traits", "E1-same-path-dup",
     "两实体 ex:path 均为 01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md"
     "（抽取重复节点；同一权威页的双 @id）"),
    ("ex:PanicAndAbort", "ex:Panic", "E3-same-concept-xlayer",
     "02_intermediate/03_error_handling/03_panic.md:9 Summary“Rust panic 的规范语义”，"
     "前置依赖指向 03_panic_and_abort.md；后者定位“系统讲解 Rust panic 机制”——同一 panic 概念的 L1/L2 两页"),
    ("ex:AutoVerusAndVerusAutomatedVerificationEcosystem", "ex:AutoVerusVerus", "E3-same-concept-xlayer",
     "04_formal/04_model_checking/07_autoverus.md 与 07_future/03_preview_features/33_autoverus_preview.md "
     "Summary 逐字相同（“Verus 是用 Rust 本身编写规格与证明的 SMT 验证器；AutoVerus 是基于 LLM 的自动化证明生成系统…”），"
     "同一主题跨 L4/L7 双权威页"),
    ("ex:SafetyTagsForUnsafeCode", "ex:SafetyTagsForUnsafeCode_03previewfea", "E2-explicit-merge",
     "04_formal/02_separation_logic/03_safety_tags_in_formal.md 为显式重定向 stub："
     "“本主题已合并至 07_future/03_preview_features/03_safety_tags_preview.md…v2 相似度 0.855”"),
    ("ex:SafetyTagsPreview", "ex:SafetyTagsForUnsafeCode_03previewfea", "E1-same-path-dup",
     "两实体 ex:path 均为 07_future/03_preview_features/03_safety_tags_preview.md（抽取重复节点）"),
    ("ex:BorrowSanitizerRuntimeTreeBorrowsViolationDetection",
     "ex:BorrowSanitizerBSanDynamicAliasingRuleVerificationForRust", "E3-same-concept-xlayer",
     "04_formal/02_separation_logic/04_borrow_sanitizer_in_formal.md 与 07_future/03_preview_features/24_borrow_sanitizer.md "
     "均为 BorrowSanitizer/BSan 权威页（MCP 958；LLVM 插桩动态别名检测），跨 L4/L7 双页"),
    ("ex:BorrowSanitizerBSanDynamicAliasingRuleVerificationForRust", "ex:BorrowSanitizerPreview",
     "E1-same-path-dup",
     "两实体 ex:path 均为 07_future/03_preview_features/24_borrow_sanitizer.md（抽取重复节点）"),
    ("ex:RustBelt", "ex:RustBelt_02separation", "E3-same-concept-xlayer",
     "两实体 prefLabel 均为 RustBelt；00_meta/02_sources/02_rustbelt_predicate_map.md 定位"
     "“将 RustBelt（Jung et al., POPL 2018）的核心形式化谓词映射到 L1-L3 工程概念”，"
     "04_formal/02_separation_logic/01_rustbelt.md Summary“RustBelt: a formal model of Rust's ownership and borrowing in Iris separation logic”"),
    ("ex:GameDevelopment_11domainappl", "ex:GameDevelopment_11domainappl_1", "E1-same-path-dup",
     "两实体 ex:path 均为 06_ecosystem/11_domain_applications/05_game_development.md（抽取重复节点）"),
]

# ---------------------------------------------------------------------------
# 策展 instanceOf（概念是范畴的实例；范畴节点均已确认存在）
# ---------------------------------------------------------------------------
CURATED_INSTANCE: list[tuple[str, str, str, str]] = [
    ("ex:MiriRustUndefinedBehaviorDetector", "ex:VerificationToolchain", "I1-category-listed",
     "04_formal/04_model_checking/01_verification_toolchain.md:6 Summary"
     "“The Rust formal verification toolchain: Miri, Kani, Creusot, Verus, Prusti, and RustBelt.”"),
    ("ex:KaniRustBoundedModelChecker", "ex:VerificationToolchain", "I1-category-listed",
     "01_verification_toolchain.md:6 Summary 将 Kani 列为验证工具链成员"),
    ("ex:AutoVerusAndVerusAutomatedVerificationEcosystem", "ex:VerificationToolchain", "I1-category-listed",
     "01_verification_toolchain.md:6 Summary 将 Verus 列为验证工具链成员"),
    ("ex:RustBelt_02separation", "ex:VerificationToolchain", "I1-category-listed",
     "01_verification_toolchain.md:6 Summary 将 RustBelt 列为验证工具链成员"),
    ("ex:ProceduralMacros", "ex:Macros", "I3-self-evident-kind",
     "01_foundation/09_macros_basics/01_attributes_and_macros.md:4 关键术语"
     "“宏 (Macro) · 声明宏 (Declarative Macro) · 过程宏 (Procedural Macro)”；"
     "03_advanced/03_proc_macros/02_proc_macro.md:170“三种宏（Macro）的编译期执行模型相同”——过程宏是宏的一种"),
    ("ex:DerivableTraits", "ex:Traits", "I3-self-evident-kind",
     "02_intermediate/00_traits/06_derive_traits.md:7 Summary"
     "“标准库中可通过 #[derive(...)] 自动实现的 trait 参考”——可派生 trait 是 trait 的一个子范畴"),
    ("ex:PanicAndAbort", "ex:ErrorHandling", "I3-self-evident-kind",
     "01_foundation/08_error_handling/03_panic_and_abort.md 标题"
     "“Panic 与 Abort：不可恢复错误的处理机制”——panic/abort 是错误处理机制的一种（不可恢复分支）"),
    ("ex:Panic", "ex:ErrorHandling", "I3-self-evident-kind",
     "02_intermediate/03_error_handling/03_panic.md:30"
     "“Panic 是 Rust 提供的机制，用于阻止函数正常返回，以响应通常不可恢复的错误条件”"),
    ("ex:CowAndBorrowed", "ex:SmartPointers", "I2-category-section",
     "02_intermediate/02_memory_management/04_smart_pointers.md:620“下层概念: Pin · Cow”——"
     "Cow 被智能指针权威页收录为下层概念（写时克隆智能指针）"),
    ("ex:PinAndUnpin", "ex:SmartPointers", "I2-category-section",
     "04_smart_pointers.md:620“下层概念: Pin · Cow”；:19 后置概念含 Pin——Pin 被智能指针权威页收录为下层概念"),
    ("ex:CustomAllocators", "ex:MemoryManagement", "I2-category-section",
     "02_intermediate/02_memory_management/01_memory_management.md:101 设 §5.7“自定义 Allocator"
     "（#[global_allocator]）”章节——自定义分配器是内存管理机制的实例"),
    ("ex:LockingPrimitives", "ex:Concurrency", "I3-self-evident-kind",
     "03_advanced/00_concurrency/06_lock_free.md:11“深入探讨 Rust 中的无锁编程”（位于 00_concurrency 章节）；"
     "01_concurrency.md:181-182 将锁/原子操作列为并发同步手段——无锁原语是并发技术的一种"),
    ("ex:NewtypeAndWrapperTypes", "ex:DesignPatterns", "I1-category-listed",
     "06_ecosystem/03_design_patterns/01_patterns.md:66“| Newtype | 结构型 | 类型区分 + 约束 | struct Wrapper(T) |”"
     "——Newtype 被设计模式权威页列为结构型模式"),
    ("ex:EventDrivenArchitecture", "ex:DesignPatterns", "I3-self-evident-kind",
     "06_ecosystem/03_design_patterns/06_event_driven_architecture.md:16"
     "“Rust 实现事件驱动架构的核心模式”（位于 03_design_patterns 章节）"),
    ("ex:CqrsEventSourcing", "ex:DesignPatterns", "I3-self-evident-kind",
     "06_ecosystem/03_design_patterns/07_cqrs_event_sourcing.md:15"
     "“设计高可靠分布式系统的数据持久化模式”（位于 03_design_patterns 章节）"),
    ("ex:ClosureTypes", "ex:Closures", "I2-category-section",
     "01_foundation/00_start/03_closure_basics.md:2 关键术语“闭包 (Closure) · Fn · FnMut · FnOnce”；"
     ":7 Summary 将 Fn/FnMut/FnOnce（闭包类型）作为闭包概念的组成"),
    ("ex:ConstantEvaluation", "ex:CompileTimeExecution", "I3-self-evident-kind",
     "07_future/03_preview_features/32_compile_time_execution.md:1 标题“编译期执行与常量求值”"
     "——常量求值（const eval）是编译期执行的实例"),
    ("ex:TypeErasure", "ex:DispatchMechanisms", "I2-category-section",
     "02_intermediate/00_traits/02_dispatch_mechanisms.md:8 Summary 覆盖“动态分发、trait objects、vtables”；"
     "04_formal/05_rustc_internals/15_generics_compiler_behavior.md:4 将“静态分发与动态分发、类型擦除”"
     "并列为泛型编译行为——类型擦除是动态分发机制的实现"),
]

# ---------------------------------------------------------------------------
# 策展 appliesTo（技术/方法应用于领域；领域节点均已确认存在）
# ---------------------------------------------------------------------------
CURATED_APPLIES: list[tuple[str, str, str, str]] = [
    ("ex:MiriRustUndefinedBehaviorDetector", "ex:SafeAndEffectiveUnsafeRust", "A1-page-application",
     "04_formal/04_model_checking/08_miri.md:9 Summary“Miri is Rust's official MIR interpreter for detecting "
     "undefined behavior in unsafe and safe Rust code”"),
    ("ex:KaniRustBoundedModelChecker", "ex:FormalMethods_04modelcheck", "A1-page-application",
     "04_formal/04_model_checking/09_kani.md:9 Summary“Kani is an AWS-developed bounded model checker for Rust. "
     "It verifies properties over all possible inputs and execution paths within bounds”——应用于模型检查领域"),
    ("ex:SerdePatterns", "ex:Traits", "A1-page-application",
     "02_intermediate/00_traits/03_serde_patterns.md:4“Serde 序列化模式：Rust 的类型驱动数据转换”（位于 00_traits 章节；"
     "关键术语 Serialize/Deserialize trait）——serde 是 trait 机制的应用"),
    ("ex:RustBelt_02separation", "ex:SafeAndEffectiveUnsafeRust", "A1-page-application",
     "04_formal/02_separation_logic/01_rustbelt.md:23 后置/相关链接 Unsafe Rust；:35“扩展层次一致性标注至 L3 Unsafe”；"
     "来源标题“RustBelt: Securing the Foundations of the Rust Programming Language”——RustBelt 应用于 unsafe 抽象可靠性"),
    ("ex:TreeBorrowsDeepDive", "ex:SafeAndEffectiveUnsafeRust", "A2-prereq-domain",
     "04_formal/01_ownership_logic/05_tree_borrows_deep_dive.md:10 受众“Unsafe Rust、形式化方法…开发者”；"
     ":15 前置依赖 Unsafe Rust——Tree Borrows 别名模型应用于 unsafe 代码合法性判定"),
    ("ex:BehaviorConsideredUndefined", "ex:SafeAndEffectiveUnsafeRust", "A2-prereq-domain",
     "04_formal/01_ownership_logic/06_behavior_considered_undefined.md:14 前置依赖 Unsafe Rust；"
     "Summary“Rust Reference 明确列出的未定义行为（UB）清单…核心安全契约边界”——UB 清单应用于 unsafe 契约边界"),
    ("ex:BorrowSanitizerRuntimeTreeBorrowsViolationDetection", "ex:SafeAndEffectiveUnsafeRust", "A2-prereq-domain",
     "04_formal/02_separation_logic/04_borrow_sanitizer_in_formal.md 前置依赖 Unsafe Rust · Miri；"
     "Summary“基于 LLVM 插桩的动态分析工具，用于检测 Rust 别名模型…违规”——应用于 unsafe 别名违规检测"),
    ("ex:ApplicationBinaryInterface", "ex:ForeignFunctionInterfaceFFI", "A2-prereq-domain",
     "04_formal/05_rustc_internals/05_application_binary_interface.md:15 前置依赖 Linkage · FFI Advanced；"
     "来源 Rust Reference extern functions/external blocks——ABI 规则应用于 FFI 边界"),
    ("ex:MemoryModel", "ex:Concurrency", "A1-page-application",
     "03_advanced/02_unsafe/06_memory_model.md:11“其并发内存序维度见 Atomics and Memory Ordering”；"
     ":33“将 Rust 内存模型与原子操作…链接”——内存模型应用于并发语义"),
    ("ex:PinAndUnpin", "ex:AsyncProgramming", "A1-page-application",
     "03_advanced/01_async/08_pin_unpin.md:6 Summary“their interaction with futures and generators”；"
     ":16“探讨 Pin 与 Future、Generator 的交互，以及 async/await 的状态机实现”——Pin 应用于 async 状态机"),
    ("ex:GenericsCompilerBehavior", "ex:Generics", "A1-page-application",
     "04_formal/05_rustc_internals/15_generics_compiler_behavior.md:4 Summary"
     "“Rust 泛型（Generics）代码的编译行为：单态化、静态分发与动态分发、类型擦除…”——应用于泛型编译"),
    ("ex:TypeInference", "ex:TypeSystem", "A1-page-application",
     "04_formal/00_type_theory/03_type_inference.md:15“Rust 对 HM 的扩展（trait 约束、泛型（Generics）、"
     "生命周期（Lifetimes））”——类型推断算法应用于 Rust 类型系统"),
    ("ex:TheTraitSolverInRustc", "ex:Traits", "A1-page-application",
     "04_formal/05_rustc_internals/03_trait_solver_in_rustc.md:2 关键术语“Trait Solver · Selection · "
     "Fulfillment · Evaluation · Obligation”——trait 求解器应用于 trait 约束求解"),
    ("ex:DispatchMechanisms", "ex:Traits", "A1-page-application",
     "02_intermediate/00_traits/02_dispatch_mechanisms.md:8 Summary“Static and dynamic dispatch in Rust: "
     "monomorphization, trait objects, vtables, object safety”（位于 00_traits 章节）——分发机制应用于 trait 使用"),
]

# ---------------------------------------------------------------------------
# 范畴节点缺口：第一轮（2026-07-12）登记 9 项，第二轮已全部解决——
# 见 scripts/add_kg_category_nodes.py 与 reports/KG_CATEGORY_NODES_2026-07-12.md
#（新建 17 节点 + 14 条 instanceOf/appliesTo 边）。本列表保留为空。
# ---------------------------------------------------------------------------
CATEGORY_GAPS: list[tuple[str, str, str]] = []


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true", help="只输出报告，不写回 kg_data_v3.json")
    ap.add_argument("--date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    data = json.loads(KG_PATH.read_text(encoding="utf-8"))
    entities = data["entities"]
    relations = data["relations"]
    id_set = {e["@id"] for e in entities}

    before = Counter(r["ex:predicate"] for r in relations)

    def has_edge(s: str, o: str, pred: str | None = None) -> bool:
        return any(r["ex:subject"] == s and r["ex:object"] == o
                   and (pred is None or r["ex:predicate"] == pred) for r in relations)

    def find_edge(s: str, o: str, pred: str):
        for r in relations:
            if r["ex:subject"] == s and r["ex:object"] == o and r["ex:predicate"] == pred:
                return r
        return None

    max_id = max((int(m.group(1)) for r in relations
                  if (m := re.match(r"_:rel(\d+)$", r.get("@id", "")))), default=0)

    changes: list[dict] = []
    skipped_missing_entity: list[tuple[str, str, str]] = []

    def apply_edge(s: str, o: str, pred: str, rule: str, evidence: str) -> None:
        nonlocal max_id
        if s not in id_set or o not in id_set:
            skipped_missing_entity.append((s, pred, o))
            return
        if has_edge(s, o, pred):
            return
        rel = find_edge(s, o, PRED_REL)
        if rel is not None:
            rel["ex:predicate"] = pred
            rel["ex:evidence"] = evidence
            rel["ex:rule"] = rule
            rel["ex:reviewed"] = True
            changes.append({"rule": rule, "subject": s, "object": o, "predicate": pred,
                            "action": "retyped relatedTo", "evidence": evidence})
        else:
            action = "added parallel edge" if has_edge(s, o) else "added new edge"
            max_id += 1
            relations.append({
                "@id": f"_:rel{max_id}",
                "@type": "ex:RelationAnnotation",
                "ex:subject": s,
                "ex:predicate": pred,
                "ex:object": o,
                "ex:source": "curated:" + rule,
                "ex:evidence": evidence,
                "ex:rule": rule,
                "ex:confidence": 1.0,
                "ex:version": "1.97.0",
                "ex:reviewed": True,
                "dcterms:created": args.date,
            })
            changes.append({"rule": rule, "subject": s, "object": o, "predicate": pred,
                            "action": action, "evidence": evidence})

    for s, o, rule, ev in CURATED_EQUIV:
        apply_edge(s, o, PRED_EQ, rule, ev)
    for s, o, rule, ev in CURATED_INSTANCE:
        apply_edge(s, o, PRED_INST, rule, ev)
    for s, o, rule, ev in CURATED_APPLIES:
        apply_edge(s, o, PRED_APPL, rule, ev)

    after = Counter(r["ex:predicate"] for r in relations)

    # ---- 报告 ----
    # dry-run 不写正式报告文件，避免覆盖历史报告（2026-07-12 曾因此覆盖第一轮报告）
    suffix = "_DRYRUN" if args.dry_run else ""
    out_md = ROOT / "reports" / f"KG_SEMANTIC_EDGE_TYPING_{args.date}{suffix}.md"
    out_json = ROOT / "reports" / f"KG_SEMANTIC_EDGE_TYPING_{args.date}{suffix}.json"

    def dist_table(b: Counter, a: Counter) -> list[str]:
        keys = sorted(set(b) | set(a), key=lambda k: -a.get(k, 0))
        rows = ["| 谓词 | 前 | 后 | Δ |", "|:---|---:|---:|---:|"]
        for k in keys:
            rows.append(f"| {k} | {b.get(k, 0)} | {a.get(k, 0)} | {a.get(k, 0) - b.get(k, 0):+d} |")
        return rows

    n_eq = sum(1 for c in changes if c["predicate"] == PRED_EQ)
    n_inst = sum(1 for c in changes if c["predicate"] == PRED_INST)
    n_appl = sum(1 for c in changes if c["predicate"] == PRED_APPL)

    lines = [
        "# KG 语义关系实例化（equivalentTo / instanceOf / appliesTo）",
        "",
        f"**日期**: {args.date}  **模式**: {'dry-run（未写回）' if args.dry_run else '已写回 kg_data_v3.json'}  ",
        f"**equivalentTo**: {n_eq} 条  **instanceOf**: {n_inst} 条  **appliesTo**: {n_appl} 条  ",
        f"**改动总数**: {len(changes)}（跳过实体缺失 {len(skipped_missing_entity)}）",
        "",
        "## 谓词分布前后对比",
        "",
    ]
    lines += dist_table(before, after)
    lines += ["", "## 逐边明细与依据", "",
              "| 规则 | 动作 | 主语 | 谓词 | 宾语 | 依据 |",
              "|:---|:---|:---|:---|:---|:---|"]
    for c in changes:
        ev = c["evidence"].replace("|", "\\|")
        lines.append(f"| {c['rule']} | {c['action']} | {c['subject']} | {c['predicate']} "
                     f"| {c['object']} | {ev} |")
    if skipped_missing_entity:
        lines += ["", "## 跳过（实体缺失）", ""]
        for s, p, o in skipped_missing_entity:
            lines.append(f"- `{s}` -[{p}]-> `{o}`：端点实体不存在")
    lines += ["", "## 范畴节点缺口清单（按约束未新建实体）", "",
              "| 缺失节点 | 原计划边 | 说明/替代 |",
              "|:---|:---|:---|"]
    for node, plan, note in CATEGORY_GAPS:
        lines.append(f"| {node} | {plan} | {note} |")
    lines += ["", "## 备注", "",
              "- equivalentTo 在 schema 中声明为 Symmetric+Transitive+Reflexive，按 `type_kg_core_edges.py` 惯例只落单向边。",
              "- Unsafe（L3 01_unsafe）与 L4 tree_borrows / behavior_considered_undefined **不**建 equivalentTo："
              "后两者是别名模型/UB 清单等独立概念，已改用 appliesTo 指向 ex:SafeAndEffectiveUnsafeRust。",
              "", "## 机器可读", "",
              f"- JSON: `reports/KG_SEMANTIC_EDGE_TYPING_{args.date}{suffix}.json`", ""]

    out_json.write_text(json.dumps({
        "date": args.date, "dry_run": args.dry_run,
        "counts": {"equivalentTo": n_eq, "instanceOf": n_inst, "appliesTo": n_appl,
                   "total_changes": len(changes), "skipped_missing_entity": len(skipped_missing_entity)},
        "before": dict(before), "after": dict(after),
        "changes_detail": changes,
        "category_gaps": [{"node": n, "planned_edge": p, "note": t} for n, p, t in CATEGORY_GAPS],
    }, ensure_ascii=False, indent=2), encoding="utf-8")
    out_md.write_text("\n".join(lines), encoding="utf-8")

    if not args.dry_run:
        meta = data.get("metadata")
        if isinstance(meta, dict) and "relation_count" in meta:
            meta["relation_count"] = len(relations)
        KG_PATH.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")

    print(f"[type_kg_semantic_edges] equiv={n_eq} instanceOf={n_inst} appliesTo={n_appl} "
          f"total={len(changes)} skipped={len(skipped_missing_entity)} dry_run={args.dry_run}")
    print(f"  relatedTo: {before.get(PRED_REL, 0)} → {after.get(PRED_REL, 0)} "
          f"(total {sum(before.values())} → {sum(after.values())})")
    print(f"  report: {out_md.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
