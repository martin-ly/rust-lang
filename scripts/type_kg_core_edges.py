#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""为 KG v3 核心子集实例化语义关系类型（反 relatedTo 塌缩）。

背景：concept/00_meta/kg_data_v3.json 的 5799 条边中 ~77% 是无类型 relatedTo；
schema 声明的 9 种关系中 mutexWith/refines/counterExample/equivalentTo/instanceOf/
appliesTo 零实例化。本脚本对 L1–L3 九大核心主题（ownership/borrowing/lifetimes/
traits/generics/async/unsafe/error_handling/concurrency 及其近邻，约 55 个实体）
之间的边进行人工/半自动类型化。

规则（按优先级，命中即定，每条改动附 ex:evidence 依据说明）：
  R1 CURATED_MUTEX    → ex:mutexWith      策展互斥对，依据为权威页原句（文件:行号）
  R2 CURATED_CEX      → ex:counterExample 策展反例：A 页的反例章节反驳 B 的朴素假设
  R3 CURATED_REFINES  → ex:refines        策展精化：A 是 B 的进阶/模式/机制展开
  R4 前置元数据       → ex:dependsOn      目标出现在源页 前置概念/前置依赖 元数据
  R5 后置元数据       → ex:entails        目标出现在源页 后置概念/后置延伸 元数据
未命中规则的 relatedTo 边保持原状；非 relatedTo 边不改动。

- 同向同谓词边已存在时不重复添加；策展对无任何边时新增 RelationAnnotation。
- 输出 reports/KG_CORE_EDGE_TYPING_<date>.{md,json}，含每条边的依据。
- 与 atlas 07 的符号推断（scripts/generate_knowledge_topology_atlas.py
  `infer_relation` / CURATED_MUTEX）同源一致。

用法：
  python scripts/type_kg_core_edges.py [--dry-run] [--date YYYY-MM-DD]
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import os
import re
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONCEPT = ROOT / "concept"
KG_PATH = CONCEPT / "00_meta" / "kg_data_v3.json"

# 核心主题目录片段（L1–L3）：九大主题及其近邻
CORE_TOPICS = (
    "ownership_borrow",     # 01_foundation/01_ownership_borrow_lifetime
    "error_handling",       # 01_foundation/08 + 02_intermediate/03
    "00_traits", "01_generics", "02_memory_management",
    "04_types_and_conversions",
    "00_concurrency", "01_async", "02_unsafe",
)
EXCLUDE_FRAGMENTS = ("quiz",)

# ---------------------------------------------------------------------------
# 策展关系（每条均附人工可辩护依据：权威页文件:行号 + 原句引述）
# ---------------------------------------------------------------------------

# R1 互斥：两概念不能同时成立（mutexWith 对称；按列出方向落边）
CURATED_MUTEX: list[tuple[str, str, str]] = [
    ("ex:MoveSemantics", "ex:Borrowing",
     "01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md:942 "
     "“Rust 的所有权（Ownership）转移（move）与借用是互斥的。若变量已被借用…在借用释放前不能转移其所有权。”"),
    ("ex:PinAndUnpin", "ex:MoveSemantics",
     "03_advanced/01_async/08_pin_unpin.md:735 “Pin 通过禁止移动（对 !Unpin 类型）来解决这个问题”；"
     ":648 “T: !Unpin — Pin 禁止 get_mut()（数据不可移动）”"),
    ("ex:Unions", "ex:MemoryManagement",
     "02_intermediate/04_types_and_conversions/06_unions.md:105 “Drop: 默认不 drop 字段”；"
     ":250 “联合体默认不会自动 drop 字段”——与 RAII 自动析构纪律互斥"),
    ("ex:PanicAndAbort", "ex:ErrorHandling",
     "01_foundation/08_error_handling/03_panic_and_abort.md:5 “不可恢复错误的处理机制”；"
     ":91 “异常: 可恢复的错误条件”——同一错误现场不可恢复(panic/abort)与可恢复(Result 传播)策略二选一"),
    ("ex:TypeLevelProgramming", "ex:RTTIAndDynamicTypeIdentification",
     "02_intermediate/04_types_and_conversions/05_rtti_and_dynamic_typing.md:203 "
     "“RTTI 是静态类型系统（Type System）向运行时的有限‘泄漏’”——编译期类型计算与运行期类型识别在同一类型问题上互斥"),
]

# R2 反例：A 页的反例章节/边界测试反驳关于 B 的朴素假设
CURATED_CEX: list[tuple[str, str, str]] = [
    ("ex:InteriorMutability", "ex:Borrowing",
     "01_foundation/01_ownership_borrow_lifetime/02_borrowing.md:781 "
     "“&mut vs &: 为什么不能同时有？… AXM: 读写互斥 … UnsafeCell 突破”；:461 “别名与可变互斥公理”"
     "——内部可变性（Cell/RefCell/UnsafeCell）是借用规则的受控反例"),
    ("ex:SafeAndEffectiveUnsafeRust", "ex:Lifetimes",
     "03_advanced/02_unsafe/01_unsafe.md:1125 “8.3 反例：悬垂裸指针（UB）”"
     "——裸指针悬垂是对“引用有效性总由生命周期保证”的反例"),
    ("ex:SafeAndEffectiveUnsafeRust", "ex:TypeConversions",
     "03_advanced/02_unsafe/01_unsafe.md:1140 “8.4 反例：transmute 滥用（UB）”"
     "——transmute 滥用是对安全类型转换纪律的反例"),
    ("ex:SafeAndEffectiveUnsafeRust", "ex:MemoryManagement",
     "03_advanced/02_unsafe/01_unsafe.md:1422 “❌ 反例: Use-after-free（Miri 会报错）”"
     "——UAF 是对自动内存管理保证的反例"),
    ("ex:LockingPrimitives", "ex:Concurrency",
     "03_advanced/00_concurrency/06_lock_free.md:409 “命题: 无锁总是优于锁” → "
     ":422 “无锁只在高竞争场景显著优于锁”——对朴素并发性能信念的反例"),
]

# R3 精化：A 是 B 的进阶/深入/模式/机制展开（refines 传递）
CURATED_REFINES: list[tuple[str, str, str]] = [
    ("ex:LifetimesAdvanced", "ex:Lifetimes",
     "01_foundation/01_ownership_borrow_lifetime/04_lifetimes_advanced.md 为 03_lifetimes.md 的进阶展开（标题“生命周期进阶”）"),
    ("ex:Traits_00traits", "ex:Traits",
     "02_intermediate/00_traits/04_advanced_traits.md 为 01_traits.md 的高级主题精化（标题“高级 Trait 主题”）"),
    ("ex:AsyncAdvanced", "ex:AsyncProgramming",
     "03_advanced/01_async/02_async_advanced.md 为 02_async.md 的进阶展开（标题“Async 进阶”）"),
    ("ex:ErrorHandling_03errorhandl_1", "ex:ErrorHandling_03errorhandl",
     "02_intermediate/03_error_handling/02_error_handling_deep_dive.md 为 04_error_handling.md 的深入精化（标题“错误处理深入”）"),
    ("ex:UnsafeRust", "ex:SafeAndEffectiveUnsafeRust",
     "03_advanced/02_unsafe/04_unsafe_rust_patterns.md 将 03_unsafe.md 精化为可复用 unsafe 模式"),
    ("ex:Concurrency_00concurrenc", "ex:Concurrency",
     "03_advanced/00_concurrency/03_concurrency_patterns.md 将 01_concurrency.md 精化为并发模式谱系"),
    ("ex:CowAndBorrowed", "ex:Borrowing",
     "02_intermediate/02_memory_management/03_cow_and_borrowed.md: Cow 将借用语义精化为写时克隆（Clone-on-Write）"),
    ("ex:Borrowing_02unsafe", "ex:Borrowing",
     "03_advanced/02_unsafe/03_nll_and_polonius.md: NLL/Polonius 将借用检查从词法作用域精化到使用点/流敏感"),
    ("ex:FutureAndExecutorMechanisms", "ex:AsyncProgramming",
     "03_advanced/01_async/04_future_and_executor_mechanisms.md 精化 async 的 Future/执行器机制"),
    ("ex:SerdePatterns", "ex:Traits",
     "02_intermediate/00_traits/03_serde_patterns.md 将 trait 精化为 serde 序列化模式应用"),
    ("ex:MemoryModel", "ex:SafeAndEffectiveUnsafeRust",
     "03_advanced/02_unsafe/06_memory_model.md 精化 unsafe 语义的内存模型基础"),
    ("ex:AsyncClosures", "ex:AsyncProgramming",
     "03_advanced/01_async/07_async_closures.md 将 async 精化到闭包捕获场景"),
]

PRED_MUTEX = "ex:mutexWith"
PRED_CEX = "ex:counterExample"
PRED_REFINES = "ex:refines"
PRED_DEP = "ex:dependsOn"
PRED_ENT = "ex:entails"
PRED_REL = "ex:relatedTo"

# ---------------------------------------------------------------------------
# 权威页头部元数据解析（与 scripts/extract_concept_topology.py 同款规整）
# ---------------------------------------------------------------------------

_FIELD_START_RE = re.compile(r"^\*\*[^*]+\*\*[:：]")
_LINK_RE = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")


def normalize_blockquote_header(text: str, max_lines: int = 150) -> str:
    fields: list[str] = []
    for ln in text.splitlines()[:max_lines]:
        s = ln.strip()
        if s == "---":
            break
        if not s.startswith(">"):
            continue
        body = s[1:].strip()
        if not body:
            continue
        if _FIELD_START_RE.match(body):
            fields.append(body)
        elif fields:
            fields[-1] += " " + body
    return "\n".join(fields)


def header_link_stems(rel_path: str, key_pat: str) -> set[str]:
    """从权威页头部元数据（前置概念/后置概念等）抽取链接目标文件 stem 集。"""
    f = CONCEPT / rel_path
    if not f.is_file():
        return set()
    header = normalize_blockquote_header(f.read_text(encoding="utf-8", errors="replace"))
    m = re.search(key_pat + r"[:：]\s*(.+)", header)
    if not m:
        return set()
    return {Path(href).stem for _, href in _LINK_RE.findall(m.group(1)) if href.endswith(".md")}


# ---------------------------------------------------------------------------


def entity_layer(path: str) -> int:
    m = re.match(r"(\d\d)_", path.split("/")[0])
    return int(m.group(1)) if m else 0


def build_core_set(entities: list[dict]) -> dict[str, dict]:
    core = {}
    for e in entities:
        p = e.get("ex:path", "")
        if not (1 <= entity_layer(p) <= 3):
            continue
        if any(t in p for t in CORE_TOPICS) and not any(x in p for x in EXCLUDE_FRAGMENTS):
            core[e["@id"]] = e
    return core


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dry-run", action="store_true", help="只输出报告，不写回 kg_data_v3.json")
    ap.add_argument("--date", default=_dt.date.today().isoformat())
    args = ap.parse_args()

    data = json.loads(KG_PATH.read_text(encoding="utf-8"))
    entities = data["entities"]
    relations = data["relations"]
    id_to_entity = {e["@id"]: e for e in entities}
    core = build_core_set(entities)

    before_global = Counter(r["ex:predicate"] for r in relations)
    core_edges = [r for r in relations
                  if r["ex:subject"] in core and r["ex:object"] in core]
    before_core = Counter(r["ex:predicate"] for r in core_edges)

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

    changes: list[dict] = []  # {rule, subject, predicate_new, object, action, evidence}

    def apply_typing(s: str, o: str, pred: str, rule: str, evidence: str) -> None:
        """把 (s,o) 类型化为 pred：优先改已有的 relatedTo 边，其次补新边。"""
        nonlocal max_id
        if has_edge(s, o, pred):
            return  # 已是目标类型
        rel = find_edge(s, o, PRED_REL)
        if rel is not None:
            rel["ex:predicate"] = pred
            rel["ex:evidence"] = evidence
            rel["ex:rule"] = rule
            rel["ex:reviewed"] = True
            changes.append({"rule": rule, "subject": s, "object": o, "predicate": pred,
                            "action": "retyped relatedTo", "evidence": evidence})
        elif not has_edge(s, o):
            max_id += 1
            relations.append({
                "@id": f"_:rel{max_id}",
                "@type": "ex:RelationAnnotation",
                "ex:subject": s,
                "ex:predicate": pred,
                "ex:object": o,
                "ex:source": "curated:" + evidence.split(" ")[0],
                "ex:evidence": evidence,
                "ex:rule": rule,
                "ex:confidence": 1.0,
                "ex:version": "1.97.0",
                "ex:reviewed": True,
                "dcterms:created": args.date,
            })
            changes.append({"rule": rule, "subject": s, "object": o, "predicate": pred,
                            "action": "added new edge", "evidence": evidence})
        else:
            # 已有非 relatedTo 边（如 dependsOn）：补一条目标类型边（语义可并存时）
            max_id += 1
            relations.append({
                "@id": f"_:rel{max_id}",
                "@type": "ex:RelationAnnotation",
                "ex:subject": s,
                "ex:predicate": pred,
                "ex:object": o,
                "ex:source": "curated:" + evidence.split(" ")[0],
                "ex:evidence": evidence,
                "ex:rule": rule,
                "ex:confidence": 1.0,
                "ex:version": "1.97.0",
                "ex:reviewed": True,
                "dcterms:created": args.date,
            })
            changes.append({"rule": rule, "subject": s, "object": o, "predicate": pred,
                            "action": "added parallel edge", "evidence": evidence})

    # R1–R3 策展规则
    for s, o, ev in CURATED_MUTEX:
        apply_typing(s, o, PRED_MUTEX, "R1-curated-mutex", ev)
    for s, o, ev in CURATED_CEX:
        apply_typing(s, o, PRED_CEX, "R2-curated-counterexample", ev)
    for s, o, ev in CURATED_REFINES:
        apply_typing(s, o, PRED_REFINES, "R3-curated-refines", ev)

    # R4/R5 元数据规则：核心子集内剩余 relatedTo 边
    rel_core = [r for r in relations
                if r["ex:predicate"] == PRED_REL
                and r["ex:subject"] in core and r["ex:object"] in core]
    for r in rel_core:
        s, o = r["ex:subject"], r["ex:object"]
        src_path = core[s].get("ex:path", "")
        dst_stem = Path(core[o].get("ex:path", "")).stem
        if not src_path or not dst_stem:
            continue
        pre = header_link_stems(src_path, r"\*\*前置(?:概念|依赖)\*\*")
        if dst_stem in pre and not has_edge(s, o, PRED_DEP):
            ev = f"权威页前置元数据：{src_path} 的 前置概念/前置依赖 含 [{dst_stem}]"
            r["ex:predicate"] = PRED_DEP
            r["ex:evidence"] = ev
            r["ex:rule"] = "R4-prereq-metadata"
            r["ex:reviewed"] = True
            changes.append({"rule": "R4-prereq-metadata", "subject": s, "object": o,
                            "predicate": PRED_DEP, "action": "retyped relatedTo", "evidence": ev})
            continue
        post = header_link_stems(src_path, r"\*\*后置(?:概念|延伸)\*\*")
        if dst_stem in post and not has_edge(s, o, PRED_ENT):
            ev = f"权威页后置元数据：{src_path} 的 后置概念/后置延伸 含 [{dst_stem}]"
            r["ex:predicate"] = PRED_ENT
            r["ex:evidence"] = ev
            r["ex:rule"] = "R5-postreq-metadata"
            r["ex:reviewed"] = True
            changes.append({"rule": "R5-postreq-metadata", "subject": s, "object": o,
                            "predicate": PRED_ENT, "action": "retyped relatedTo", "evidence": ev})

    after_global = Counter(r["ex:predicate"] for r in relations)
    core_edges_after = [r for r in relations
                        if r["ex:subject"] in core and r["ex:object"] in core]
    after_core = Counter(r["ex:predicate"] for r in core_edges_after)

    # ---- 报告 ----
    out_md = ROOT / "reports" / f"KG_CORE_EDGE_TYPING_{args.date}.md"
    out_json = ROOT / "reports" / f"KG_CORE_EDGE_TYPING_{args.date}.json"

    def dist_table(title: str, before: Counter, after: Counter) -> list[str]:
        keys = sorted(set(before) | set(after), key=lambda k: -after.get(k, 0))
        rows = [f"### {title}", "", "| 谓词 | 前 | 后 | Δ |", "|:---|---:|---:|---:|"]
        for k in keys:
            b, a = before.get(k, 0), after.get(k, 0)
            rows.append(f"| {k} | {b} | {a} | {a - b:+d} |")
        rows.append("")
        return rows

    lines = [
        "# KG 核心边语义类型化（relatedTo 反塌缩）",
        "",
        f"**日期**: {args.date}  **核心实体**: {len(core)}  "
        f"**核心子集边**: {len(core_edges)} → {len(core_edges_after)}  **改动**: {len(changes)}  ",
        f"**模式**: {'dry-run（未写回）' if args.dry_run else '已写回 kg_data_v3.json'}",
        "",
        "## 规则",
        "",
        "- R1 策展互斥 → `ex:mutexWith`（依据为权威页原句，见下文各行）",
        "- R2 策展反例 → `ex:counterExample`（A 页反例章节反驳 B 的朴素假设）",
        "- R3 策展精化 → `ex:refines`（A 为 B 的进阶/模式/机制展开）",
        "- R4 前置元数据 → `ex:dependsOn`（目标在源页 前置概念/前置依赖 元数据中）",
        "- R5 后置元数据 → `ex:entails`（目标在源页 后置概念/后置延伸 元数据中）",
        "",
        "## 分布前后对比",
        "",
    ]
    lines += dist_table("核心子集（L1–L3 九大主题）", before_core, after_core)
    lines += dist_table("全局 KG", before_global, after_global)
    lines += ["## 逐边改动与依据", "",
              "| 规则 | 动作 | 主语 | 谓词 | 宾语 | 依据 |",
              "|:---|:---|:---|:---|:---|:---|"]
    for c in changes:
        ev = c["evidence"].replace("|", "\\|")
        lines.append(f"| {c['rule']} | {c['action']} | {c['subject']} | {c['predicate']} "
                     f"| {c['object']} | {ev} |")
    lines.append("")
    lines.append("## 机器可读")
    lines.append("")
    lines.append(f"- JSON: `reports/KG_CORE_EDGE_TYPING_{args.date}.json`")

    out_json.write_text(json.dumps({
        "date": args.date, "dry_run": args.dry_run,
        "core_entities": len(core), "changes": len(changes),
        "before_core": dict(before_core), "after_core": dict(after_core),
        "before_global": dict(before_global), "after_global": dict(after_global),
        "changes_detail": changes,
    }, ensure_ascii=False, indent=2), encoding="utf-8")
    out_md.write_text("\n".join(lines), encoding="utf-8")

    if not args.dry_run:
        meta = data.get("metadata")
        if isinstance(meta, dict) and "relation_count" in meta:
            meta["relation_count"] = len(relations)
        KG_PATH.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")

    print(f"[type_kg_core_edges] core={len(core)} changes={len(changes)} dry_run={args.dry_run}")
    print(f"  core before={dict(before_core)}")
    print(f"  core after ={dict(after_core)}")
    print(f"  global relatedTo: {before_global.get(PRED_REL, 0)} → {after_global.get(PRED_REL, 0)} "
          f"(of {sum(before_global.values())} → {sum(after_global.values())})")
    print(f"  report: {out_md.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
