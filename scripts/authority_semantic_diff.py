#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""权威语义关键词覆盖扫描器（原型）。

对 `concept/` 中核心权威页做静态关键词覆盖检查，判断这些页面是否包含
国际化权威来源（Reference / Nomicon / TRPL / Async Book）强调的关键语义词。
当前为观察门原型：默认 exit 0，输出缺失关键词供人工复核；--strict 时若
核心页存在 P0 级缺失则 exit 1。

扫描范围（可配置）：
  - 所有权 / 借用 / 生命周期
  - Unsafe / 内存模型 / UB
  - Async / Pin
  - 类型系统 / Trait
"""
from __future__ import annotations

import argparse
import glob
import os
import re
import sys
from dataclasses import dataclass
from typing import Dict, List, Tuple

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# 主题 -> (glob 模式, 必须出现的关键词列表)
# 关键词来自 Rust Reference / Nomicon / Async Book / std docs 等权威来源。
SEMANTIC_EXPECTATIONS: Dict[str, Tuple[str, List[str]]] = {
    "lifetimes": (
        "concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md",
        ["elision", "trait object", "'static", "'_", "function pointer", "lifetime elision"],
    ),
    "variance": (
        "concept/04_formal/00_type_theory/02_subtype_variance.md",
        ["PhantomData", "dyn Trait", "covariant", "contravariant", "invariant", "variance"],
    ),
    "unsafe_ub": (
        "concept/04_formal/01_ownership_logic/06_behavior_considered_undefined.md",
        ["isize::MAX", "misaligned", "padding", "MaybeUninit", "union", "valid-for-read", "valid-for-write"],
    ),
    "async": (
        "concept/03_advanced/01_async/01_async.md",
        ["IntoFuture", "Pin::new_unchecked", "poll", "Future::poll", "async unsafe fn", "drop order"],
    ),
    "pin": (
        "concept/03_advanced/01_async/08_pin_unpin.md",
        ["structural pinning", "Pin::set", "ManuallyDrop", "Pin::new_unchecked", "projection"],
    ),
    "ffi": (
        "concept/03_advanced/04_ffi/01_rust_ffi.md",
        ["extern block", "unsafe extern", "ABI", "static", "#[no_mangle]", "repr(C)"],
    ),
    "type_system": (
        "concept/01_foundation/02_type_system/01_type_system.md",
        ["nominal type", "recursive type", "str", "primitive type", "HM", "principal type"],
    ),
}

# P0 级关键词：缺失即视为与权威来源存在明显语义对称差
P0_KEYWORDS: Dict[str, List[str]] = {
    "lifetimes": ["elision", "'static"],
    "variance": ["variance", "PhantomData"],
    "unsafe_ub": ["isize::MAX", "MaybeUninit"],
    "async": ["IntoFuture", "poll"],
    "pin": ["structural pinning", "Pin::set"],
    "ffi": ["extern block", "unsafe extern"],
    "type_system": ["recursive type", "str"],
}


@dataclass
class Finding:
    topic: str
    path: str
    keyword: str
    level: str  # P0 or P1


def scan_topic(topic: str, pattern: str, keywords: List[str]) -> List[Finding]:
    findings = []
    path = os.path.join(ROOT, pattern)
    if not os.path.exists(path):
        return [Finding(topic, pattern, "<file missing>", "P0")]
    text = open(path, encoding="utf-8", errors="ignore").read().lower()
    p0_set = {k.lower() for k in P0_KEYWORDS.get(topic, [])}
    for kw in keywords:
        kw_lower = kw.lower()
        # 允许出现在代码块、正文或标题中
        if kw_lower not in text:
            level = "P0" if kw_lower in p0_set else "P1"
            findings.append(Finding(topic, pattern, kw, level))
    return findings


def main() -> int:
    parser = argparse.ArgumentParser(description="Semantic keyword coverage scanner against authority sources")
    parser.add_argument("--strict", action="store_true", help="Exit 1 if any P0 keyword is missing")
    parser.add_argument("--json", help="Write findings to JSON file")
    args = parser.parse_args()

    all_findings: List[Finding] = []
    for topic, (pattern, keywords) in SEMANTIC_EXPECTATIONS.items():
        all_findings.extend(scan_topic(topic, pattern, keywords))

    p0 = [f for f in all_findings if f.level == "P0"]
    p1 = [f for f in all_findings if f.level == "P1"]

    print(f"[authority_semantic_diff] P0={len(p0)} P1={len(p1)}")
    if not all_findings:
        print("✅ 所有核心页均覆盖权威语义关键词。")
        return 0

    if p0:
        print("\n=== P0 缺失（建议立即补齐）===")
        for f in p0:
            print(f"  {f.path} 缺 [{f.keyword}]（主题: {f.topic}）")
    if p1:
        print("\n=== P1 缺失（建议逐步补齐）===")
        for f in p1:
            print(f"  {f.path} 缺 [{f.keyword}]（主题: {f.topic}）")

    if args.json:
        import json
        payload = [
            {"topic": f.topic, "path": f.path, "keyword": f.keyword, "level": f.level}
            for f in all_findings
        ]
        with open(args.json, "w", encoding="utf-8") as jf:
            json.dump(payload, jf, ensure_ascii=False, indent=2)
        print(f"\n📝 JSON 报告: {args.json}")

    if args.strict and p0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
