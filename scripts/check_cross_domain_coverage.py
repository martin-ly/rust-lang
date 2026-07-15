#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""check_cross_domain_coverage.py — 检查 Rust 关键交叉/边界语义域的权威覆盖。

Rust 1.97 的复杂语义大量出现在概念交叉与边界处（如 async+unsafe、FFI+async、
const generics+trait objects）。本脚本维护一个“关键交叉主题清单”，检查每个主题
是否在 `concept/` 中有非 stub 的权威页，并输出缺口报告。

清单维护原则：
  - 只收录涉及两个及以上核心域、且 Rust 1.97 稳定或预览中实际存在的语义交叉。
  - 每个主题可映射到一个或多个候选 `concept/` 路径；任一存在且非 stub 即算覆盖。
  - 不覆盖单一核心域内部主题（如所有权基础、async/await 基础），那些由常规
    concept/ 目录结构保证。

退出码：
  默认：输出报告，exit 0
  --strict：存在未覆盖主题时 exit 1

输出：
  reports/CROSS_DOMAIN_COVERAGE_BASELINE_<date>.md
  reports/CROSS_DOMAIN_COVERAGE_BASELINE_<date>.json
"""
from __future__ import annotations

import argparse
import datetime as _dt
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CONCEPT_DIR = ROOT / "concept"

# 关键交叉/边界主题清单：主题名 → 候选权威页路径（相对 concept/）
# 任一候选存在且非 stub 即视为覆盖。
CROSS_DOMAIN_TOPICS: dict[str, list[str]] = {
    "let chains / if-let guards": [
        "01_foundation/04_control_flow/03_let_chains.md",
    ],
    "unsafe extern blocks (Edition 2024)": [
        "03_advanced/04_ffi/05_unsafe_extern_blocks.md",
    ],
    "async + unsafe boundary": [
        "03_advanced/01_async/12_async_unsafe_boundary.md",
        "03_advanced/02_unsafe/08_async_in_unsafe_contexts.md",
    ],
    "FFI + async boundary": [
        "03_advanced/04_ffi/06_async_ffi_boundary.md",
        "03_advanced/04_ffi/04_async_ffi_boundary.md",
    ],
    "no_std + async": [
        "06_ecosystem/05_systems_and_embedded/12_async_no_std_embedded.md",
        "06_ecosystem/05_systems_and_embedded/11_async_no_std_embedded.md",
    ],
    "const generics + trait objects": [
        "02_intermediate/01_generics/06_const_generics_and_trait_objects.md",
        "02_intermediate/01_generics/05_const_generics_and_trait_objects.md",
    ],
    "GAT + async": [
        "03_advanced/01_async/14_gat_async_boundary.md",
        "02_intermediate/00_traits/07_generic_associated_types.md",
    ],
    "Send/Sync boundary in trait objects / closures / async state machines": [
        "03_advanced/00_concurrency/04_send_sync_boundaries.md",
        "03_advanced/00_concurrency/02_send_sync_auto_traits.md",
    ],
    "Pin projection + structural projection": [
        "03_advanced/01_async/03_pin_unpin.md",
        "03_advanced/01_async/11_pin_projection_counterexamples.md",
    ],
    "allocator_api / per-container allocators": [
        "03_advanced/06_low_level_patterns/01_custom_allocators.md",
    ],
    "match ergonomics / default binding mode in Edition 2024": [
        "01_foundation/04_control_flow/02_patterns.md",
    ],
    "temporary scope / tail expression drop (Edition 2024)": [
        "04_formal/05_rustc_internals/09_destructors.md",
    ],
    "const trait impl (effects system)": [
        "07_future/02_preview_features/06_const_trait_impl_preview.md",
        "07_future/02_preview_features/19_const_trait_preview.md",
    ],
    "RTN / RPITIT / TAIT precise capturing": [
        "07_future/02_preview_features/17_type_alias_impl_trait_preview.md",
        "07_future/02_preview_features/13_lifetime_capture_preview.md",
        "07_future/03_preview_features/20_return_type_notation_preview.md",
    ],
    "async fn / Future equivalence + Send across await": [
        "03_advanced/01_async/01_async.md",
        "03_advanced/01_async/02_async_state_machine.md",
    ],
    "unsafe op in unsafe fn (Edition 2024)": [
        "03_advanced/02_unsafe/01_unsafe.md",
    ],
}

# stub 标记（出现任一即视为 stub）
STUB_MARKERS = (
    "本文件为学习入口 stub",
    "本文件为专题深度内容入口",
    "本文件保留为重定向",
    "本文件为重定向",
    "stub/archive redirect",
    "archive redirect",
    "redirect",
    "本主题已合并至",
    "完整概念解释请见",
    "通用 Rust 概念解释请见",
)

TITLE_RE = re.compile(r"^#\s+(.+?)\s*$", re.MULTILINE)
EN_RE = re.compile(r"\*\*EN\*\*\s*[:：]\s*(.+?)$", re.MULTILINE)


def is_stub(text: str) -> bool:
    return any(marker in text for marker in STUB_MARKERS)


def check_topic(name: str, candidates: list[str]) -> dict:
    existing = []
    stub_existing = []
    missing = []

    for rel in candidates:
        path = CONCEPT_DIR / rel
        if not path.exists():
            missing.append(rel)
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        title_m = TITLE_RE.search(text)
        en_m = EN_RE.search(text)
        info = {
            "path": rel,
            "title": title_m.group(1).strip() if title_m else "",
            "en": en_m.group(1).strip() if en_m else "",
            "stub": is_stub(text),
        }
        if info["stub"]:
            stub_existing.append(info)
        else:
            existing.append(info)

    covered = bool(existing)
    return {
        "topic": name,
        "covered": covered,
        "authority_pages": existing,
        "stub_pages": stub_existing,
        "missing_candidates": missing,
    }


def evaluate() -> dict:
    results = []
    for name, candidates in CROSS_DOMAIN_TOPICS.items():
        results.append(check_topic(name, candidates))

    covered = [r for r in results if r["covered"]]
    uncovered = [r for r in results if not r["covered"]]

    return {
        "total": len(results),
        "covered_count": len(covered),
        "uncovered_count": len(uncovered),
        "coverage_rate": round(len(covered) / len(results) * 100, 1),
        "topics": results,
    }


def format_report(result: dict, date_str: str) -> str:
    lines = [
        f"# Cross-Domain Semantic Coverage Baseline Report ({date_str})",
        "",
        "> 检查 Rust 1.97 关键交叉/边界语义域在 `concept/` 中是否有非 stub 权威页。",
        "",
        "## 汇总",
        "",
        f"- 总主题数：{result['total']}",
        f"- 已覆盖：{result['covered_count']} ({result['coverage_rate']}%)",
        f"- 未覆盖：{result['uncovered_count']}",
        "",
    ]

    lines.append("## 未覆盖主题")
    lines.append("")
    if not result["uncovered_count"]:
        lines.append("未发现。")
    else:
        for r in result["topics"]:
            if not r["covered"]:
                lines.append(f"### {r['topic']}")
                lines.append("")
                if r["stub_pages"]:
                    lines.append("存在 stub 页，需充实为权威页：")
                    for s in r["stub_pages"]:
                        lines.append(f"- `{s['path']}` — {s['title']} ({s['en']})")
                if r["missing_candidates"]:
                    lines.append("候选路径均不存在，需新建：")
                    for m in r["missing_candidates"]:
                        lines.append(f"- `{m}`")
                lines.append("")

    lines.append("## 已覆盖主题")
    lines.append("")
    for r in result["topics"]:
        if r["covered"]:
            page = r["authority_pages"][0]
            lines.append(f"- ✅ `{page['path']}` — {r['topic']}")
    lines.append("")

    lines.append("## 主题清单维护说明")
    lines.append("")
    lines.append("清单位于 `scripts/check_cross_domain_coverage.py` 的 `CROSS_DOMAIN_TOPICS` 字典。")
    lines.append("新增主题时，需给出候选 `concept/` 权威页路径；覆盖标准：任一候选存在且非 stub。")
    lines.append("")

    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="检查 Rust 关键交叉/边界语义域的权威覆盖")
    parser.add_argument("--strict", action="store_true", help="存在未覆盖主题时 exit 1")
    parser.add_argument("--json", action="store_true", help="仅输出 JSON 到 stdout")
    parser.add_argument("--report", action="store_true", help="写入 reports/ 文件")
    args = parser.parse_args()

    result = evaluate()
    date_str = _dt.datetime.now().strftime("%Y_%m_%d")

    if args.json:
        print(json.dumps(result, ensure_ascii=False, indent=2))
        return 0

    report = format_report(result, date_str)
    print(report)

    if args.report:
        reports_dir = ROOT / "reports"
        reports_dir.mkdir(exist_ok=True)
        md_path = reports_dir / f"CROSS_DOMAIN_COVERAGE_BASELINE_{date_str}.md"
        json_path = reports_dir / f"CROSS_DOMAIN_COVERAGE_BASELINE_{date_str}.json"
        md_path.write_text(report, encoding="utf-8")
        json_path.write_text(json.dumps(result, ensure_ascii=False, indent=2), encoding="utf-8")
        print(f"\n报告已写入：\n  {md_path}\n  {json_path}", file=sys.stderr)

    if args.strict and result["uncovered_count"] > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
