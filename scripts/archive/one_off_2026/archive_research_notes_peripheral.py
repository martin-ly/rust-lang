#!/usr/bin/env python3
"""
归档 docs/research_notes/ 中边缘/重复/低价值的文件。

目标类别：
- experiments/（性能实验笔记）
- software_design_theory/ 中的设计模式、执行模型、分布式模式、工作流矩阵等
- formal_methods/ 中的 mindmap/decision_tree/matrix/proof_tree 等辅助索引
- research_notes 根目录中的 mindmap/decision_tree/matrix/proof_tree/distributed/workflow 文件

保留文件（即使匹配也不归档）：
- 根 README.md、INDEX.md、10_research_notes_organization.md
- formal_methods/ 中核心形式化文件（ownership_model、borrow_checker_proof、lifetime、send_sync、pin、async_state_machine、separation_logic、axiomatic/operational semantics 等）
- type_theory/ 中核心类型理论文件
- software_design_theory/06_rust_idioms.md、07_anti_patterns.md、07_crate_architectures/、10_00_master_index.md
- 10_safe_unsafe_comprehensive_analysis.md
"""

from __future__ import annotations

import argparse
import re
import shutil
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RESEARCH_NOTES = ROOT / "docs" / "research_notes"
ARCHIVE_DIR = ROOT / "archive" / "research_notes_2026_06_25"

# 保留路径模式（相对 RESEARCH_NOTES 的 POSIX 路径，支持 * 通配）
RETAIN_PATTERNS = [
    "README.md",
    "INDEX.md",
    "10_research_notes_organization.md",
    "10_safe_unsafe_comprehensive_analysis.md",
    "formal_methods/10_ownership_model.md",
    "formal_methods/10_borrow_checker_proof.md",
    "formal_methods/10_lifetime_formalization.md",
    "formal_methods/10_send_sync_formalization.md",
    "formal_methods/10_async_state_machine.md",
    "formal_methods/10_pin_self_referential.md",
    "formal_methods/10_separation_logic.md",
    "formal_methods/10_axiomatic_semantics.md",
    "formal_methods/10_operational_semantics.md",
    "formal_methods/lifetime_formalization.md",
    "formal_methods/10_coq_formalization_guide.md",
    "type_theory/*.md",
    "software_design_theory/06_rust_idioms.md",
    "software_design_theory/07_anti_patterns.md",
    "software_design_theory/10_00_master_index.md",
    "software_design_theory/07_crate_architectures/**/*.md",
]

# 归档路径模式（相对 RESEARCH_NOTES 的 POSIX 路径，支持 ** 递归）
ARCHIVE_PATTERNS = [
    "experiments/**/*.md",
    "software_design_theory/01_design_patterns_formal/**/*.md",
    "software_design_theory/02_workflow*/**/*.md",
    "software_design_theory/03_execution_models/**/*.md",
    "software_design_theory/04_compositional_engineering/**/*.md",
    "software_design_theory/05_boundary_system/**/*.md",
    "software_design_theory/05_distributed/**/*.md",
    "10_*_mindmap*.md",
    "10_*_decision_tree*.md",
    "10_*_matrix*.md",
    "10_proof_tree*.md",
    "10_distributed_*.md",
    "10_workflow_*.md",
    "formal_methods/10_*_mindmap*.md",
    "formal_methods/10_*_decision_tree*.md",
    "formal_methods/10_*_matrix*.md",
    "formal_methods/10_proof_tree*.md",
    "formal_methods/10_formal_methods_*_completion*.md",
    "formal_methods/10_implementation_progress_matrix.md",
    "formal_methods/10_learning_progression_matrix.md",
    "formal_methods/10_proof_completion_matrix.md",
    "formal_methods/10_risk_assessment_matrix.md",
    "formal_methods/10_safe_decidable_mechanisms_and_formal_methods_plan.md",
    "formal_methods/10_reference_cycles_formalization.md",
    "formal_modules/**/*.md",
]


def matches_any(rel: Path, patterns: list[str]) -> bool:
    rel_posix = rel.as_posix()
    for pat in patterns:
        if "**" in pat:
            # 简单实现：将 ** 转换为通配任意目录
            regex = pat.replace(".", r"\.")
            regex = regex.replace("**", "<<DOUBLESTAR>>")
            regex = regex.replace("*", "[^/]*")
            regex = regex.replace("<<DOUBLESTAR>>", ".*")
            regex = regex + "$"
            if re.match(regex, rel_posix):
                return True
        else:
            if re.match(pat.replace("*", "[^/]*") + "$", rel_posix):
                return True
    return False


def collect_all_references() -> set[Path]:
    refs: set[Path] = set()
    for path in ROOT.rglob("*.md"):
        if any(p in ("archive", "target", ".git") for p in path.parts):
            continue
        text = path.read_text(encoding="utf-8", errors="ignore")
        for note in RESEARCH_NOTES.rglob("*.md"):
            if note in refs:
                continue
            rel = note.relative_to(ROOT).as_posix()
            escaped = re.escape(rel)
            if re.search(rf"\]\([^)]*{escaped}[)#]?", text):
                refs.add(note)
    return refs


def build_report(moved: list[Path], tagged: list[Path]) -> str:
    lines = ["# research_notes 边缘内容归档报告\n"]
    lines.append(f"- **归档时间**: {datetime.now().strftime('%Y-%m-%d')}\n")
    lines.append(f"- **移动文件数**: {len(moved)}\n")
    lines.append(f"- **标记但未移动文件数**: {len(tagged)}\n\n")
    lines.append("## 已移动文件\n\n")
    for p in moved:
        lines.append(f"- `{p.relative_to(ROOT).as_posix()}`\n")
    lines.append("\n## 已标记归档但未移动（被引用）\n\n")
    for p in tagged:
        lines.append(f"- `{p.relative_to(ROOT).as_posix()}`\n")
    return "".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="归档 docs/research_notes/ 边缘内容")
    parser.add_argument("--dry-run", action="store_true", help="仅打印候选清单")
    parser.add_argument("--yes", action="store_true", help="跳过确认")
    args = parser.parse_args(argv)

    ARCHIVE_DIR.mkdir(parents=True, exist_ok=True)
    refs = collect_all_references()

    candidates = []
    for path in sorted(RESEARCH_NOTES.rglob("*.md")):
        rel = path.relative_to(RESEARCH_NOTES)
        if matches_any(rel, RETAIN_PATTERNS):
            continue
        if not matches_any(rel, ARCHIVE_PATTERNS):
            continue
        candidates.append(path)

    print(f"候选归档文件: {len(candidates)}")

    if args.dry_run:
        for p in candidates:
            status = "[被引用-将标记]" if p in refs else "[将移动]"
            print(f"{status} {p.relative_to(ROOT)}")
        return 0

    if not candidates:
        print("没有候选文件。")
        return 0

    if not args.yes:
        resp = input("确认执行？输入 yes 继续: ")
        if resp.strip().lower() != "yes":
            print("已取消。")
            return 1

    moved = []
    tagged = []
    for path in candidates:
        if path in refs:
            text = path.read_text(encoding="utf-8")
            if not text.startswith("> **归档提示**"):
                header = (
                    "> **归档提示**: 本文档内容为研究笔记，自 2026-03 前后未再更新，"
                    "于 2026-06-25 标记为归档参考。核心结论请优先查阅 `concept/` 与 `knowledge/`。\n\n"
                )
                path.write_text(header + text, encoding="utf-8")
                tagged.append(path)
        else:
            rel = path.relative_to(RESEARCH_NOTES)
            dest = ARCHIVE_DIR / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.move(str(path), str(dest))
            moved.append(path)

    print(f"\n✅ 已移动 {len(moved)} 个文件到 {ARCHIVE_DIR.relative_to(ROOT)}")
    print(f"✅ 已标记 {len(tagged)} 个被引用文件为归档（未移动）")

    report_path = ROOT / "reports" / "RESEARCH_NOTES_PERIPHERAL_ARCHIVE_2026_06_25.md"
    report_path.write_text(build_report(moved, tagged), encoding="utf-8")
    print(f"\n📄 报告已生成: {report_path.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
