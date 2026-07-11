#!/usr/bin/env python3
"""
归档迁移脚本：将 docs/research_notes/ 中评估为"归档候选"的文件移动到 archive/research_notes_2026_06_25/。

归档标准（满足任一即可）：
1. 属于黑名单类别（模板、进度/完成/证书/统计、过时版本更新、已重定向计划文件）。
2. 最后更新 > stale_days（默认 150）且未被项目内 .md 文件引用。

对于被引用的旧文件，仅添加归档提示头部，不移动。
"""

from __future__ import annotations

import argparse
import re
import shutil
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RESEARCH_NOTES = ROOT / "docs" / "research_notes"
ARCHIVE_DIR = ROOT / "archive" / "research_notes_2026_06_25"

# 低价值文件名黑名单（正则，匹配 relative path 字符串）
BLACKLIST_PATTERNS = [
    # 模板与写作指南
    r"(^|/)10_template\.md$",
    r"(^|/)10_feature_template\.md$",
    r"(^|/)10_example\.md$",
    r"(^|/)10_writing_guide\.md$",
    r"(^|/)10_contributing\.md$",
    r"(^|/)10_quality_checklist\.md$",
    # 进度/完成/证书/统计
    r"10_100_percent_completion",
    r"10_actual_completion_status",
    r"10_comprehensive_task_orchestration",
    r"10_final_100_percent",
    r"10_final_completion",
    r"10_final_verification_checklist",
    r"10_formal_argumentation_completion_report",
    r"10_progress_tracking",
    r"10_project_completion",
    r"10_statistics",
    r"10_task_checklist",
    r"10_maintenance_guide",
    r"10_project_maintenance_guide",
    # 过时版本更新笔记
    r"10_rust_191_",
    r"10_rust_192_",
    r"10_rust_193_",
    r"10_rust_194_",
    r"10_cargo_194_features",
    # 已重定向到 archive/deprecated/ 的计划文件
    r"10_aeneas_integration_plan",
    r"10_coq_of_rust_integration_plan",
    r"10_coq_isabelle_proof_scaffolding",
]


def parse_last_update(text: str) -> datetime | None:
    patterns = [
        r"\*\*最后更新\*\*[:：]\s*(\d{4}-\d{2}-\d{2})",
        r"最后更新[:：]\s*(\d{4}-\d{2}-\d{2})",
    ]
    for pat in patterns:
        m = re.search(pat, text)
        if m:
            return datetime.strptime(m.group(1), "%Y-%m-%d").replace(tzinfo=timezone.utc)
    return None


def collect_all_references() -> set[Path]:
    """检查项目内所有 .md 文件对 research_notes/ 的引用。"""
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


def is_blacklisted(rel: Path) -> bool:
    rel_str = rel.as_posix()
    return any(re.search(pat, rel_str) for pat in BLACKLIST_PATTERNS)


def build_report(moved: list[Path], tagged: list[Path]) -> str:
    lines = ["# research_notes 批量归档报告\n"]
    lines.append(f"- **归档时间**: {datetime.now().strftime('%Y-%m-%d')}\n")
    lines.append(f"- **移动文件数**: {len(moved)}\n")
    lines.append(f"- **标记但未移动文件数**: {len(tagged)}\n\n")
    lines.append("## 已移动文件\n\n")
    for p in moved:
        lines.append(f"- `{p.relative_to(ROOT).as_posix()}` → `{ARCHIVE_DIR.relative_to(ROOT).as_posix()}/{p.relative_to(RESEARCH_NOTES).as_posix()}`\n")
    lines.append("\n## 已标记归档但未移动（被引用）\n\n")
    for p in tagged:
        lines.append(f"- `{p.relative_to(ROOT).as_posix()}`\n")
    return "".join(lines)


# 即使满足归档条件也保留的入口/导航文件
RETAIN_PATHS = {
    RESEARCH_NOTES / "README.md",
    RESEARCH_NOTES / "INDEX.md",
    RESEARCH_NOTES / "10_research_notes_organization.md",
}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="批量归档 docs/research_notes/ 低价值文件")
    parser.add_argument("--stale-days", type=int, default=150, help="超过多少天未更新视为陈旧（默认 150）")
    parser.add_argument("--dry-run", action="store_true", help="仅打印候选清单，不实际移动")
    parser.add_argument("--yes", action="store_true", help="跳过确认直接执行")
    args = parser.parse_args(argv)

    ARCHIVE_DIR.mkdir(parents=True, exist_ok=True)
    refs = collect_all_references()

    candidates_moved = []
    candidates_tagged = []

    for path in sorted(RESEARCH_NOTES.rglob("*.md")):
        if path in RETAIN_PATHS:
            continue
        text = path.read_text(encoding="utf-8", errors="ignore")
        rel = path.relative_to(RESEARCH_NOTES)
        blacklisted = is_blacklisted(rel)

        last_update = parse_last_update(text)
        age_days = (datetime.now(timezone.utc) - last_update).days if last_update else None
        stale = age_days is not None and age_days > args.stale_days

        if not (blacklisted or stale):
            continue

        if path in refs:
            candidates_tagged.append(path)
        else:
            candidates_moved.append(path)

    print(f"候选移动文件: {len(candidates_moved)}")
    print(f"候选标记文件: {len(candidates_tagged)}")

    if args.dry_run:
        print("\n--- 仅模拟，未执行任何更改 ---")
        for p in candidates_moved:
            print(f"[将移动] {p.relative_to(ROOT)}")
        for p in candidates_tagged:
            print(f"[将标记] {p.relative_to(ROOT)}")
        return 0

    if not (candidates_moved or candidates_tagged):
        print("没有需要归档的候选文件。")
        return 0

    if not args.yes:
        resp = input("确认执行？输入 yes 继续: ")
        if resp.strip().lower() != "yes":
            print("已取消。")
            return 1

    moved = []
    tagged = []

    for path in candidates_moved:
        rel = path.relative_to(RESEARCH_NOTES)
        dest = ARCHIVE_DIR / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.move(str(path), str(dest))
        moved.append(path)

    for path in candidates_tagged:
        text = path.read_text(encoding="utf-8")
        if text.startswith("> **归档提示**"):
            continue
        header = (
            "> **归档提示**: 本文档内容为研究笔记，自 2026-03 前后未再更新，"
            "于 2026-06-25 标记为归档参考。核心结论请优先查阅 `concept/` 与 `knowledge/`。\n\n"
        )
        path.write_text(header + text, encoding="utf-8")
        tagged.append(path)

    print(f"\n✅ 已移动 {len(moved)} 个文件到 {ARCHIVE_DIR.relative_to(ROOT)}")
    for p in moved:
        print(f"  - {p.relative_to(ROOT)}")

    print(f"\n✅ 已标记 {len(tagged)} 个被引用文件为归档（未移动）")
    for p in tagged:
        print(f"  - {p.relative_to(ROOT)}")

    report_path = ROOT / "reports" / "RESEARCH_NOTES_ARCHIVE_BATCH_2026_06_25.md"
    report_path.write_text(build_report(moved, tagged), encoding="utf-8")
    print(f"\n📄 归档报告已生成: {report_path.relative_to(ROOT)}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
