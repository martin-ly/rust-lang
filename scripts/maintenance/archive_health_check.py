#!/usr/bin/env python3
"""
归档健康检查脚本

用于定期检查：
1. archive/ 子目录 README 是否错误地声明为“活跃/持续维护”。
2. docs/research_notes/ 是否仍存在应归档的重复低价值文件。
3. tmp/ 工作区是否残留临时文件。
4. docs/ / knowledge/ 中的 redirect stub 是否缺少“历史内容已迁移”状态标记。

用法：
    python scripts/maintenance/archive_health_check.py [--json]
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]

RESEARCH_NOTES = ROOT / "docs" / "research_notes"
ARCHIVE_RESEARCH_NOTES = ROOT / "archive" / "research_notes_2026_06_25"
TMP_DIR = ROOT / "tmp"

# 与已归档脚本 scripts/archive/one_off_2026/archive_research_notes_candidates.py 保持一致的黑名单
BLACKLIST_PATTERNS = [
    r"(^|/)10_template\.md$",
    r"(^|/)10_feature_template\.md$",
    r"(^|/)10_example\.md$",
    r"(^|/)10_writing_guide\.md$",
    r"(^|/)10_contributing\.md$",
    r"(^|/)10_quality_checklist\.md$",
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
    r"10_rust_191_",
    r"10_rust_192_",
    r"10_rust_193_",
    r"10_rust_194_",
    r"10_cargo_194_features",
    r"10_aeneas_integration_plan",
    r"10_coq_of_rust_integration_plan",
    r"10_coq_isabelle_proof_scaffolding",
]

RETAIN_PATHS = {
    RESEARCH_NOTES / "README.md",
    RESEARCH_NOTES / "INDEX.md",
    RESEARCH_NOTES / "10_research_notes_organization.md",
}

FORBIDDEN_STATUS_PATTERNS = [
    re.compile(r"持续完善"),
    re.compile(r"持续更新"),
    re.compile(r"持续整合"),
    re.compile(r"持续扩充"),
    re.compile(r"活跃开发"),
    re.compile(r"🚧"),
    re.compile(r"🟢"),
]

ARCHIVE_README_CANDIDATES = [
    ROOT / "archive" / "cargo_package_management_from_c02" / "README.md",
    ROOT / "archive" / "content" / "academic" / "README.md",
    ROOT / "archive" / "content" / "ecosystem" / "README.md",
    ROOT / "archive" / "content" / "emerging" / "README.md",
    ROOT / "archive" / "content" / "production" / "README.md",
    ROOT / "archive" / "docs" / "README.md",
]


@dataclass
class Finding:
    category: str
    file: Path
    message: str
    line: int | None = None


@dataclass
class Report:
    findings: list[Finding] = field(default_factory=list)

    def add(self, category: str, file: Path, message: str, line: int | None = None) -> None:
        self.findings.append(Finding(category, file, message, line))


def is_blacklisted(rel: Path) -> bool:
    s = rel.as_posix()
    return any(re.search(pat, s) for pat in BLACKLIST_PATTERNS)


def check_archive_readme_status(report: Report) -> None:
    for readme in ARCHIVE_README_CANDIDATES:
        if not readme.exists():
            continue
        text = readme.read_text(encoding="utf-8", errors="ignore")
        for i, line in enumerate(text.splitlines(), start=1):
            for pat in FORBIDDEN_STATUS_PATTERNS:
                if pat.search(line):
                    report.add(
                        "archive_active_status",
                        readme,
                        f"归档 README 仍包含活跃/维护标记：{line.strip()}",
                        i,
                    )
                    break


def check_research_notes_duplicates(report: Report) -> None:
    for path in sorted(RESEARCH_NOTES.rglob("*.md")):
        if path in RETAIN_PATHS:
            continue
        rel = path.relative_to(RESEARCH_NOTES)
        if not is_blacklisted(rel):
            continue
        archive_copy = ARCHIVE_RESEARCH_NOTES / rel
        if archive_copy.exists():
            report.add(
                "research_notes_duplicate",
                path,
                f"docs/research_notes 文件与 archive 副本重复，建议清理：{rel.as_posix()}",
            )


def check_tmp_residual(report: Report) -> None:
    if not TMP_DIR.exists():
        return
    for path in TMP_DIR.iterdir():
        if path.name in {"__pycache__"}:
            continue
        report.add("tmp_residual", path, f"tmp/ 目录残留文件：{path.name}")


def check_stub_markers(report: Report) -> None:
    """检查 docs/ 和 knowledge/ 中简短的 redirect stub 是否缺少迁移说明。"""
    stub_indicator = "(stub/archive redirect)"
    migration_markers = ["历史内容已迁移", "内容已迁移", "不再维护", "已合并到权威来源", "已统一归档", "已重定向"]
    status_pattern = re.compile(r"\*\*状态\*\*.*(?:历史内容已迁移|内容已迁移|不再维护)")
    for base in (ROOT / "docs", ROOT / "knowledge"):
        for path in base.rglob("*.md"):
            if "archive" in path.parts:
                continue
            # 只关注轻量 stub（< 2KB），避免把带标注的长文误判
            if path.stat().st_size > 2048:
                continue
            text = path.read_text(encoding="utf-8", errors="ignore")
            head = "\n".join(text.splitlines()[:10])
            if stub_indicator not in head:
                continue
            if status_pattern.search(text):
                continue
            if any(marker in text for marker in migration_markers):
                continue
            report.add(
                "stub_missing_status",
                path,
                "redirect/stub 文件缺少迁移说明或 '> **状态**: 历史内容已迁移' 标记",
            )


def print_text_report(report: Report) -> None:
    if not report.findings:
        print("✅ Archive health check passed. No issues found.")
        return
    print(f"⚠️ Archive health check found {len(report.findings)} issue(s):\n")
    for f in report.findings:
        loc = f" (line {f.line})" if f.line else ""
        print(f"[{f.category}]{loc} {f.file.relative_to(ROOT)}")
        print(f"  {f.message}\n")


def print_json_report(report: Report) -> None:
    data = [
        {
            "category": f.category,
            "file": f.file.relative_to(ROOT).as_posix(),
            "message": f.message,
            "line": f.line,
        }
        for f in report.findings
    ]
    print(json.dumps(data, ensure_ascii=False, indent=2))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Archive health check")
    parser.add_argument("--json", action="store_true", help="Output JSON")
    args = parser.parse_args(argv)

    report = Report()
    check_archive_readme_status(report)
    check_research_notes_duplicates(report)
    check_tmp_residual(report)
    check_stub_markers(report)

    if args.json:
        print_json_report(report)
    else:
        print_text_report(report)

    return 1 if report.findings else 0


if __name__ == "__main__":
    raise SystemExit(main())
