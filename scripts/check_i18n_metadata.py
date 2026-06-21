#!/usr/bin/env python3
"""扫描 concept/ 下 Markdown 文件的国际化元数据覆盖率."""
import os
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent / "concept"
EN_RE = re.compile(r'^>\s*\*\*EN\*\*:\s*(.*)$', re.MULTILINE)
SUMMARY_RE = re.compile(r'^>\s*\*\*Summary\*\*:\s*(.*)$', re.MULTILINE)
SOURCE_RE = re.compile(r'^>\s*\*\*来源\*\*:\s*(.*)$', re.MULTILINE)

placeholder_en = {"(Chinese)", "Core Rust concept.", "", "(待补充)", "(TBD)"}
placeholder_summary = {"Core Rust concept.", "(待补充)", "(TBD)", ""}


def is_placeholder_en(text: str) -> bool:
    t = text.strip()
    return t in placeholder_en or not t or "(Chinese)" in t or "Core Rust concept." in t


def is_placeholder_summary(text: str) -> bool:
    t = text.strip()
    return t in placeholder_summary or not t or t.startswith("Core Rust concept.") and len(t) <= len("Core Rust concept. X") + 5


def main():
    files = sorted([p for p in ROOT.rglob("*.md") if p.is_file()])
    total = len(files)
    missing_en, missing_summary, missing_source = [], [], []
    placeholder_en_files, placeholder_summary_files = [], []
    en_count = summary_count = source_count = 0
    for p in files:
        text = p.read_text(encoding="utf-8")
        en = EN_RE.search(text)
        summary = SUMMARY_RE.search(text)
        source = SOURCE_RE.search(text)
        rel = p.relative_to(ROOT).as_posix()
        if en:
            en_count += 1
            if is_placeholder_en(en.group(1)):
                placeholder_en_files.append(rel)
        else:
            missing_en.append(rel)
        if summary:
            summary_count += 1
            if is_placeholder_summary(summary.group(1)):
                placeholder_summary_files.append(rel)
        else:
            missing_summary.append(rel)
        if source and source.group(1).strip():
            source_count += 1
        else:
            missing_source.append(rel)

    print("# 概念文件国际化元数据覆盖率报告\n")
    print(f"扫描文件数: {total}\n")
    print("| 指标 | 覆盖数 | 覆盖率 |")
    print("|------|-------:|-------:|")
    print(f"| EN 标题 | {en_count} / {total} | {en_count/total*100:.1f}% |")
    print(f"| Summary | {summary_count} / {total} | {summary_count/total*100:.1f}% |")
    print(f"| 来源链接 | {source_count} / {total} | {source_count/total*100:.1f}% |")
    print()
    if missing_en:
        print(f"## 缺失 EN 标题（{len(missing_en)} 个）\n")
        for f in missing_en[:30]:
            print(f"- {f}")
        print()
    if placeholder_en_files:
        print(f"## 占位 EN 标题（{len(placeholder_en_files)} 个）\n")
        for f in placeholder_en_files[:30]:
            print(f"- {f}")
        print()
    if missing_summary:
        print(f"## 缺失 Summary（{len(missing_summary)} 个）\n")
        for f in missing_summary[:30]:
            print(f"- {f}")
        print()
    if placeholder_summary_files:
        print(f"## 占位 Summary（{len(placeholder_summary_files)} 个）\n")
        for f in placeholder_summary_files[:30]:
            print(f"- {f}")
        print()
    if missing_source:
        print(f"## 缺失来源链接（{len(missing_source)} 个）\n")
        for f in missing_source[:30]:
            print(f"- {f}")
        print()

    # 写报告
    report_path = Path(__file__).resolve().parent.parent / "reports" / "i18n_metadata_report.md"
    report_path.parent.mkdir(parents=True, exist_ok=True)
    lines = ["# 概念文件国际化元数据覆盖率报告\n", f"扫描文件数: {total}\n\n"]
    lines += ["| 指标 | 覆盖数 | 覆盖率 |\n", "|------|-------:|-------:|\n"]
    lines.append(f"| EN 标题 | {en_count} / {total} | {en_count/total*100:.1f}% |\n")
    lines.append(f"| Summary | {summary_count} / {total} | {summary_count/total*100:.1f}% |\n")
    lines.append(f"| 来源链接 | {source_count} / {total} | {source_count/total*100:.1f}% |\n\n")
    report_path.write_text("".join(lines), encoding="utf-8")


if __name__ == "__main__":
    main()
