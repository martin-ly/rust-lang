#!/usr/bin/env python3
"""
自动将高相似度非 concept/ 文件替换为指向 concept/ 权威来源的重定向。

用法:
    python scripts/auto_dedup_redirect.py [--dry-run] [report_path]

默认读取 reports/CONTENT_OVERLAP_DETECTION_YYYY_MM_DD.md。
"""

from pathlib import Path
from collections import defaultdict
import re
import os
import argparse
from datetime import datetime

PROJECT_ROOT = Path(".").resolve()

# 以下文件即使出现在高相似度报告中，也不自动替换为重定向
#（例如：速查表、不同版本专题、特定映射页等）
SKIP_PATHS = {
    "docs/03_reference/quick_reference/21_rust_197_features_cheatsheet.md",
    "docs/09_toolchain/10_rust_1_97_features.md",
    "docs/02_learning/03_google_rust_mapping.md",
}

DEFAULT_REPORT = sorted(
    PROJECT_ROOT.glob("reports/CONTENT_OVERLAP_DETECTION_*.md"),
    key=lambda p: p.stat().st_mtime,
    reverse=True,
)[0]
THRESHOLD = 0.75


def extract_title(filepath):
    try:
        content = filepath.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return Path(filepath).stem.replace("_", " ")
    match = re.search(r"^#\s+(.+)$", content, re.MULTILINE)
    return match.group(1).strip() if match else Path(filepath).stem.replace("_", " ")


def relative_link(from_file, to_file):
    # 计算从 from_file 所在目录到 to_file 的相对路径
    from_dir = Path(from_file).parent
    rel = os.path.relpath(to_file, from_dir)
    return rel.replace("\\", "/")


def redirect_content(source, target, title):
    target_link = relative_link(source, target)
    target_display = "/".join(Path(target).relative_to(PROJECT_ROOT).parts)
    return f"""# {title}

> **注意**: 本主题内容已整合到 `{target_display}`。
> 请以 [{target_display}]({target_link}) 为权威来源。

---

**历史内容已迁移**：本文件不再维护，请点击上方链接查看最新内容。
"""


def parse_report(report_path):
    text = report_path.read_text(encoding="utf-8", errors="ignore")
    rows = []
    # 匹配表格行: | 1.00 | `path1` | `path2` | title1 | title2 |
    for line in text.splitlines():
        line = line.strip()
        if not line.startswith("|") or "相似度" in line or "---" in line:
            continue
        parts = [p.strip().strip("`") for p in line.split("|")]
        parts = [p for p in parts if p]
        if len(parts) < 5:
            continue
        try:
            sim = float(parts[0])
        except ValueError:
            continue
        f1, f2 = parts[1], parts[2]
        rows.append((sim, f1, f2))
    return rows


def main():
    parser = argparse.ArgumentParser(description="Auto-dedup redirect generator")
    parser.add_argument("--dry-run", action="store_true", help="预览改动而不写入")
    parser.add_argument("report", nargs="?", default=str(DEFAULT_REPORT), help="重叠检测报告路径")
    args = parser.parse_args()

    report_path = Path(args.report)
    if not report_path.exists():
        print(f"报告不存在: {report_path}")
        return

    rows = parse_report(report_path)
    print(f"读取报告: {report_path}")
    print(f"阈值: {THRESHOLD}，共 {len(rows)} 对记录\n")

    # source -> (target, sim)
    mappings = {}

    for sim, f1, f2 in rows:
        if sim < THRESHOLD:
            continue
        p1 = PROJECT_ROOT / f1.replace("\\", "/")
        p2 = PROJECT_ROOT / f2.replace("\\", "/")
        if not p1.exists() or not p2.exists():
            continue

        in_concept_1 = "concept" in p1.parts
        in_concept_2 = "concept" in p2.parts

        if in_concept_1 and not in_concept_2:
            target, source = p1, p2
        elif in_concept_2 and not in_concept_1:
            target, source = p2, p1
        else:
            # 两者都在或都不在 concept/，跳过自动处理
            continue

        rel_source = source.relative_to(PROJECT_ROOT).as_posix()
        if rel_source in SKIP_PATHS:
            continue

        key = source.resolve()
        if key not in mappings or sim > mappings[key][1]:
            mappings[key] = (target, sim)

    if not mappings:
        print("没有可自动处理的映射。")
        return

    print(f"将处理 {len(mappings)} 个文件:\n")
    for source, (target, sim) in sorted(mappings.items(), key=lambda x: -x[1][1]):
        print(f"  [{sim:.2f}] {source.relative_to(PROJECT_ROOT)}")
        print(f"        -> {target.relative_to(PROJECT_ROOT)}")

    if args.dry_run:
        print("\n--dry-run：未写入任何文件。")
        return

    print("\n开始写入重定向...\n")
    for source, (target, sim) in mappings.items():
        title = extract_title(source)
        content = redirect_content(source, target, title)
        source.write_text(content, encoding="utf-8")
        print(f"已重写: {source.relative_to(PROJECT_ROOT)}")

    print(f"\n完成，共重写 {len(mappings)} 个文件。")


if __name__ == "__main__":
    main()
