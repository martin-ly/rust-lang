#!/usr/bin/env python3
"""
清理 concept/ 目录下的机械重复引用块。

三级清理策略：
  Level 1: 目录块内的引用（100%安全）
  Level 2: 连续重复的引用组（100%安全）
  Level 3: 章节标题后/孤立的纯引用（需人工复核）

保留规则：
  - 含实质解释内容的混合引用（如 > **修正**: ... [来源: ...]）
  - 文件头部的 > **来源**: ... 总述块
  - 正文段落末尾的溯源标注
"""

import os
import re
import sys
import json
import argparse
from pathlib import Path

RE_HEADING = re.compile(r"^#{1,6} ")
RE_TOC_START = re.compile(r"^## 📑 目录")
RE_TOC_ITEM = re.compile(r"^\s*- \[")
RE_TABLE_START = re.compile(r"^\|")
RE_CODE_FENCE = re.compile(r"^```")
RE_HORIZONTAL_RULE = re.compile(r"^---\s*$")
RE_EMPTY_BLOCKQUOTE = re.compile(r"^>\s*$")

# 混合引用中的解释关键词——含有这些词的行不应被删除
MIXED_CITATION_KEYWORDS = [
    "**修正**", "**认知**", "**关键洞察**", "**定理**", "**推论**",
    "**定义**", "**说明**", "**注意**", "**警告**", "**提示**",
    "**直觉**", "**形式化**", "**对比**", "**实践**",
]


def is_standalone_citation(line):
    """判断是否为独立的纯引用行（不含后续解释文字）
    
    匹配模式：
      > [来源: ...]
      > **[来源: ...]**
      > [来源: ...] · [来源: ...]
    
    不匹配（混合引用）：
      > **修正**: ... [来源: ...]
      > **[来源: ...]** 这是解释文字...
    """
    stripped = line.strip()
    if not stripped.startswith("> "):
        return False
    content = stripped[2:].strip()
    
    # 必须以 [来源: 或 **[来源: 开头
    if not (content.startswith("[来源:") or content.startswith("**[来源:")):
        return False
    
    # 排除含解释关键词的混合引用
    for kw in MIXED_CITATION_KEYWORDS:
        if kw in content:
            return False
    
    # 检查 ] 或 ]** 后面是否还有实质解释文字
    # 找到最后一个 ] 的位置
    last_bracket = content.rfind("]")
    if last_bracket == -1:
        return True  # 没有 ]，格式异常，但仍视为纯引用处理
    
    after = content[last_bracket + 1:].strip()
    # 去除常见分隔符后检查剩余内容
    after_clean = after.lstrip("·").strip()
    if len(after_clean) > 5:
        # ] 后面有实质文字（非来源列表），视为混合引用
        return False
    
    return True


def is_empty_blockquote(line):
    """判断是否为空的引用行 (> 后面只有空白)"""
    return bool(RE_EMPTY_BLOCKQUOTE.match(line))


def is_heading(line):
    return bool(RE_HEADING.match(line))


def is_toc_start(line):
    return bool(RE_TOC_START.match(line))


def is_toc_item(line):
    return bool(RE_TOC_ITEM.match(line))


def is_empty(line):
    return not line.strip()


def find_toc_regions(lines):
    """返回目录块的起止索引列表 [(start, end), ...]"""
    regions = []
    i = 0
    n = len(lines)
    while i < n:
        if is_toc_start(lines[i]):
            start = i
            i += 1
            while i < n:
                line = lines[i]
                if is_heading(line) and not is_toc_start(line):
                    break
                if (
                    not is_empty(line)
                    and not is_standalone_citation(line)
                    and not is_toc_item(line)
                    and not line.strip().startswith(">")
                ):
                    break
                i += 1
            regions.append((start, i))
        else:
            i += 1
    return regions


def find_consecutive_citation_groups(lines):
    """返回连续引用组的起止索引列表 [(start, end), ...]"""
    groups = []
    i = 0
    n = len(lines)
    while i < n:
        if is_standalone_citation(lines[i]) or is_empty_blockquote(lines[i]):
            start = i
            while i < n and (is_standalone_citation(lines[i]) or is_empty_blockquote(lines[i]) or is_empty(lines[i])):
                i += 1
            groups.append((start, i))
        else:
            i += 1
    return groups


def find_duplicate_groups(groups, lines):
    """在连续引用组中找出重复序列。"""
    if len(groups) < 2:
        return None, []

    signatures = []
    for start, end in groups:
        sig = tuple(
            lines[j].strip() for j in range(start, end) if not is_empty(lines[j])
        )
        signatures.append(sig)

    to_delete = []
    seen = {}
    for idx, sig in enumerate(signatures):
        if sig in seen:
            to_delete.append(idx)
        else:
            seen[sig] = idx

    return seen, to_delete


def analyze_file(filepath):
    with open(filepath, "r", encoding="utf-8") as f:
        lines = f.readlines()

    lines = [line.rstrip("\n").rstrip("\r") for line in lines]
    n = len(lines)
    deletions = set()
    reasons = {}

    # ===== Level 1: 目录块内的引用 =====
    toc_regions = find_toc_regions(lines)
    for start, end in toc_regions:
        for i in range(start, end):
            if is_standalone_citation(lines[i]):
                deletions.add(i)
                reasons[i] = "L1_toc_block"

    # ===== Level 2: 连续重复的引用组 =====
    groups = find_consecutive_citation_groups(lines)
    seen, dup_indices = find_duplicate_groups(groups, lines)
    for idx in dup_indices:
        start, end = groups[idx]
        for i in range(start, end):
            if is_standalone_citation(lines[i]) or is_empty_blockquote(lines[i]):
                deletions.add(i)
                reasons[i] = "L2_duplicate_group"

    # ===== Level 3: 章节标题后孤立引用 / 完全孤立引用 =====
    for i in range(n):
        if i in deletions:
            continue
        if not is_standalone_citation(lines[i]):
            continue

        prev_line = lines[i - 1] if i > 0 else ""
        next_line = lines[i + 1] if i < n - 1 else ""

        prev_is_heading = is_heading(prev_line)
        prev_is_empty = is_empty(prev_line)
        prev_is_citation = is_standalone_citation(prev_line) or is_empty_blockquote(prev_line)
        prev_is_hr = bool(RE_HORIZONTAL_RULE.match(prev_line)) if prev_line else False

        next_is_empty = is_empty(next_line)
        next_is_heading = is_heading(next_line)
        next_is_table = bool(RE_TABLE_START.match(next_line)) if next_line else False
        next_is_code = bool(RE_CODE_FENCE.match(next_line)) if next_line else False
        next_is_citation = is_standalone_citation(next_line) or is_empty_blockquote(next_line)
        next_is_hr = bool(RE_HORIZONTAL_RULE.match(next_line)) if next_line else False

        # 情况A: 章节标题后紧跟引用，再后面是空行/表格/代码块/标题/HR
        if prev_is_heading and (
            next_is_empty
            or next_is_table
            or next_is_code
            or next_is_heading
            or next_is_hr
        ):
            deletions.add(i)
            reasons[i] = "L3_after_heading"
            continue

        # 情况B: 前后都是空行或空引用行（完全孤立）
        prev_is_isolator = prev_is_empty or prev_is_citation or prev_is_hr
        next_is_isolator = next_is_empty or next_is_citation or next_is_hr
        if prev_is_isolator and next_is_isolator:
            deletions.add(i)
            reasons[i] = "L3_isolated"
            continue

    report = {
        "filepath": str(filepath),
        "total_lines": n,
        "deletions": sorted(deletions),
        "reasons": {str(k): reasons[k] for k in sorted(reasons.keys())},
        "level_counts": {
            "L1": sum(1 for r in reasons.values() if r.startswith("L1")),
            "L2": sum(1 for r in reasons.values() if r.startswith("L2")),
            "L3": sum(1 for r in reasons.values() if r.startswith("L3")),
        },
    }
    return report


def apply_deletions(filepath, report):
    with open(filepath, "r", encoding="utf-8") as f:
        lines = f.readlines()

    deletions = set(report["deletions"])
    new_lines = [line for i, line in enumerate(lines) if i not in deletions]

    with open(filepath, "w", encoding="utf-8") as f:
        f.writelines(new_lines)

    return len(deletions)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--dir", default="concept", help="目标目录")
    parser.add_argument("--apply", action="store_true", help="实际应用删除（默认仅报告）")
    parser.add_argument("--file", default=None, help="仅处理单个文件")
    args = parser.parse_args()

    target_dir = Path(args.dir)
    if args.file:
        files = [Path(args.file)]
    else:
        files = sorted(target_dir.rglob("*.md"))

    total_deletions = 0
    file_reports = []

    for filepath in files:
        rel = str(filepath.relative_to(target_dir))
        parts = rel.replace("\\", "/").split("/")
        if "archive" in [p.lower() for p in parts]:
            continue

        report = analyze_file(filepath)
        if report["deletions"]:
            file_reports.append(report)
            total_deletions += len(report["deletions"])

    print(f"{'='*60}")
    print(f"分析目录: {target_dir}")
    print(f"处理文件数: {len(file_reports)} / {len(files)}")
    print(f"建议删除总行数: {total_deletions}")
    print(
        f"  Level 1 (目录块内): {sum(r['level_counts']['L1'] for r in file_reports)}"
    )
    print(
        f"  Level 2 (重复组):   {sum(r['level_counts']['L2'] for r in file_reports)}"
    )
    print(
        f"  Level 3 (孤立引用): {sum(r['level_counts']['L3'] for r in file_reports)}"
    )
    print(f"{'='*60}")

    file_reports.sort(key=lambda r: len(r["deletions"]), reverse=True)
    print("\n受影响最严重的 20 个文件:")
    for r in file_reports[:20]:
        print(
            f"  {r['filepath']}: {len(r['deletions'])} 行 (L1={r['level_counts']['L1']}, L2={r['level_counts']['L2']}, L3={r['level_counts']['L3']})"
        )

    print("\n--- 样本详情（前 3 个文件） ---")
    for r in file_reports[:3]:
        print(f"\n文件: {r['filepath']} ({len(r['deletions'])} 行将被删除)")
        with open(r["filepath"], "r", encoding="utf-8") as f:
            lines = f.readlines()
        for idx in r["deletions"][:5]:
            reason = r["reasons"][str(idx)]
            line_text = lines[idx].rstrip("\n")
            print(f"  行{idx+1:4d} [{reason}]: {line_text[:80]}")
        if len(r["deletions"]) > 5:
            print(f"  ... 还有 {len(r['deletions']) - 5} 行")

    if args.apply:
        applied_count = 0
        for report in file_reports:
            applied_count += apply_deletions(Path(report["filepath"]), report)
        print(f"\n{'='*60}")
        print(f"已应用删除！共清理 {applied_count} 行")
        print(f"{'='*60}")
        report_path = target_dir / ".cleanup_report.json"
        with open(report_path, "w", encoding="utf-8") as f:
            json.dump(file_reports, f, ensure_ascii=False, indent=2)
        print(f"详细报告已保存: {report_path}")
    else:
        print(f"\n{'='*60}")
        print("干运行模式完成。使用 --apply 实际应用删除。")
        print(f"{'='*60}")


if __name__ == "__main__":
    main()
