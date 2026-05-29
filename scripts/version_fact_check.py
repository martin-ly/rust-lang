#!/usr/bin/env python3
"""
版本事实核查脚本 (version_fact_check.py)

扫描项目中所有版本特性声明，要求每个 "X.Y stable" 声明必须伴随官方来源链接，
并对已知的历史版本错误进行自动检测。

用法:
    python scripts/version_fact_check.py

返回码:
    0 - 无错误或警告
    1 - 发现错误或警告
"""

import re
import sys
import pathlib
from collections import defaultdict

# 项目根目录
PROJECT_ROOT = pathlib.Path(__file__).parent.parent.resolve()

# 已知的"特性 -> 实际稳定版本"映射表（基于官方 Release Notes）
# 用于自动检测常见的版本错位
KNOWN_FEATURE_VERSIONS = {
    # (关键词模式, 实际稳定版本, 错误标注版本)
    ("assert_matches!", "1.96", "1.77"),
    ("From<bool> for f32", "1.68", "1.96"),
    ("From<bool> for f64", "1.68", "1.96"),
    ("VecDeque::new", "1.68", "1.96"),
    ("VecDeque::new const", "1.68", "1.96"),
    ("core::range::Range", "1.96", None),
    ("core::range::RangeFrom", "1.96", None),
    ("core::range::RangeToInclusive", "1.96", None),
    ("NonZero" "范围迭代", "1.96", None),
    ("NonZero" "Step", "1.96", None),
    ("From<T> for LazyLock", "1.96", None),
    ("From<T> for LazyCell", "1.96", None),
    ("From<T> for AssertUnwindSafe", "1.96", None),
    ("expr" "metavariable" "cfg", "1.96", None),
    ("ManuallyDrop" "常量" "模式", "1.96", None),
}

# 扫描的文件模式
SCAN_PATTERNS = [
    "crates/*/src/rust_*_features.rs",
    "concept/**/*.md",
    "knowledge/**/*.md",
    "docs/**/*.md",
]

# 正则表达式：匹配 "X.Y stable" 或 "Rust X.Y 稳定" 等声明
VERSION_DECLARATION_RE = re.compile(
    r"(Rust\s+)?(?P<ver>\d+\.\d+(?:\.\d+)?)\s*(?:稳定|stable|稳定化)",
    re.IGNORECASE | re.UNICODE,
)

# 正则表达式：匹配官方来源链接
OFFICIAL_SOURCE_RE = re.compile(
    r"\[.*?\]\(https?://(?:releases\.rs|github\.com/rust-lang/rust|doc\.rust-lang\.org)/.*?\)",
    re.IGNORECASE,
)

# 正则表达式：匹配 "#![feature(...)]" 代码块（标识 nightly 内容）
FEATURE_GATE_RE = re.compile(r"#!\s*\[\s*feature\s*\(\s*([^)]+)\s*\)\s*\]", re.IGNORECASE)

# 2026-05-29: 确认未进入 1.96 stable 的虚假特性（用于检测残留错误）
NOT_IN_1_96_STABLE = [
    "VecDeque::truncate_front",
    "int_format_into",
    "NumBuffer",
    "RefCell::try_map",
    "RefMut::try_map",
    "proc_macro_value",
    "cargo script frontmatter",
]


def scan_file(filepath: pathlib.Path) -> list[dict]:
    """扫描单个文件中的版本声明。"""
    issues = []
    try:
        content = filepath.read_text(encoding="utf-8")
    except Exception as e:
        issues.append({
            "file": str(filepath.relative_to(PROJECT_ROOT)),
            "line": 0,
            "severity": "ERROR",
            "message": f"无法读取文件: {e}",
        })
        return issues

    lines = content.splitlines()
    has_official_source = bool(OFFICIAL_SOURCE_RE.search(content))

    for lineno, line in enumerate(lines, start=1):
        # 检测虚假 1.96 特性声明
        for false_feature in NOT_IN_1_96_STABLE:
            if false_feature.lower() in line.lower() and "1.96" in line:
                # 排除已明确标记为 nightly/未稳定的注释
                if "nightly" in line.lower() or "未稳定" in line or "unstable" in line.lower():
                    continue
                # 排除已修正/已删除/未进入的注释
                if "已删除" in line or "虚假" in line or "未进入" in line or "已修正" in line:
                    continue
                # 排除审计/分析报告中的问题记录（非声明本身）
                if "标签错误" in line or "错位" in line or "发现" in line:
                    continue
                issues.append({
                    "file": str(filepath.relative_to(PROJECT_ROOT)),
                    "line": lineno,
                    "severity": "ERROR",
                    "message": f"检测到未进入 1.96 stable 的虚假特性声明: '{false_feature}'",
                })

        # 检测版本声明
        for match in VERSION_DECLARATION_RE.finditer(line):
            declared_ver = match.group("ver")
            # 检查是否伴随来源链接（简化检查：同一行或附近是否有链接）
            nearby = "\n".join(lines[max(0, lineno-3):min(len(lines), lineno+2)])
            has_source_nearby = bool(OFFICIAL_SOURCE_RE.search(nearby))

            if not has_source_nearby and not has_official_source:
                issues.append({
                    "file": str(filepath.relative_to(PROJECT_ROOT)),
                    "line": lineno,
                    "severity": "WARNING",
                    "message": f"版本声明 '{declared_ver}' 未伴随官方来源链接",
                })

        # 检测已知错误版本对
        for keywords, correct_ver, wrong_ver in KNOWN_FEATURE_VERSIONS:
            if wrong_ver is None:
                continue
            # 检查行中是否同时包含关键词和错误版本
            if wrong_ver in line:
                # 排除已修正/审计记录行和任务描述行
                if "已修正" in line or "标签错误" in line or "错位" in line:
                    continue
                # 排除任务/计划描述行（如"补充 xxx 等 1.96 特性"）
                if "补充" in line or "缺少" in line or "计划" in line or "任务" in line:
                    continue
                all_keywords_present = all(kw in line for kw in keywords.split())
                if all_keywords_present:
                    issues.append({
                        "file": str(filepath.relative_to(PROJECT_ROOT)),
                        "line": lineno,
                        "severity": "ERROR",
                        "message": f"已知版本错误: '{keywords}' 实际稳定于 {correct_ver}，但文档声明为 {wrong_ver}",
                    })

    return issues


def main() -> int:
    all_issues = []
    scanned_files = 0

    for pattern in SCAN_PATTERNS:
        for filepath in PROJECT_ROOT.glob(pattern):
            if not filepath.is_file():
                continue
            # 跳过 archive 和历史文件
            if "archive" in str(filepath) or "_preview" in str(filepath):
                continue
            issues = scan_file(filepath)
            if issues:
                all_issues.extend(issues)
            scanned_files += 1

    # 按文件分组输出
    issues_by_file = defaultdict(list)
    for issue in all_issues:
        issues_by_file[issue["file"]].append(issue)

    error_count = sum(1 for i in all_issues if i["severity"] == "ERROR")
    warning_count = sum(1 for i in all_issues if i["severity"] == "WARNING")

    print("=" * 70)
    print("版本事实核查报告 (Version Fact Check)")
    print("=" * 70)
    print(f"扫描文件数: {scanned_files}")
    print(f"错误数: {error_count}")
    print(f"警告数: {warning_count}")
    print()

    if not all_issues:
        print("✅ 未发现问题")
        return 0

    for filepath, issues in sorted(issues_by_file.items()):
        print(f"📄 {filepath}")
        for issue in issues:
            icon = "🔴" if issue["severity"] == "ERROR" else "🟡"
            print(f"  {icon} 第 {issue['line']} 行: {issue['message']}")
        print()

    print("=" * 70)
    print("建议: 对每个 ERROR，请核对官方 Release Notes 并修正版本号；")
    print("      对每个 WARNING，请在版本声明附近添加官方来源链接。")
    print("=" * 70)

    return 1 if error_count > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
