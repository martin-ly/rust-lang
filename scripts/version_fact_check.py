#!/usr/bin/env python3
"""
version_fact_check.py — Rust 版本声明事实核查工具

扫描项目中的版本声明，与权威来源交叉验证，输出可疑声明。

用法:
    python scripts/version_fact_check.py
    python scripts/version_fact_check.py --path concept/02_intermediate/
    python scripts/version_fact_check.py --json
    python scripts/version_fact_check.py --fix-suggestions
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path
from typing import Dict, List, Tuple

# ============================================================================
# 权威版本映射表 —— 关键 API/特性 → 实际稳定版本
# ============================================================================

AUTHORITATIVE_VERSIONS: Dict[str, Tuple[str, str]] = {
    # API/特性名称: (实际稳定版本, 说明)
    "assert_matches": ("1.96.0", "标准库宏，此前长期 unstable"),
    "debug_assert_matches": ("1.96.0", "assert_matches 的 debug 变体"),
    "core::range::Range": ("1.96.0", "Copy 范围类型"),
    "core::range::RangeFrom": ("1.96.0", "Copy 范围起始类型"),
    "core::range::RangeToInclusive": ("1.96.0", "Copy 范围闭合终点类型"),
    "core::range::RangeInclusive": ("1.95.0", "此前已稳定"),
    "NonZero range iteration": ("1.96.0", "NonZero 整数范围迭代"),
    "From<T> for LazyLock": ("1.96.0", "LazyLock 直接构造"),
    "From<T> for LazyCell": ("1.96.0", "LazyCell 直接构造"),
    "From<T> for AssertUnwindSafe": ("1.96.0", "AssertUnwindSafe 直接构造"),
    "ManuallyDrop pattern": ("1.96.0", "ManuallyDrop 常量模式匹配"),
    "expr metavariable to cfg": ("1.96.0", "宏 expr 片段传递给 cfg"),
    "never type tuple coercion": ("1.96.0", "Never 类型在 tuple 中的强制转换"),
    "if let guards": ("1.95.0", "match 守卫中的 if let"),
    "VecDeque::truncate_front": ("TBD", "VecDeque 前端截断；PR #151973 FCP finished，预计 1.98+"),
    "RefCell::try_map": ("TBD", "RefCell 条件映射；PR #152122 等待作者"),
    "int_format_into": ("TBD", "整数格式化到缓冲区；PR #152544 已合并至 master，将进入 1.98"),
    "cfg_select": ("1.95.0", "条件编译选择宏"),
    "From<bool> for f32": ("1.68.0", "布尔到浮点转换"),
    "From<bool> for f64": ("1.68.0", "布尔到浮点转换"),
    "VecDeque::new const": ("1.68.0", "VecDeque 常量构造"),
    "async fn in trait": ("1.75.0", "trait 中 async fn"),
    "impl trait in assoc fn": ("1.75.0", "关联函数返回位置 impl trait"),
    "let else": ("1.65.0", "let-else 绑定"),
    "generic associated types": ("1.65.0", "GAT"),
    "const generics": ("1.51.0", "常量泛型"),
}

# ============================================================================
# 扫描模式 —— 用于匹配文档中的版本声明
# ============================================================================

# (模式名称, 正则表达式, 提取组索引, 预期版本)
SCAN_PATTERNS: List[Tuple[str, str, int, str]] = [
    # assert_matches
    ("assert_matches", r"assert_matches!.*?([Rr]ust\s+)?1\.(\d{2})(?!\.0)\b", 2, "1.96.0"),
    ("assert_matches", r"assert_matches.*?稳定.*?1\.(\d{2})(?!\.0)", 1, "1.96.0"),
    ("assert_matches", r"assert_matches.*?([Rr]ust\s+)?1\.(\d{2})(?!\.0)\s+stable", 2, "1.96.0"),

    # From<bool>
    ("From<bool>", r"From<bool>.*?1\.(\d{2})(?!\.0)\b", 1, "1.68.0"),
    ("From<bool>", r"布尔到浮点.*?1\.(\d{2})(?!\.0)\b", 1, "1.68.0"),

    # VecDeque::new const
    ("VecDeque::new const", r"VecDeque::new.*?const.*?1\.(\d{2})(?!\.0)\b", 1, "1.68.0"),
    ("VecDeque::new const", r"VecDeque.*?const.*?1\.(\d{2})(?!\.0)\b", 1, "1.68.0"),

    # core::range: 仅匹配核心类型迁移（Range/RangeFrom/RangeToInclusive/RangeInclusive），
    # 排除 1.98 才迁移的 RangeFull/RangeTo/legacy 等子特性，避免误报。
    ("core::range", r"core::range(?:(?!RangeFull|RangeTo\b|legacy).)*?1\.(\d{2})(?!\.0)\b", 1, "1.96.0"),
    ("core::range", r"RangeIter.*?1\.(\d{2})(?!\.0)\b", 1, "1.96.0"),

    # async fn in trait
    ("async fn in trait", r"async fn in trait.*?1\.(\d{2})(?!\.0)\b", 1, "1.75.0"),

    # if let guards
    ("if let guards", r"if let guard.*?1\.(\d{2})(?!\.0)\b", 1, "1.95.0"),

    # Never type tuple coercion
    ("never type tuple coercion", r"never type.*?tuple.*?1\.(\d{2})(?!\.0)\b", 1, "1.96.0"),
    ("never type tuple coercion", r"tuple coercion.*?1\.(\d{2})(?!\.0)\b", 1, "1.96.0"),
]

# 高置信度错误模式 —— 一旦发现直接报错误
HIGH_CONFIDENCE_ERRORS: List[Tuple[str, str, str]] = [
    # (模式, 替代文本, 错误说明)
    (r"assert_matches!.*?1\.77", "1.96", "assert_matches! 于 1.96.0 稳定，非 1.77"),
    (r"assert_matches.*?1\.77", "1.96", "assert_matches! 于 1.96.0 稳定，非 1.77"),
    (r"From<bool>.*?1\.96", "1.68", "From<bool> for f32/f64 于 1.68.0 稳定，非 1.96"),
    (r"VecDeque::new.*?const.*?1\.96", "1.68", "VecDeque::new const 于 1.68.0 稳定，非 1.96"),
]


# ============================================================================
# 数据类
# ============================================================================

@dataclass
class Finding:
    file: str
    line: int
    context: str
    feature: str
    claimed_version: str
    actual_version: str
    severity: str  # "error" | "warning"
    message: str
    suggestion: str = ""


@dataclass
class Report:
    scanned_files: int = 0
    findings: List[Finding] = field(default_factory=list)

    def add(self, finding: Finding) -> None:
        self.findings.append(finding)

    def errors(self) -> List[Finding]:
        return [f for f in self.findings if f.severity == "error"]

    def warnings(self) -> List[Finding]:
        return [f for f in self.findings if f.severity == "warning"]


# ============================================================================
# 扫描逻辑
# ============================================================================

def normalize_version(version: str) -> str:
    """将版本号标准化为 `major.minor` 形式，忽略补丁版本。

    例如 `1.96.0` → `1.96`，`1.96` → `1.96`。
    """
    parts = version.split(".")
    return ".".join(parts[:2])


def scan_file(path: Path, report: Report, fix_suggestions: bool = False) -> None:
    """扫描单个文件中的版本声明。"""
    try:
        content = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return

    lines = content.splitlines()
    rel_path = str(path).replace(os.sep, "/")

    for line_idx, line in enumerate(lines, start=1):
        # 高置信度错误检测
        for pattern, replacement, msg in HIGH_CONFIDENCE_ERRORS:
            if re.search(pattern, line, re.IGNORECASE):
                suggestion = f"将版本号改为 {replacement}" if fix_suggestions else ""
                report.add(Finding(
                    file=rel_path,
                    line=line_idx,
                    context=line.strip(),
                    feature=pattern.split("!")[0] if "!" in pattern else pattern.split(".*?")[0],
                    claimed_version=re.search(r"1\.\d{2}", line).group(0) if re.search(r"1\.\d{2}", line) else "?",
                    actual_version=replacement,
                    severity="error",
                    message=msg,
                    suggestion=suggestion,
                ))

        # 通用模式扫描
        for feature_name, pattern, group_idx, expected_version in SCAN_PATTERNS:
            for match in re.finditer(pattern, line, re.IGNORECASE):
                groups = match.groups()
                if len(groups) >= group_idx:
                    claimed = f"1.{groups[group_idx - 1]}"
                    # 如果当前行已显式包含实际稳定版本号，视为免责声明/上下文说明，跳过误报
                    if expected_version in line:
                        continue
                    if normalize_version(claimed) != normalize_version(expected_version):
                        # 判断严重程度：相差越大越严重
                        claimed_minor = int(groups[group_idx - 1])
                        expected_minor = int(expected_version.split(".")[1])
                        if abs(claimed_minor - expected_minor) >= 10:
                            severity = "error"
                        else:
                            severity = "warning"

                        suggestion = (
                            f"将 {claimed} 改为 {expected_version}"
                            if fix_suggestions else ""
                        )
                        report.add(Finding(
                            file=rel_path,
                            line=line_idx,
                            context=line.strip(),
                            feature=feature_name,
                            claimed_version=claimed,
                            actual_version=expected_version,
                            severity=severity,
                            message=f"{feature_name} 实际于 {expected_version} 稳定，文档声明为 {claimed}",
                            suggestion=suggestion,
                        ))


def scan_directory(root: Path, report: Report, fix_suggestions: bool = False) -> None:
    """递归扫描目录。"""
    # 排除分析/库存文件（记录历史错误，不应被扫描）
    EXCLUDED_PATHS = {
        "analysis",
        "00_rust_global_alignment_symmetric_difference_analysis",
        "04_rust_language_feature_comprehensive_inventory",
    }
    for path in root.rglob("*"):
        if path.is_file() and path.suffix in (".md", ".rs"):
            # 跳过 .git 和 target
            if ".git" in str(path) or "target" in str(path).split(os.sep):
                continue
            # 跳过分析/库存文件
            path_str = str(path).replace("\\", "/")
            if any(ex in path_str for ex in EXCLUDED_PATHS):
                continue
            report.scanned_files += 1
            scan_file(path, report, fix_suggestions)


# ============================================================================
# 输出格式
# ============================================================================

def print_text_report(report: Report) -> None:
    print("=" * 70)
    print(f"Rust 版本声明事实核查报告")
    print("=" * 70)
    print(f"扫描文件数: {report.scanned_files}")
    print(f"发现问题: {len(report.findings)} 处")
    print(f"  - 错误: {len(report.errors())} 处")
    print(f"  - 警告: {len(report.warnings())} 处")
    print()

    if not report.findings:
        print("✅ 未发现版本声明错误。")
        return

    # 按严重程度和文件分组
    current_file = ""
    for finding in sorted(report.findings, key=lambda f: (f.file, f.line)):
        if finding.file != current_file:
            current_file = finding.file
            print(f"\n📄 {current_file}")
            print("-" * 60)

        icon = "🔴" if finding.severity == "error" else "🟡"
        print(f"  {icon} 第 {finding.line} 行 [{finding.feature}]")
        print(f"     声明: {finding.claimed_version} | 实际: {finding.actual_version}")
        print(f"     上下文: {finding.context[:80]}")
        print(f"     说明: {finding.message}")
        if finding.suggestion:
            print(f"     建议: {finding.suggestion}")


def print_json_report(report: Report) -> None:
    output = {
        "scanned_files": report.scanned_files,
        "total_findings": len(report.findings),
        "errors": len(report.errors()),
        "warnings": len(report.warnings()),
        "findings": [asdict(f) for f in report.findings],
    }
    print(json.dumps(output, indent=2, ensure_ascii=False))


# ============================================================================
# 主入口
# ============================================================================

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Rust 版本声明事实核查工具",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  %(prog)s                          # 扫描默认目录
  %(prog)s --path concept/          # 扫描指定路径
  %(prog)s --json                   # JSON 输出
  %(prog)s --fix-suggestions        # 输出修正建议
""",
    )
    parser.add_argument(
        "--path",
        type=str,
        default=None,
        help="要扫描的目录或文件（默认: concept/ knowledge/ crates/ docs/）",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="以 JSON 格式输出",
    )
    parser.add_argument(
        "--fix-suggestions",
        action="store_true",
        help="输出修正建议",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="将 warning 也视为失败（退出码非 0）",
    )
    args = parser.parse_args()

    report = Report()

    if args.path:
        target = Path(args.path)
        if target.is_file():
            report.scanned_files = 1
            scan_file(target, report, args.fix_suggestions)
        else:
            scan_directory(target, report, args.fix_suggestions)
    else:
        # 默认扫描核心目录
        project_root = Path(__file__).parent.parent
        for subdir in ("concept", "knowledge", "crates", "docs"):
            d = project_root / subdir
            if d.exists():
                scan_directory(d, report, args.fix_suggestions)

    if args.json:
        print_json_report(report)
    else:
        print_text_report(report)

    if args.strict and report.findings:
        return 1
    return 1 if report.errors() else 0


if __name__ == "__main__":
    sys.exit(main())
