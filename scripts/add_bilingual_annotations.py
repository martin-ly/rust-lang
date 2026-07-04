#!/usr/bin/env python3
"""为 concept/ 中的 Markdown 文件添加关键术语中英双语标注，并支持国际化元数据检查。

模式:
- 默认模式: 扫描并自动标注 01_foundation / 02_intermediate / 03_advanced。
- enforce 模式: 覆盖全部 concept/ 目录，对缺失 EN/Summary 或未标注术语报错，不修改文件。
- check-only 模式: 只检查不修改，输出未覆盖术语清单。

用法:
    python scripts/add_bilingual_annotations.py
    python scripts/add_bilingual_annotations.py --mode enforce
    python scripts/add_bilingual_annotations.py --mode check-only --dir concept/06_ecosystem
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import datetime, timezone
from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable

TERMS = [
    ("所有权", "Ownership"),
    ("可变借用", "Mutable Borrow"),
    ("不可变借用", "Immutable Borrow"),
    ("借用", "Borrowing"),
    ("生命周期", "Lifetimes"),
    ("可变引用", "Mutable Reference"),
    ("不可变引用", "Immutable Reference"),
    ("引用", "Reference"),
    ("字符串切片", "String Slice"),
    ("切片", "Slice"),
    ("结构体", "Struct"),
    ("枚举", "Enum"),
    ("模式匹配", "Pattern Matching"),
    ("闭包", "Closures"),
    ("迭代器", "Iterator"),
    ("泛型", "Generics"),
    ("trait对象", "Trait Object"),
    ("trait", "Trait"),
    ("Box", "Box"),
    ("Vec", "Vec"),
    ("HashMap", "HashMap"),
    ("Result", "Result"),
    ("Option", "Option"),
    ("panic", "Panic"),
    ("错误处理", "Error Handling"),
    ("智能指针", "Smart Pointer"),
    ("原子操作", "Atomic Operations"),
    ("异步", "Async"),
    ("Future", "Future"),
    ("运行时", "Runtime"),
    ("原始指针", "Raw Pointer"),
    ("内联汇编", "Inline Assembly"),
    ("FFI", "FFI"),
    ("声明宏", "Declarative Macro"),
    ("过程宏", "Procedural Macro"),
    ("宏", "Macro"),
    ("模块", "Module"),
    ("crate", "Crate"),
    ("Cargo", "Cargo"),
    ("零成本抽象", "Zero-Cost Abstraction"),
    ("RAII", "RAII"),
    ("类型系统", "Type System"),
    ("类型推断", "Type Inference"),
    ("内存安全", "Memory Safety"),
    ("并发安全", "Concurrency Safety"),
    ("Send", "Send"),
    ("Sync", "Sync"),
    ("unsafe", "Unsafe"),
    ("Pin", "Pin"),
    ("生命周期省略", "Lifetime Elision"),
    ("孤儿规则", "Orphan Rule"),
    ("一致性", "Coherence"),
    ("单态化", "Monomorphization"),
]

DEFAULT_DIRS = [
    Path("concept/01_foundation"),
    Path("concept/02_intermediate"),
    Path("concept/03_advanced"),
]

ALL_CONCEPT_DIRS = [Path("concept")]

LINK_PLACEHOLDER = "\x00LINK\x00"
CODE_PLACEHOLDER = "\x00CODE\x00"


@dataclass
class FileReport:
    path: Path
    missing_en: bool = False
    missing_summary: bool = False
    uncovered_terms: list[str] = field(default_factory=list)
    annotated_terms: list[str] = field(default_factory=list)


def mask_links_and_code(line: str) -> tuple[str, list[str], list[str]]:
    links: list[str] = []
    codes: list[str] = []

    def link_repl(m: re.Match) -> str:
        links.append(m.group(0))
        return LINK_PLACEHOLDER

    def code_repl(m: re.Match) -> str:
        codes.append(m.group(0))
        return CODE_PLACEHOLDER

    line = re.sub(r"`[^`]+`", code_repl, line)
    # 只遮蔽链接的 URL 部分，保留链接文本以便标注
    line = re.sub(r"\]\([^)]+\)", link_repl, line)
    return line, links, codes


def unmask(line: str, links: list[str], codes: list[str]) -> str:
    parts = line.split(LINK_PLACEHOLDER)
    out = ""
    link_idx = 0
    for i, part in enumerate(parts):
        out += part
        if i < len(parts) - 1:
            out += links[link_idx]
            link_idx += 1

    parts = out.split(CODE_PLACEHOLDER)
    out = ""
    code_idx = 0
    for i, part in enumerate(parts):
        out += part
        if i < len(parts) - 1:
            out += codes[code_idx]
            code_idx += 1
    return out


def has_bilingual_annotation(text: str, cn: str, en: str) -> bool:
    """检查文本中该术语是否已有双语标注。"""
    # 1. 中文后紧跟英文括号
    if re.search(rf"{re.escape(cn)}\s*[（(]{re.escape(en)}[）)]", text):
        return True
    # 2. 同一行已包含英文术语（简化判断）
    if re.search(rf"\b{re.escape(en)}\b", text, re.IGNORECASE):
        return True
    return False


def annotate_line(line: str, seen_terms: set[str]) -> tuple[str, bool]:
    masked, links, codes = mask_links_and_code(line)
    original_masked = masked

    for cn, en in TERMS:
        if cn in seen_terms:
            continue
        if masked.lstrip().startswith("#"):
            continue
        if re.search(rf"\b{re.escape(en)}\b", masked, re.IGNORECASE):
            continue
        if re.search(rf"{re.escape(cn)}\s*[\(（][A-Za-z]", masked):
            continue

        pattern = re.compile(
            rf"(?<![A-Za-z0-9_])({re.escape(cn)})(?![A-Za-z0-9_])"
        )

        def repl(m: re.Match) -> str:
            tail = masked[m.end() : m.end() + 30]
            if re.match(r"[\(（][A-Za-z]", tail):
                return m.group(1)
            before = masked[m.start() - 1] if m.start() > 0 else ""
            after = masked[m.end()] if m.end() < len(masked) else ""
            if before in "（(" and after in "）)":
                return m.group(1)
            return f"{m.group(1)}（{en}）"

        new_masked, count = pattern.subn(repl, masked, count=1)
        if count > 0:
            masked = new_masked
            seen_terms.add(cn)

    if masked == original_masked:
        return line, False
    return unmask(masked, links, codes), True


def collect_text_blocks(content: str) -> str:
    """收集 Markdown 中所有非代码块、非标题文本（用于检查术语覆盖）。"""
    blocks = []
    in_code = False
    for line in content.splitlines():
        if line.lstrip().startswith("```"):
            in_code = not in_code
            continue
        if in_code:
            continue
        if line.lstrip().startswith("#"):
            continue
        blocks.append(line)
    return "\n".join(blocks)


def check_metadata(content: str, path: Path) -> FileReport:
    """检查文件头元数据。"""
    report = FileReport(path=path)
    if "**EN**" not in content:
        report.missing_en = True
    if "**Summary**" not in content:
        report.missing_summary = True
    return report


def check_term_coverage(content: str, path: Path) -> FileReport:
    """检查术语覆盖情况（不修改文件）。"""
    report = FileReport(path=path)
    text = collect_text_blocks(content)

    for cn, en in TERMS:
        # 仅对作为独立词/词组出现的术语检查是否已标注（前后不能是其他中文字符或单词字符）
        term_pattern = re.compile(rf"(?<![A-Za-z0-9_\u4e00-\u9fff]){re.escape(cn)}(?![A-Za-z0-9_\u4e00-\u9fff])")
        if term_pattern.search(text):
            if not has_bilingual_annotation(text, cn, en):
                report.uncovered_terms.append(cn)
            else:
                report.annotated_terms.append(cn)

    return report


def process_file(path: Path, mode: str) -> FileReport | None:
    raw = path.read_bytes()
    has_bom = raw.startswith(b"\xef\xbb\xbf")
    original = raw.decode("utf-8-sig")

    report = check_metadata(original, path)
    coverage = check_term_coverage(original, path)
    report.uncovered_terms = coverage.uncovered_terms
    report.annotated_terms = coverage.annotated_terms

    if mode in ("enforce", "check-only"):
        return report

    # 默认模式：自动标注
    parts = []
    in_code = False
    seen_terms: set[str] = set()
    changed = False

    for line in original.splitlines(keepends=True):
        if line.lstrip().startswith("```"):
            in_code = not in_code
            parts.append(line)
            continue
        if in_code:
            parts.append(line)
            continue

        new_line, line_changed = annotate_line(line, seen_terms)
        if line_changed:
            changed = True
        parts.append(new_line)

    if changed:
        out = "".join(parts)
        data = out.encode("utf-8")
        if has_bom:
            data = b"\xef\xbb\xbf" + data
        path.write_bytes(data)

    return report


def iter_md_files(dirs: Iterable[Path]) -> Iterable[Path]:
    for directory in dirs:
        if not directory.exists():
            continue
        if directory.is_file() and directory.suffix == ".md":
            yield directory
            continue
        yield from sorted(directory.rglob("*.md"))


def write_report(
    path: Path,
    reports: list[FileReport],
    total_files: int,
    missing_en: int,
    missing_summary: int,
    uncovered_terms: set[str],
) -> None:
    """生成 Markdown 格式的双语标注基线报告。"""
    uncovered_by_term: dict[str, list[str]] = {}
    for r in reports:
        for term in r.uncovered_terms:
            uncovered_by_term.setdefault(term, []).append(str(r.path))

    top_uncovered = sorted(
        uncovered_by_term.items(), key=lambda kv: len(kv[1]), reverse=True
    )[:20]

    missing_en_files = [str(r.path) for r in reports if r.missing_en]
    missing_summary_files = [str(r.path) for r in reports if r.missing_summary]

    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S UTC")

    lines = [
        "# 国际化双语标注基线报告",
        "",
        f"> 生成日期: {now}",
        f"> 扫描文件数: {total_files}",
        f"> 生成工具: `scripts/add_bilingual_annotations.py --mode check-only --report`",
        "",
        "## 统计",
        "",
        "| 指标 | 数值 |",
        "|---|---:|",
        f"| 扫描文件数 | {total_files} |",
        f"| 缺少 EN 字段 | {missing_en} |",
        f"| 缺少 Summary 字段 | {missing_summary} |",
        f"| 未覆盖术语种类 | {len(uncovered_terms)} |",
        "",
        "## 未覆盖术语 TOP 20",
        "",
        "| 术语 | 出现文件数 |",
        "|---|---:|",
    ]
    for term, files in top_uncovered:
        lines.append(f"| {term} | {len(files)} |")

    lines += [
        "",
        "## 缺少 EN 字段的文件",
        "",
    ]
    if missing_en_files:
        for f in missing_en_files[:50]:
            lines.append(f"- `{f}`")
        if len(missing_en_files) > 50:
            lines.append(f"- ... 共 {len(missing_en_files)} 个文件")
    else:
        lines.append("无")

    lines += [
        "",
        "## 缺少 Summary 字段的文件",
        "",
    ]
    if missing_summary_files:
        for f in missing_summary_files[:50]:
            lines.append(f"- `{f}`")
        if len(missing_summary_files) > 50:
            lines.append(f"- ... 共 {len(missing_summary_files)} 个文件")
    else:
        lines.append("无")

    lines += [
        "",
        "## 建议",
        "",
        "1. 优先处理 TOP 未覆盖术语，它们在最多文件中出现。",
        "2. 对缺失 EN/Summary 的文件，参考 `concept/00_meta/bilingual_template.md` 补齐头部。",
        "3. 使用 `python scripts/add_bilingual_annotations.py --mode annotate --dir concept/XX_YYYY` 自动标注指定目录。",
        "",
        "---",
        "",
        "*本报告为基线数据，用于追踪国际化覆盖进度。*",
    ]

    path.write_text("\n".join(lines), encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="中英双语标注与国际化元数据检查")
    parser.add_argument(
        "--mode",
        choices=["annotate", "enforce", "check-only"],
        default="annotate",
        help="annotate=自动标注; enforce=强制检查全部 concept/ 并报错; check-only=只检查不修改",
    )
    parser.add_argument("--dir", nargs="+", type=Path, help="指定目录（可多次）")
    parser.add_argument("--output-uncovered", type=Path, help="输出未覆盖术语清单 JSON")
    parser.add_argument("--report", type=Path, help="输出 Markdown 检查报告")
    args = parser.parse_args(argv)

    if args.dir:
        dirs = args.dir
    elif args.mode in ("enforce", "check-only"):
        dirs = ALL_CONCEPT_DIRS
    else:
        dirs = DEFAULT_DIRS

    reports: list[FileReport] = []
    modified = 0

    for path in iter_md_files(dirs):
        # 跳过元目录自身的模板文件
        if "00_meta" in path.parts and path.name != "bilingual_template.md":
            continue
        report = process_file(path, args.mode)
        if report is None:
            continue
        reports.append(report)
        if args.mode == "annotate" and (report.annotated_terms or report.uncovered_terms):
            # 默认模式下只要有检查到术语就打印，已修改的额外标记
            print(f"{'+ ' if report.uncovered_terms else '  '}{path}")
            modified += 1

    # 汇总
    total_missing_en = sum(1 for r in reports if r.missing_en)
    total_missing_summary = sum(1 for r in reports if r.missing_summary)
    total_uncovered = {term for r in reports for term in r.uncovered_terms}

    print(f"\n扫描文件数: {len(reports)}")
    if args.mode in ("enforce", "check-only"):
        print(f"缺少 EN 字段: {total_missing_en}")
        print(f"缺少 Summary 字段: {total_missing_summary}")
        print(f"未覆盖术语种类: {len(total_uncovered)}")

    if args.output_uncovered:
        uncovered_by_term: dict[str, list[str]] = {}
        for r in reports:
            for term in r.uncovered_terms:
                uncovered_by_term.setdefault(term, []).append(str(r.path))
        args.output_uncovered.write_text(
            json.dumps(uncovered_by_term, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )
        print(f"未覆盖术语清单已保存: {args.output_uncovered}")

    if args.report:
        write_report(
            args.report,
            reports,
            len(reports),
            total_missing_en,
            total_missing_summary,
            total_uncovered,
        )
        print(f"Markdown 报告已保存: {args.report}")

    if args.mode == "enforce":
        has_error = total_missing_en or total_missing_summary or total_uncovered
        if has_error:
            print("\n❌ 强制检查失败，请修复以下问题:")
            if total_missing_en:
                print(f"  - {total_missing_en} 个文件缺少 EN 字段")
            if total_missing_summary:
                print(f"  - {total_missing_summary} 个文件缺少 Summary 字段")
            if total_uncovered:
                print(f"  - {len(total_uncovered)} 种术语未覆盖: {', '.join(sorted(total_uncovered))}")
            return 1
        print("\n✅ 强制检查通过")
        return 0

    if args.mode == "annotate":
        print(f"共处理 {len(reports)} 个文件，修改 {modified} 个")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
