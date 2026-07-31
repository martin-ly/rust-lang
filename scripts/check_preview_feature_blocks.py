#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""预览特性代码块编译探测工具（E9 迁移产物）。

来源：原 tmp/validate_198_blocks/extract_and_compile.py 迁移至 scripts/，
用于验证 `concept/07_future/00_version_tracking/` 等预览/稳定化跟踪页中
被标记为 `rust,ignore` / `no_run` 的代码块在当前 stable rustc 下的真实编译
结果，确保“因特性未稳定而 ignore”的示例确实因预期理由失败。

与 `scripts/check_concept_code_blocks.py` 的关系：
- 主脚本负责 `concept/` 所有 ```rust 块（candidate/compile_fail/dep 等），
  是阻断门 21 的正式工具；
- 本脚本专攻 preview/stabilized 版本跟踪页中被 ignore 的块，补充验证这些
  块是否因 feature gate / 未稳定 API 而失败，防止“一旦特性稳定，ignore
  块悄悄腐烂”而无感知。

用法：
    python scripts/check_preview_feature_blocks.py
    python scripts/check_preview_feature_blocks.py --strict --json tmp/pfb.json
    python scripts/check_preview_feature_blocks.py --paths concept/07_future/00_version_tracking/rust_1_98_*.md
"""

from __future__ import annotations

import argparse
import fnmatch
import json
import os
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_PATHS = [
    "concept/07_future/00_version_tracking/rust_1_98_stabilized.md",
    "concept/07_future/00_version_tracking/rust_1_98_preview.md",
    "concept/07_future/00_version_tracking/feature_domain_matrix_198.md",
    "concept/07_future/00_version_tracking/migration_198_decision_tree.md",
]
DEFAULT_OUT_DIR = ROOT / "tmp" / "check_preview_feature_blocks"
DEFAULT_REPORT = ROOT / "tmp" / "check_preview_feature_blocks_report.md"

# 匹配 rust,ignore / ignore,rust / no_run / rust,no_run / no_run,rust 等变体
FENCE_RE = re.compile(
    r"^\s*```(?:rust,ignore|ignore,rust|no_run|rust,no_run|no_run,rust)\b"
)

# 预期的“因未稳定而失败”信号；命中则视为 Expected fail，否则标记为 Unexpected fail
EXPECTED_MARKERS = [
    "e0554",
    "e0658",
    "use of unstable",
    "unstable library feature",
    "has not been marked as const",
    "requires nightly",
    "feature gate",
    "named_fn_trait_parameters",
    "pin_ergonomics",
    "async_drop",
    "return_type_notation",
    "float_algebraic",
    "nonzero_from_str_radix",
    "box_as_ptr",
    "int_format_into",
    "async fn in trait",
    "cannot find attribute",
    "expected one of",
    "wrong number of type arguments",
]


def discover_files(paths: list[str]) -> list[Path]:
    files: list[Path] = []
    seen = set()
    for p in paths:
        target = ROOT / p
        if target.is_file():
            if str(target) not in seen:
                files.append(target)
                seen.add(str(target))
        elif target.is_dir():
            for f in target.rglob("*.md"):
                if str(f) not in seen:
                    files.append(f)
                    seen.add(str(f))
        elif "*" in p or "?" in p:
            # 支持相对通配符，例如 concept/07_future/00_version_tracking/rust_1_98_*.md
            for f in ROOT.rglob("*.md"):
                rel = f.relative_to(ROOT).as_posix()
                if fnmatch.fnmatch(rel, p) and str(f) not in seen:
                    files.append(f)
                    seen.add(str(f))
        else:
            print(f"[warn] path not found: {p}", file=sys.stderr)
    return sorted(files)


def extract_blocks(path: Path) -> list[dict]:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    blocks = []
    i = 0
    while i < len(lines):
        if FENCE_RE.match(lines[i]):
            fence_line = i + 1  # 1-based line number of the opening fence
            content_lines = []
            i += 1
            while i < len(lines) and not lines[i].strip().startswith("```"):
                content_lines.append(lines[i])
                i += 1
            blocks.append(
                {"fence_line": fence_line, "content": "\n".join(content_lines)}
            )
        else:
            i += 1
    return blocks


def determine_wrapping(content: str) -> tuple[str, str]:
    stripped = content.strip()
    if not stripped:
        return ("empty", "")

    # 显式 fn main -> 保持原样作为 binary
    if re.search(r"\bfn main\s*\(", stripped):
        return ("has fn main", stripped)

    # 模块级项启发式：所有非空非注释行都以顶层关键字/属性开头，且无裸表达式
    item_kw = {
        "use", "mod", "pub", "fn", "struct", "enum", "trait", "impl", "type",
        "const", "static", "unsafe", "extern", "macro_rules",
    }
    lines = stripped.splitlines()
    non_empty = [
        ln for ln in lines if ln.strip() and not ln.strip().startswith("//")
    ]
    if non_empty:
        all_items = all(
            any(ln.strip().startswith(k) for k in item_kw)
            or ln.strip().startswith("#")
            for ln in non_empty
        )
    else:
        all_items = False

    if all_items:
        return ("module items", stripped)
    return ("wrapped in main", f"fn main() {{\n{stripped}\n}}")


def classify(stderr: str, returncode: int) -> tuple[str, str]:
    if returncode == 0:
        return ("OK", "compiled successfully")
    low = stderr.lower()
    if any(m in low for m in EXPECTED_MARKERS):
        return ("Expected fail", "unstable/preview feature gate failure")
    return ("Unexpected fail", (stderr.splitlines()[0] if stderr else ""))


def compile_block(
    path: Path, block: dict, out_dir: Path, rustc: str, edition: str
) -> dict:
    fence_line = block["fence_line"]
    content = block["content"]
    wrap_desc, source = determine_wrapping(content)

    rs_file = out_dir / f"{path.stem}_{fence_line}.rs"
    rs_file.write_text(source + "\n", encoding="utf-8")

    proc = subprocess.run(
        [rustc, "--edition", edition, "-o", str(rs_file.with_suffix("")), str(rs_file)],
        capture_output=True,
        text=True,
    )
    category, note = classify(proc.stderr, proc.returncode)
    return {
        "file": str(path.relative_to(ROOT).as_posix()),
        "line": fence_line,
        "wrap": wrap_desc,
        "category": category,
        "note": note,
        "returncode": proc.returncode,
        "stderr": proc.stderr,
    }


def build_report(results: list[dict], out_file: Path) -> None:
    lines = [
        "# Preview Feature Block Compile Report",
        "",
        "| file | line | wrap | result | note |",
        "|---|---|---|---|---|",
    ]
    for r in results:
        note = r["note"].replace("|", "\\|")
        lines.append(
            f"| {r['file']} | {r['line']} | {r['wrap']} | {r['category']} | {note} |"
        )

    counts: dict[str, int] = {}
    for r in results:
        counts[r["category"]] = counts.get(r["category"], 0) + 1
    lines.extend(["", "## Summary", ""])
    for cat, cnt in sorted(counts.items()):
        lines.append(f"- {cat}: {cnt}")

    out_file.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Compile probe for rust,ignore / no_run blocks in preview/stabilization pages."
    )
    parser.add_argument(
        "--paths",
        nargs="+",
        default=DEFAULT_PATHS,
        help="Markdown files or directories to scan (default: 1.98 version tracking pages).",
    )
    parser.add_argument(
        "--out-dir",
        type=Path,
        default=DEFAULT_OUT_DIR,
        help="Directory for extracted .rs files.",
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=DEFAULT_REPORT,
        help="Markdown report output path.",
    )
    parser.add_argument(
        "--json",
        type=Path,
        default=None,
        help="JSON results output path.",
    )
    parser.add_argument(
        "--rustc",
        default="rustc",
        help="rustc binary to use.",
    )
    parser.add_argument(
        "--edition",
        default="2024",
        help="Edition passed to rustc.",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Exit non-zero if any block is Unexpected fail or compiles OK unexpectedly.",
    )
    args = parser.parse_args()

    args.out_dir.mkdir(parents=True, exist_ok=True)

    files = discover_files(args.paths)
    if not files:
        print("[warn] no markdown files matched", file=sys.stderr)
        return 0

    results: list[dict] = []
    print("| file | line | wrap | result | note |")
    print("|---|---|---|---|---|")
    for path in files:
        blocks = extract_blocks(path)
        for block in blocks:
            res = compile_block(path, block, args.out_dir, args.rustc, args.edition)
            results.append(res)
            note = res["note"].replace("|", "\\|")
            print(
                f"| {res['file']} | {res['line']} | {res['wrap']} | {res['category']} | {note} |"
            )

    build_report(results, args.report)
    if args.json:
        args.json.parent.mkdir(parents=True, exist_ok=True)
        args.json.write_text(
            json.dumps(results, indent=2, ensure_ascii=False), encoding="utf-8"
        )

    unexpected = [r for r in results if r["category"] == "Unexpected fail"]
    ok_blocks = [r for r in results if r["category"] == "OK"]
    print(f"\n[summary] OK={len(ok_blocks)} Expected fail={len([r for r in results if r['category'] == 'Expected fail'])} Unexpected fail={len(unexpected)}")
    print(f"[report] {args.report}")

    if args.strict and (unexpected or ok_blocks):
        # strict 模式下：预览特性页中的 ignore/no_run 块应当是“预期失败”（未稳定）；
        # 若编译通过（OK）或意外失败，都说明标注/正文可能需要更新。
        print(
            f"[strict] {len(unexpected)} unexpected fail + {len(ok_blocks)} OK blocks; exit 1",
            file=sys.stderr,
        )
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
