#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
命名规范 lint（AGENTS.md §4.0，2026-07-12 全库重编号后生效）。

扫描 concept/、knowledge/、docs/、content/、crates/*/docs/，检查：

  N1 序号格式：带序号文件必须 NN_ 两位数字前缀 + snake_case slug（ERROR）
  N2 同目录同号冲突（ERROR）
  N3 双前缀（如 06_20_foo.md）/ 异形前缀（如 1_2_foo.md、1_foo.md、001_foo.md）（ERROR）
  N4 变体后缀 *_final / *_expanded / *_supplement（ERROR；stub 豁免：文件 ≤15 行且含
     "权威来源" blockquote 的视为已处置 stub，降级 WARN）
  N5 一级目录两位连续不跳号（concept/、docs/、knowledge/ 顶层；WARN，大目录允许留空号策略）
  N6 中文文件名 / 空格 / 混合大小写（ERROR；archive/、reports/、.kimi/、.github/ 本就不在扫描范围）

豁免文件名（大小写不敏感）：README.md、SUMMARY.md、INDEX.md、CHANGELOG.md、AGENTS.md。
无序号专题系列目录（AGENTS.md §4.0-4）：其内无序号 .md 文件按 WARN 而非 ERROR；
book/、tmp/、target/、vendor/、archive/、reports/、.git/ 不扫描。

默认观察模式 exit 0；--strict 时 ERROR>0 则 exit 1。

用法:
    python scripts/check_naming_convention.py [--strict]
"""
from __future__ import annotations

import glob
import os
import re
import sys
from collections import defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

SCAN_ROOTS = ["concept", "knowledge", "docs", "content"]
SCAN_ROOTS += sorted(glob.glob(os.path.join(ROOT, "crates", "*", "docs")))
SCAN_ROOTS = [os.path.relpath(r, ROOT).replace(os.sep, "/") for r in SCAN_ROOTS]

# 不进入的子目录（含 §4.0 豁免目录与构建/临时产物）
SKIP_DIR_NAMES = {
    "archive", "deprecated", "sources", "target", ".git", "node_modules",
    "__pycache__", ".venv", "venv", ".pytest_cache", "book", "tmp", "vendor",
    "reports", ".kimi", ".github",
}

# 豁免文件名（小写比较）
EXEMPT_FILES = {"readme.md", "summary.md", "index.md", "changelog.md", "agents.md"}

# 无序号专题系列目录（AGENTS.md §4.0-4）：其下无序号 .md 文件按 WARN 处理
UNNUMBERED_SERIES_DIRS = {
    "concept/00_meta/00_framework",
    "concept/00_meta/knowledge_topology",
    "concept/07_future/00_version_tracking",
}

# N5 一级目录连续性检查对象（顶层）
N5_TOP_LEVELS = ["concept", "docs", "knowledge"]

NUMBERED_RE = re.compile(r"^(\d{2})_(.+)$")
DOUBLE_PREFIX_RE = re.compile(r"^\d+_\d+_")          # 06_20_ / 1_2_
SINGLE_DIGIT_RE = re.compile(r"^\d_")                # 1_foo
LONG_DIGIT_RE = re.compile(r"^\d{3,}_")              # 001_foo
SNAKE_SLUG_RE = re.compile(r"^[a-z0-9]+(?:_[a-z0-9]+)*$")
VARIANT_SUFFIX_RE = re.compile(r"_(?:final|expanded|supplement)$")
CJK_RE = re.compile(r"[\u3400-\u4dbf\u4e00-\u9fff]")

MAX_REPORT = 50


def is_stub(path: str) -> bool:
    """≤15 行且含 '权威来源' blockquote 视为已处置 stub。"""
    try:
        with open(path, encoding="utf-8", errors="ignore") as f:
            lines = f.readlines()
    except OSError:
        return False
    if len(lines) > 15:
        return False
    return any(l.lstrip().startswith(">") and "权威来源" in l for l in lines)


def in_series_dir(rel_dir: str) -> bool:
    rel_dir = rel_dir.replace(os.sep, "/")
    if rel_dir in UNNUMBERED_SERIES_DIRS:
        return True
    # knowledge/ 下既有无序号结构整体按 WARN（AGENTS.md §4.0 任务约定）
    return rel_dir == "knowledge" or rel_dir.startswith("knowledge/")


def main() -> int:
    strict = "--strict" in sys.argv[1:]

    findings: list[tuple[str, str, str, str]] = []  # (level, rule, path, msg)
    stats = defaultdict(int)
    n_files = 0
    n_dirs = 0

    def add(level: str, rule: str, path: str, msg: str):
        findings.append((level, rule, path.replace(os.sep, "/"), msg))
        stats[f"{rule}_{level}"] += 1

    for root in SCAN_ROOTS:
        abs_root = os.path.join(ROOT, root)
        if not os.path.isdir(abs_root):
            continue
        for dirpath, dirnames, filenames in os.walk(abs_root):
            dirnames[:] = [
                d for d in dirnames
                if d not in SKIP_DIR_NAMES and not d.startswith(".")
            ]
            rel_dir = os.path.relpath(dirpath, ROOT)

            # --- 目录名检查 ---
            for d in dirnames:
                n_dirs += 1
                p = os.path.join(rel_dir, d)
                check_name(d, p, is_dir=True, rel_dir=rel_dir, add=add)

            # --- 文件名检查 ---
            num_seen: dict[str, list[str]] = defaultdict(list)
            for fn in filenames:
                n_files += 1
                p = os.path.join(rel_dir, fn)
                if fn.lower() in EXEMPT_FILES:
                    continue
                m = NUMBERED_RE.match(fn)
                if m:
                    num_seen[m.group(1)].append(fn)
                check_name(fn, p, is_dir=False, rel_dir=rel_dir, add=add)
            # --- N2 同目录同号冲突（文件）---
            for num, names in num_seen.items():
                if len(names) > 1:
                    add("ERROR", "N2", rel_dir,
                        f"同目录序号 {num}_ 冲突: {', '.join(sorted(names))}")

            # --- N2 目录同号 ---
            dnum: dict[str, list[str]] = defaultdict(list)
            for d in dirnames:
                m = NUMBERED_RE.match(d)
                if m:
                    dnum[m.group(1)].append(d)
            for num, names in dnum.items():
                if len(names) > 1:
                    add("ERROR", "N2", rel_dir,
                        f"同目录序号 {num}_ 目录冲突: {', '.join(sorted(names))}")

    # --- N5 一级目录两位连续不跳号（WARN）---
    for top in N5_TOP_LEVELS:
        abs_top = os.path.join(ROOT, top)
        if not os.path.isdir(abs_top):
            continue
        nums = []
        for d in os.listdir(abs_top):
            if not os.path.isdir(os.path.join(abs_top, d)):
                continue
            m = NUMBERED_RE.match(d)
            if m and m.group(1) != "99":  # 99_archive 为约定归档标记，不参与连续性
                nums.append(int(m.group(1)))
        if nums:
            expected = list(range(min(nums), max(nums) + 1))
            gaps = sorted(set(expected) - set(nums))
            if gaps:
                add("WARN", "N5", top,
                    f"一级目录跳号: 缺 {', '.join(f'{g:02d}' for g in gaps)}"
                    "（大目录留空号须在 README 记录原因，AGENTS.md §4.0-3）")

    # --- 输出 ---
    n_err = sum(1 for f in findings if f[0] == "ERROR")
    n_warn = sum(1 for f in findings if f[0] == "WARN")
    print(f"[check_naming_convention] 扫描 {len(SCAN_ROOTS)} 个根目录: "
          f"{n_files} 文件 / {n_dirs} 目录")
    print(f"汇总: ERROR={n_err}  WARN={n_warn}")
    for rule in ["N1", "N2", "N3", "N4", "N5", "N6"]:
        e = stats.get(f"{rule}_ERROR", 0)
        w = stats.get(f"{rule}_WARN", 0)
        if e or w:
            print(f"  {rule}: ERROR={e} WARN={w}")
    if findings:
        # ERROR 优先展示，保证截断后仍可见全部 ERROR
        findings.sort(key=lambda f: (f[0] != "ERROR", f[1], f[2]))
        print(f"--- 问题清单（前 {MAX_REPORT} 条 / 共 {len(findings)} 条，ERROR 优先）---")
        for level, rule, path, msg in findings[:MAX_REPORT]:
            print(f"[{level}][{rule}] {path} — {msg}")
        if len(findings) > MAX_REPORT:
            print(f"... 其余 {len(findings) - MAX_REPORT} 条省略")

    if n_err == 0:
        print("✅ 命名规范检查通过（无 ERROR）。")
    else:
        print(f"❌ 发现 {n_err} 个 ERROR 级命名问题。")
    if strict and n_err > 0:
        return 1
    return 0


def check_name(name: str, path: str, is_dir: bool, rel_dir: str, add):
    # N3 双前缀 / 异形前缀
    if DOUBLE_PREFIX_RE.match(name):
        add("ERROR", "N3", path, "双前缀/异形复合前缀（应为单一 NN_ 两位前缀）")
        return
    if SINGLE_DIGIT_RE.match(name) or LONG_DIGIT_RE.match(name):
        add("ERROR", "N3", path, "异形序号前缀（必须为两位 NN_）")
        return

    m = NUMBERED_RE.match(name)
    if m:
        # N1 带序号条目：slug 必须 snake_case
        slug = m.group(2)
        if not is_dir:
            stem, dot, ext = slug.rpartition(".")
            if not dot or not re.fullmatch(r"[a-z0-9]+", ext):
                add("ERROR", "N1", path, "带序号文件扩展名异常")
                return
            slug = stem
        if not SNAKE_SLUG_RE.fullmatch(slug):
            add("ERROR", "N1", path,
                "带序号条目 slug 必须为小写 snake_case（仅 [a-z0-9_]）")
            return
        # N4 变体后缀
        if not is_dir and VARIANT_SUFFIX_RE.search(slug):
            if is_stub(os.path.join(ROOT, path)):
                add("WARN", "N4", path,
                    "变体后缀文件，但已是处置 stub（≤15 行 + 权威来源 blockquote）")
            else:
                add("ERROR", "N4", path,
                    "变体后缀 *_final/*_expanded/*_supplement 禁止保留正文"
                    "（应并入主干后 stub 化或删除，AGENTS.md §4.0-6）")
        return

    # 无序号条目
    # N6 中文/空格/混合大小写
    if CJK_RE.search(name) or " " in name or re.search(r"[A-Z]", name):
        add("ERROR", "N6", path, "文件名含中文/空格/大写字母")
        return

    if is_dir:
        # crates/*/docs/ 下 tier_0N_* 为 §4.0-6  sanctioned 结构，不告警
        if re.fullmatch(r"tier_0\d+_[a-z0-9_]+", name) and rel_dir.replace(os.sep, "/").startswith("crates/"):
            return
        # 无序号 snake_case 目录：专题系列/既有结构，WARN 提示需 README 索引（§4.0-4）
        add("WARN", "N1", path,
            "无序号目录（专题系列须集中于同一目录并有 README 索引，AGENTS.md §4.0-4）")
        return

    if name.endswith(".md"):
        if in_series_dir(rel_dir):
            add("WARN", "N1", path, "无序号专题系列文件（WARN，系列目录约定）")
        else:
            add("ERROR", "N1", path,
                "内容 .md 文件缺少 NN_ 两位序号前缀（非专题系列白名单目录）")


if __name__ == "__main__":
    sys.exit(main())
