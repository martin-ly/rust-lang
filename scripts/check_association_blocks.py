#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""P3-3 语义观察：concept/ 关联区块存在性与命名合规检查。

背景：2026-07-12 关联区块模板统一（见 reports/L4_REFERENCE_AND_ASSOCIATION_BLOCKS_2026_07_12.md）。
标准模板：`## 相关概念`（可带编号前缀，如「七、」），下分四个可选子项：
    - **上层概念**: ...   （前置依赖/前置概念）
    - **下层概念**: ...   （后置概念/后置延伸）
    - **对比概念**: ...
    - **应用场景**: ...

检查项（只读 concept/，排除 archive/、00_meta/、README.md）：
    A1 命名合规：关联区块标题必须为「相关概念」；
       已弃用变体「相关概念文件」「关联概念」出现即不合规（strict 下阻断）。
    A2 存在性：内容页（非重定向 stub）须有关联区块标题或 前置/后置 概念元数据。
    A3（观察，不阻断）：「相关概念链接」为待归并变体；统计 上层/下层概念 子项覆盖率。

用法：
    python scripts/check_association_blocks.py            # 默认 warning，exit 0
    python scripts/check_association_blocks.py --strict   # A1/A2 不合规 exit 1
    python scripts/check_association_blocks.py --path concept/01_foundation
"""
from __future__ import annotations

import argparse
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

HEADING_RE = re.compile(
    r"^(#{1,6})\s+(?:(?:\d+|[一二三四五六七八九十]+)[、.．]\s*)?"
    r"(相关概念|相关概念文件|关联概念|相关概念链接)\s*$",
    re.M,
)
META_RE = re.compile(r"^>\s*\*\*(前置概念|前置依赖|后置概念|后置延伸)\*\*", re.M)
DEPRECATED = {"相关概念文件", "关联概念"}
MERGE_CANDIDATE = {"相关概念链接"}
STANDARD = {"相关概念"}


def is_stub(text: str) -> bool:
    lines = text.splitlines()
    if len(lines) > 40:
        return False
    return "重定向" in text or ("权威来源" in text and "stub" in text.lower())


def scan(base: str):
    stats = {"files": 0, "missing": [], "deprecated": [], "merge": [],
             "compliant_heads": 0, "up": 0, "down": 0, "stubs": 0}
    for root, dirs, files in os.walk(base):
        dirs[:] = [d for d in dirs if d != "archive"]
        if os.sep + "00_meta" in root or root.endswith(os.sep + "00_meta"):
            continue
        for f in sorted(files):
            if not f.endswith(".md") or f == "README.md":
                continue
            path = os.path.join(root, f)
            rel = os.path.relpath(path, ROOT).replace(os.sep, "/")
            text = open(path, encoding="utf-8", errors="ignore").read()
            if is_stub(text):
                stats["stubs"] += 1
                continue
            stats["files"] += 1
            heads = HEADING_RE.findall(text)
            names = {h[1] for h in heads}
            if not heads and not META_RE.search(text):
                stats["missing"].append(rel)
            for name in sorted(names & DEPRECATED):
                stats["deprecated"].append((rel, name))
            for name in sorted(names & MERGE_CANDIDATE):
                stats["merge"].append((rel, name))
            stats["compliant_heads"] += sum(1 for h in heads if h[1] in STANDARD)
            if "**上层概念**" in text:
                stats["up"] += 1
            if "**下层概念**" in text:
                stats["down"] += 1
    return stats


def main() -> int:
    ap = argparse.ArgumentParser(description="concept/ 关联区块合规检查")
    ap.add_argument("--strict", action="store_true", help="A1/A2 不合规时 exit 1")
    ap.add_argument("--path", default=os.path.join(ROOT, "concept"), help="扫描根目录")
    args = ap.parse_args()

    s = scan(args.path)
    print("[check_association_blocks] 关联区块合规报告")
    print(f"  扫描内容页: {s['files']}（跳过重定向 stub {s['stubs']}）")
    print(f"  A1 弃用变体（相关概念文件/关联概念）: {len(s['deprecated'])}")
    for rel, name in s["deprecated"][:20]:
        print(f"    ✗ {rel} — 「{name}」应改为「相关概念」")
    print(f"  A2 缺关联区块且无前置/后置元数据: {len(s['missing'])}")
    for rel in s["missing"][:20]:
        print(f"    ✗ {rel}")
    print(f"  A3 观察: 待归并变体「相关概念链接」 {len(s['merge'])} 文件；"
          f"合规标题 {s['compliant_heads']} 处；"
          f"上层概念覆盖 {s['up']} 页，下层概念覆盖 {s['down']} 页")

    fail = bool(s["deprecated"] or s["missing"])
    if fail:
        print("  结果: 不合规" + ("（--strict 阻断）" if args.strict else "（warning）"))
    else:
        print("  结果: 合规 ✓")
    return 1 if (args.strict and fail) else 0


if __name__ == "__main__":
    sys.exit(main())
