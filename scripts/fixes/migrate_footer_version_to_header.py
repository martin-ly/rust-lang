#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""迁移 concept/ 页脚「Rust 版本」声明到文首元数据块（P3 元数据精修，2026-07-12）。

背景：约 213 个 concept 文件的版本声明写在页脚文档信息块（无 `>` 前缀），
文首口径覆盖率仅 ~56%。本脚本：

1. 识别页脚纯文本声明行 `**Rust 版本**: ...` / `**对应 Rust 版本**: ...`
   （位于 `**文档版本**`/`**最后更新**` 等元数据簇内，跳过代码围栏内行）；
2. 文首（首个 `---` 之前）无同名字段时，在 `> **Summary**:` 行后插入
   `> **Rust 版本**: <原值>`（值原样保留；仅精确值 `1.97.0+` 规范为
   `1.97.0+ (Edition 2024)`）；
3. 文首已有同名字段（双声明）时，仅删除页脚行，保留文首；
4. 同名不同值（潜在 D4 版本矛盾）时跳过该文件并报告，不擅自合并；
5. 保持文件原有行尾（CRLF/LF）。

用法：
    python scripts/fixes/migrate_footer_version_to_header.py --dry-run   # 只统计
    python scripts/fixes/migrate_footer_version_to_header.py --apply     # 执行迁移
"""
from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CONCEPT = ROOT / "concept"

FOOTER_RE = re.compile(r"^\*\*\s*(Rust\s*版本|对应\s*Rust\s*版本)\s*\*\*\s*[:：]\s*(.*?)\s*$")
HDR_RE = re.compile(r"^>\s*\*\*\s*(Rust\s*版本|对应\s*Rust\s*版本)\s*\*\*\s*[:：]\s*(.*?)\s*$")
VER_RE = re.compile(r"\b1\.(\d{2,3})(?:\.\d+)?\b")
SUMMARY_RE = re.compile(r"^>\s*\*\*Summary\*\*\s*[:：]")
EN_RE = re.compile(r"^>\s*\*\*EN\*\*\s*[:：]")
BQ_RE = re.compile(r"^>")


def norm_key(k: str) -> str:
    return re.sub(r"\s+", " ", k)


def norm_value(v: str) -> str:
    return "1.97.0+ (Edition 2024)" if v == "1.97.0+" else v


def process(path: Path, apply: bool) -> str | None:
    """返回动作描述；None 表示无需处理。apply 时写回文件。"""
    data = path.read_bytes()
    nl = "\r\n" if b"\r\n" in data else "\n"
    lines = data.decode("utf-8").split(nl)

    sep_idx = next((i for i, l in enumerate(lines) if l.strip() == "---"), len(lines))

    # 全文所有 `>` 前缀版本字段（check_metadata_consistency 的 D3/D4 按全文统计）
    header_fields: dict[str, set[str]] = {}
    in_code = False
    for l in lines:
        s = l.strip()
        if s.startswith("```"):
            in_code = not in_code
            continue
        if in_code:
            continue
        m = HDR_RE.match(s)
        if m:
            header_fields.setdefault(norm_key(m.group(1)), set()).add(m.group(2).strip())

    # 页脚纯文本声明（跳过代码围栏）
    footer: list[tuple[int, str, str]] = []
    in_code = False
    for i, l in enumerate(lines):
        s = l.strip()
        if s.startswith("```"):
            in_code = not in_code
            continue
        if in_code:
            continue
        m = FOOTER_RE.match(s)
        if m:
            footer.append((i, norm_key(m.group(1)), m.group(2).strip()))
    if not footer:
        return None

    # 同名不同值 -> 潜在 D4，跳过并报告
    for _, k, v in footer:
        if k in header_fields and v not in header_fields[k]:
            return f"SKIP(conflict {k}: 文首={sorted(header_fields[k])} 页脚={v!r})"

    to_insert: list[tuple[str, str]] = []  # 需迁移到文首的 (key, value)
    for _, k, v in footer:
        if k not in header_fields:
            to_insert.append((k, norm_value(v)))

    # D4 护栏：迁移后全文版本字段的 distinct minor 必须 < 2，
    # 否则保留页脚原样（多为 07_future 多版本跟踪页，多版本是其本意）
    minors = set()
    for vals in header_fields.values():
        for v in vals:
            minors.update(VER_RE.findall(v))
    for _, v in to_insert:
        minors.update(VER_RE.findall(v))
    if len(minors) >= 2:
        return f"SKIP(D4-risk minors={sorted(minors)})"

    # 文首插入点：首个 --- 之前的 Summary 行之后；回退 EN 行；再回退文首最后一个 blockquote 行
    ins_idx = None
    for rx in (SUMMARY_RE, EN_RE, BQ_RE):
        cand = [i for i, l in enumerate(lines[:sep_idx]) if rx.match(l.strip())]
        if cand:
            ins_idx = cand[-1] + 1
            break
    if to_insert and ins_idx is None:
        return "SKIP(no header anchor)"

    new_lines = list(lines)
    shift = 0
    if to_insert:
        payload = [f"> **{k}**: {v}" for k, v in to_insert]
        new_lines[ins_idx:ins_idx] = payload
        shift = len(payload)
    # 删除页脚原声明行（插入后索引顺延）
    anchor = ins_idx if to_insert else 10**9
    del_new = {i + (shift if i >= anchor else 0) for i, _, _ in footer}
    new_lines = [l for j, l in enumerate(new_lines) if j not in del_new]

    action = f"migrate={[(k, v) for k, v in to_insert]} delete_footer={len(footer)}"
    if apply:
        path.write_bytes(nl.join(new_lines).encode("utf-8"))
    return action


def main() -> int:
    ap = argparse.ArgumentParser()
    g = ap.add_mutually_exclusive_group(required=True)
    g.add_argument("--dry-run", action="store_true")
    g.add_argument("--apply", action="store_true")
    args = ap.parse_args()

    files = sorted(CONCEPT.rglob("*.md"))
    n_migrate = n_dedup = n_skip = 0
    for f in files:
        rel = f.relative_to(ROOT).as_posix()
        action = process(f, apply=args.apply)
        if action is None:
            continue
        if action.startswith("SKIP"):
            n_skip += 1
            print(f"  {action}  {rel}")
        else:
            if "migrate=[]" in action:
                n_dedup += 1
            else:
                n_migrate += 1
            print(f"  {action}  {rel}")
    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"[{mode}] migrate={n_migrate} dedup(delete footer only)={n_dedup} skip={n_skip} total_files={len(files)}")
    return 0 if n_skip == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
