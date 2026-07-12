#!/usr/bin/env python3
"""plan_renumber.py — 生成目录内两位连续序号（NN_）重编号计划的 dry-run 映射表。

本脚本**只读仓库、只写映射表与报告**，不移动任何文件。

背景决策（2026-07，用户确认）：
- `concept/` 下所有文件统一为**目录内两位连续序号 NN_** 命名；
- `00_` 保留给导览页（现有 `00_` 前缀文件保留 00 序号）；
- README.md 默认保持原名（`--readme-mode keep`，GitHub/mdBook 约定），
  可用 `--readme-mode number` 改为 `00_README.md`；
- 无序号专题系列文件保持无序号，排在同目录序号文件之后：
  * 文件名匹配 `rust_1_<NN>_*`（如 rust_1_90_stabilized.md）；
  * `00_meta/00_framework/` 下的无序号文件；
  * `07_future/00_version_tracking/` 下的无序号文件；
- SUMMARY.md（mdBook TOC）永不改名。

目录内目标顺序：
  1. README.md 永远最前（order 0）；
  2. `<root>/SUMMARY.md` 中条目出现顺序为教学顺序；
  3. SUMMARY 未收录的文件按文件名字母序追加；
  4. 无序号专题系列文件排在序号文件之后（SUMMARY 顺序优先，否则字母序）。

用法：
    python scripts/plan_renumber.py --root concept \
        --out tmp/renumber/mapping_concept.csv \
        --report tmp/renumber/plan_report.md
"""

from __future__ import annotations

import argparse
import csv
import posixpath
import re
import sys
from collections import defaultdict
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_REPO_ROOT = REPO_ROOT

# 扫描时排除的路径组件（相对 root 的任意层级）
EXCLUDE_DIR_NAMES = {"archive", "sources", "book", "tmp", "reports", "vendor", "target", ".git"}
EXCLUDE_DIR_RE = re.compile(r"quiz", re.IGNORECASE)  # quiz / quizzes 目录
EXCLUDE_EXACT_DIRS = {"knowledge_topology"}  # atlas 生成目录

# 无序号专题系列判定
SERIES_NAME_RE = re.compile(r"^rust_1_\d+_", re.IGNORECASE)
SERIES_DIRS = ("00_meta/00_framework", "07_future/00_version_tracking")

SUMMARY_LINK_RE = re.compile(r"^\s*- \[([^\]]*)\]\(([^)]+)\)")
LEADING_NUM_RE = re.compile(r"^(\d+)_")
MULTI_PREFIX_RE = re.compile(r"^(\d+[_\-. ])+")

REASONS = ("renumber", "prefix_cleanup", "collision_resolve", "unchanged")


def to_posix(p: str) -> str:
    return p.replace("\\", "/")


def parse_summary(summary_path: Path, root_rel: str) -> list[str]:
    """解析 SUMMARY.md，返回条目目标路径列表（相对仓库根，posix），保持出现顺序。"""
    ordered: list[str] = []
    seen: set[str] = set()
    if not summary_path.exists():
        return ordered
    for line in summary_path.read_text(encoding="utf-8").splitlines():
        m = SUMMARY_LINK_RE.match(line)
        if not m:
            continue
        target = m.group(2).strip()
        if target.startswith(("http://", "https://", "#", "/")):
            continue
        target = target.split("#")[0]
        if not target.endswith(".md"):
            continue
        full = posixpath.normpath(posixpath.join(root_rel, target))
        if full not in seen:
            seen.add(full)
            ordered.append(full)
    return ordered


def is_excluded(rel_parts: tuple[str, ...]) -> bool:
    for part in rel_parts:
        if part in EXCLUDE_DIR_NAMES or part in EXCLUDE_EXACT_DIRS:
            return True
        if EXCLUDE_DIR_RE.search(part):
            return True
    return False


def scan_md_files(root_abs: Path, root_rel: str) -> list[str]:
    """扫描 root 下所有 .md 文件（相对仓库根 posix 路径），应用排除规则。"""
    out: list[str] = []
    for p in sorted(root_abs.rglob("*.md")):
        rel = p.relative_to(root_abs)
        if is_excluded(rel.parts[:-1]):
            continue
        out.append(to_posix(posixpath.join(root_rel, to_posix(str(rel)))))
    return out


def is_series_file(name: str, dir_rel_to_root: str, root_rel: str) -> bool:
    """判断无序号文件是否属于「保持无序号」的专题系列。"""
    if LEADING_NUM_RE.match(name) or MULTI_PREFIX_RE.match(name):
        return False  # 有序号（含异形前缀）的不算无序号系列
    if SERIES_NAME_RE.match(name):
        return True
    dir_in_root = posixpath.relpath(dir_rel_to_root, root_rel) if dir_rel_to_root != root_rel else "."
    return any(dir_in_root == d or dir_in_root.endswith("/" + d) for d in SERIES_DIRS)


def clean_slug(name: str) -> tuple[str, bool, int | None]:
    """返回 (slug, 是否做了异形清理, 原序号)。

    - `01_foo.md`        -> ("foo.md", False, 1)
    - `01_02_foo.md`     -> ("foo.md", True, 1)   双前缀清理
    - `01-foo.md`/`01 foo.md` -> ("foo.md", True, 1)  异形前缀清理
    - `foo.md`           -> ("foo.md", False, None)
    """
    m = LEADING_NUM_RE.match(name)
    simple_num = int(m.group(1)) if m else None
    slug = name[m.end():] if m else name
    cleaned = MULTI_PREFIX_RE.sub("", name) if MULTI_PREFIX_RE.match(name) else slug
    # 双前缀情形：MULTI_PREFIX_RE 会吃掉 "01_02_"，此时原序号取第一段
    if cleaned != slug:
        m2 = LEADING_NUM_RE.match(name)
        simple_num = int(m2.group(1)) if m2 else simple_num
        return cleaned, True, simple_num
    return slug, False, simple_num


def plan_directory(
    dir_path: str,
    files: list[str],
    summary_order: list[str],
    readme_mode: str,
) -> list[dict]:
    """为单个目录生成重编号计划行。"""
    order_rank = {p: i for i, p in enumerate(summary_order)}
    names = sorted(posixpath.basename(f) for f in files)

    readme = [n for n in names if n.upper() == "README.MD"]
    special = [n for n in names if n == "SUMMARY.md"]
    series = [n for n in names if n not in readme and n not in special
              and is_series_file(n, dir_path, ROOT_REL_GLOBAL)]
    numbered = [n for n in names if n not in readme and n not in special and n not in series]

    # 序号文件的目标顺序：SUMMARY 顺序优先，未收录的字母序追加
    def sort_key(n: str) -> tuple[int, str]:
        full = posixpath.join(dir_path, n)
        if full in order_rank:
            return (0, f"{order_rank[full]:06d}")
        return (1, n.lower())

    numbered.sort(key=sort_key)
    series.sort(key=sort_key)

    rows: list[dict] = []
    used_targets: set[str] = set()
    next_nn = 1

    def alloc_target(slug: str, want_nn: int | None) -> tuple[str, int, bool]:
        """分配不冲突的 <NN>_<slug>；返回 (target_name, nn, bumped)。"""
        nonlocal next_nn
        if want_nn is not None:
            cand = f"{want_nn:02d}_{slug}"
            if cand not in used_targets:
                return cand, want_nn, False
        nn = max(next_nn, 1)
        bumped = False
        while True:
            cand = f"{nn:02d}_{slug}"
            if cand not in used_targets:
                next_nn = nn + 1
                return cand, nn, bumped
            bumped = True
            nn += 1

    # README 优先
    for n in readme:
        old = posixpath.join(dir_path, n)
        if readme_mode == "number":
            target = "00_README.md"
            used_targets.add(target)
            new = posixpath.join(dir_path, target)
            rows.append(dict(old_path=old, new_path=new,
                             reason="unchanged" if n == target else "renumber",
                             order_in_dir="0"))
        else:
            rows.append(dict(old_path=old, new_path=old, reason="unchanged", order_in_dir="0"))

    # 现有 00_ 前缀文件保留 00 序号（导览页约定）
    guide = [n for n in numbered if clean_slug(n)[2] == 0]
    rest = [n for n in numbered if clean_slug(n)[2] != 0]

    for n in guide:
        slug, cleaned, _ = clean_slug(n)
        target, _, bumped = alloc_target(slug, 0)
        used_targets.add(target)
        old = posixpath.join(dir_path, n)
        new = posixpath.join(dir_path, target)
        reason = "unchanged"
        if bumped:
            reason = "collision_resolve"
        elif cleaned:
            reason = "prefix_cleanup"
        elif n != target:
            reason = "renumber"
        rows.append(dict(old_path=old, new_path=new, reason=reason, order_in_dir="0"))

    for n in rest:
        slug, cleaned, orig_num = clean_slug(n)
        target, nn, bumped = alloc_target(slug, None)
        used_targets.add(target)
        old = posixpath.join(dir_path, n)
        new = posixpath.join(dir_path, target)
        if n == target:
            reason = "unchanged"
        elif bumped:
            reason = "collision_resolve"
        elif cleaned:
            reason = "prefix_cleanup"
        else:
            reason = "renumber"
        rows.append(dict(old_path=old, new_path=new, reason=reason, order_in_dir=str(nn)))

    for n in special:  # SUMMARY.md 永不改名
        old = posixpath.join(dir_path, n)
        rows.append(dict(old_path=old, new_path=old, reason="unchanged", order_in_dir=""))

    for n in series:  # 无序号专题系列：保持原名，排在序号文件之后
        old = posixpath.join(dir_path, n)
        rows.append(dict(old_path=old, new_path=old, reason="unchanged", order_in_dir=""))

    return rows


def dir_of(p: str) -> str:
    return posixpath.dirname(p)


def review_suspects(rows: list[dict]) -> list[str]:
    """检测 SUMMARY 顺序与现序号严重矛盾的目录/文件。"""
    by_dir: dict[str, list[dict]] = defaultdict(list)
    for r in rows:
        if r["order_in_dir"] not in ("", "0"):
            by_dir[dir_of(r["old_path"])].append(r)
    out: list[str] = []
    for d, rs in sorted(by_dir.items()):
        pairs = [(clean_slug(posixpath.basename(r["old_path"]))[2], int(r["order_in_dir"]),
                  posixpath.basename(r["old_path"])) for r in rs]
        pairs = [(c, n, name) for c, n, name in pairs if c is not None]
        if len(pairs) < 4:
            continue
        cur_sorted = sorted(pairs, key=lambda t: t[0])
        cur_rank = {name: i for i, (_, _, name) in enumerate(cur_sorted)}
        new_rank = {name: i for i, (_, _, name) in enumerate(sorted(pairs, key=lambda t: t[1]))}
        inv = 0
        total = 0
        names = [name for _, _, name in pairs]
        for i in range(len(names)):
            for j in range(i + 1, len(names)):
                total += 1
                if (cur_rank[names[i]] - cur_rank[names[j]]) * (new_rank[names[i]] - new_rank[names[j]]) < 0:
                    inv += 1
        if total and inv / total > 0.3:
            worst = sorted(pairs, key=lambda t: -abs(cur_rank[t[2]] - new_rank[t[2]]))[:5]
            out.append(f"- `{d}/`：序号逆序率 {inv}/{total}={inv/total:.0%}，"
                       f"位移最大文件：" + "、".join(
                           f"`{w[2]}`（现 #{w[0]:02d}→目标 #{w[1]:02d}）" for w in worst))
    return out


ROOT_REL_GLOBAL = "concept"


def main() -> int:
    global ROOT_REL_GLOBAL
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--root", default="concept", help="扫描根目录（相对仓库根），如 concept/docs/knowledge")
    ap.add_argument("--out", default="tmp/renumber/mapping_concept.csv", help="输出映射 CSV")
    ap.add_argument("--report", default="tmp/renumber/plan_report.md", help="输出计划报告")
    ap.add_argument("--summary", default=None, help="SUMMARY.md 路径（默认 <root>/SUMMARY.md）")
    ap.add_argument("--readme-mode", choices=("keep", "number"), default="keep",
                    help="README.md 处理方式：keep=保持原名（默认）；number=改名为 00_README.md")
    ap.add_argument("--repo-root", default=str(DEFAULT_REPO_ROOT),
                    help="仓库根（CSV 路径相对此目录；默认脚本所在仓库）")
    args = ap.parse_args()

    global REPO_ROOT
    REPO_ROOT = Path(args.repo_root).resolve()
    ROOT_REL_GLOBAL = to_posix(args.root).strip("/")
    root_abs = REPO_ROOT / ROOT_REL_GLOBAL
    if not root_abs.is_dir():
        print(f"ERROR: root 不存在: {root_abs}", file=sys.stderr)
        return 2

    summary_path = Path(args.summary) if args.summary else root_abs / "SUMMARY.md"
    summary_order = parse_summary(summary_path, ROOT_REL_GLOBAL)
    files = scan_md_files(root_abs, ROOT_REL_GLOBAL)

    by_dir: dict[str, list[str]] = defaultdict(list)
    for f in files:
        by_dir[dir_of(f)].append(f)

    all_rows: list[dict] = []
    for d in sorted(by_dir):
        all_rows.extend(plan_directory(d, by_dir[d], summary_order, args.readme_mode))

    # ---- 写出 CSV ----
    out_path = REPO_ROOT / args.out if not Path(args.out).is_absolute() else Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with out_path.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=("old_path", "new_path", "reason", "order_in_dir"))
        w.writeheader()
        for r in sorted(all_rows, key=lambda r: (r["old_path"])):
            w.writerow(r)

    # ---- 统计与报告 ----
    def layer_of(p: str) -> str:
        rel = posixpath.relpath(p, ROOT_REL_GLOBAL)
        return rel.split("/")[0] if "/" in rel else "(root)"

    per_layer: dict[str, dict[str, int]] = defaultdict(lambda: defaultdict(int))
    per_dir: dict[str, dict[str, int]] = defaultdict(lambda: defaultdict(int))
    series_list: list[str] = []
    collisions: list[str] = []
    for r in all_rows:
        d = dir_of(r["old_path"])
        per_layer[layer_of(r["old_path"])][r["reason"]] += 1
        per_layer[layer_of(r["old_path"])]["total"] += 1
        per_dir[d][r["reason"]] += 1
        per_dir[d]["total"] += 1
        name = posixpath.basename(r["old_path"])
        if r["reason"] == "unchanged" and r["order_in_dir"] == "" and name != "SUMMARY.md":
            series_list.append(r["old_path"])
        if r["reason"] == "collision_resolve":
            collisions.append(f"- `{r['old_path']}` → `{r['new_path']}`")

    # SUMMARY 收录但磁盘不存在
    disk_set = set(files)
    missing = [p for p in summary_order if p not in disk_set
               and not is_excluded(tuple(posixpath.relpath(p, ROOT_REL_GLOBAL).split("/")[:-1]))]

    suspects = review_suspects(all_rows)

    n_changed = sum(1 for r in all_rows if r["old_path"] != r["new_path"])
    lines: list[str] = []
    lines.append("# 重编号计划报告（dry-run，未移动任何文件）")
    lines.append("")
    lines.append(f"- root: `{ROOT_REL_GLOBAL}/`")
    lines.append(f"- 扫描 .md 文件: **{len(all_rows)}**；需改名: **{n_changed}**；"
                 f"保持不变: **{len(all_rows) - n_changed}**")
    lines.append(f"- README 模式: `{args.readme_mode}`"
                 + ("（README.md 保持原名，遵循 GitHub/mdBook 约定；`00_` 槽位仅用于现有导览页）"
                    if args.readme_mode == "keep" else "（README.md → 00_README.md）"))
    lines.append(f"- 映射表: `{args.out}`")
    lines.append("- 排除: archive/ sources/ book/ tmp/ reports/ quiz* 目录、knowledge_topology/（atlas 生成目录）")
    lines.append("")

    lines.append("## 各层统计")
    lines.append("")
    lines.append("| 层 | 总数 | renumber | prefix_cleanup | collision_resolve | unchanged |")
    lines.append("|---|---:|---:|---:|---:|---:|")
    for layer in sorted(per_layer):
        c = per_layer[layer]
        lines.append(f"| {layer} | {c['total']} | {c.get('renumber',0)} | "
                     f"{c.get('prefix_cleanup',0)} | {c.get('collision_resolve',0)} | {c.get('unchanged',0)} |")
    lines.append("")

    lines.append("## 各目录统计")
    lines.append("")
    lines.append("| 目录 | 总数 | renumber | prefix_cleanup | collision | unchanged |")
    lines.append("|---|---:|---:|---:|---:|---:|")
    for d in sorted(per_dir):
        c = per_dir[d]
        lines.append(f"| `{d}/` | {c['total']} | {c.get('renumber',0)} | "
                     f"{c.get('prefix_cleanup',0)} | {c.get('collision_resolve',0)} | {c.get('unchanged',0)} |")
    lines.append("")

    lines.append("## 序号冲突解决明细")
    lines.append("")
    lines.extend(collisions if collisions else ["- （无）"])
    lines.append("")

    lines.append("## 无序号专题系列文件清单（保持无序号，排在序号文件之后）")
    lines.append("")
    lines.extend(f"- `{p}`" for p in sorted(series_list))
    if not series_list:
        lines.append("- （无）")
    lines.append("")

    lines.append("## 需要人工 review 的疑点")
    lines.append("")
    lines.append("### SUMMARY 顺序与现序号矛盾严重的目录（逆序率 > 30%）")
    lines.append("")
    lines.extend(suspects if suspects else ["- （无）"])
    lines.append("")
    lines.append("### SUMMARY 收录但磁盘缺失的条目")
    lines.append("")
    lines.extend(f"- `{p}`" for p in missing[:50])
    if not missing:
        lines.append("- （无）")
    elif len(missing) > 50:
        lines.append(f"- …… 其余 {len(missing)-50} 条见 CSV/日志")
    lines.append("")

    report_path = REPO_ROOT / args.report if not Path(args.report).is_absolute() else Path(args.report)
    report_path.parent.mkdir(parents=True, exist_ok=True)
    report_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"[plan] scanned={len(all_rows)} changed={n_changed} unchanged={len(all_rows)-n_changed}")
    print(f"[plan] csv    -> {args.out}")
    print(f"[plan] report -> {args.report}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
