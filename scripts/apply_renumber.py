#!/usr/bin/env python3
"""apply_renumber.py — 按映射表执行重编号 + 全库链接重写（默认 dry-run）。

框架开发阶段产物：**默认 dry-run，不移动任何文件、不改写任何仓库文件**；
只有显式 `--apply` 才执行 `os.rename` 与文件改写。脚本**不使用任何 git 命令**。

功能：
1. 按 CSV 映射（old_path,new_path,reason,order_in_dir）移动文件，使用
   `os.rename` 两阶段（临时名 -> 目标名）处理同目录链式/环状重命名。
2. 全库链接重写：扫描 .md/.py/.json/.yaml/.yml/.toml（跳过 book/ reports/
   archive/ tmp/ vendor/ target/ .git/），对每个 old_path→new_path：
   - Markdown 链接/图片：按链接所在文件的**移动前**路径解析为仓库绝对路径，
     命中映射后用链接所在文件的**移动后**路径重算相对路径；
   - 行内反引号路径、纯文本路径引用（含 `concept/...` 仓库相对形式、绝对
     路径形式、同目录相对形式）同样重写。
3. 数据文件同步（结构化 JSON 更新 + 文本兜底）：
   - `concept_kb.json`（绝对路径 path 字段）
   - `concept/00_meta/kg_data.json` / `kg_data_v3.json` / `kg_index.json`
     （ex:path / path / id 字段，含去序号归一化兜底匹配）
   - `concept/00_meta/taxonomy.yaml` 仅含目录前缀，目录不改名时通常无需动
     （走通用文本兜底）。
4. SUMMARY.md 重新生成：按映射替换路径（保留层级与标题文本），输出到
   `tmp/renumber/SUMMARY.new.md` 供人工 diff，不直接覆盖（--apply 时
   SUMMARY.md 本身也会被通用 Markdown 链接重写更新）。
5. 执行日志 `tmp/renumber/apply_log.md`：移动数、重写文件数/处数、
   未能解析的引用清单（人工 review）。

用法：
    # dry-run（默认）
    python scripts/apply_renumber.py --mapping tmp/renumber/mapping_concept.csv --scope concept
    # 实际执行
    python scripts/apply_renumber.py --mapping tmp/renumber/mapping_concept.csv --scope concept --apply
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import posixpath
import re
import sys
import uuid
from collections import defaultdict
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
DEFAULT_REPO_ROOT = SCRIPT_DIR.parent

SKIP_DIR_NAMES = {"book", "reports", "archive", "tmp", "vendor", "target", ".git",
                  "node_modules", "__pycache__"}
SCAN_EXTS = {".md", ".py", ".json", ".yaml", ".yml", ".toml"}
SUMMARY_LINK_RE = re.compile(r"^(\s*- \[)([^\]]*)(\]\()([^)]+)(\).*)$")
MD_LINK_RE = re.compile(r"(!?\[[^\]]*\]\()([^)\n]+)(\))")
SCHEME_RE = re.compile(r"^[a-zA-Z][a-zA-Z0-9+.\-]*:")
STRIP_NUM_RE = re.compile(r"(^|[/\\])\d+_")


def to_posix(p: str) -> str:
    return p.replace("\\", "/")


def strip_numbers(path: str) -> str:
    """去除每级路径组件的 NN_ 前缀（用于数据文件陈旧序号的归一化匹配）。"""
    return STRIP_NUM_RE.sub(r"\1", path)


def load_mapping(mapping_path: Path, scope: str) -> tuple[dict[str, str], list[dict]]:
    """加载映射，按 scope 过滤，返回 (moves{old:new(仅改名)}, 全部行)。"""
    moves: dict[str, str] = {}
    rows: list[dict] = []
    scope = scope.strip("/")
    with mapping_path.open(encoding="utf-8", newline="") as fh:
        for row in csv.DictReader(fh):
            old = to_posix(row["old_path"].strip())
            new = to_posix(row["new_path"].strip())
            if scope and not old.startswith(scope + "/"):
                continue
            rows.append(row)
            if old != new:
                if new in moves.values():
                    print(f"ERROR: 映射目标重复: {new}", file=sys.stderr)
                    raise SystemExit(2)
                moves[old] = new
    return moves, rows


def scan_files(repo_root: Path) -> list[str]:
    """扫描需参与链接重写的文件（相对仓库根 posix），os.walk 剪枝跳过目录。"""
    out: list[str] = []
    for dirpath, dirnames, filenames in os.walk(repo_root):
        dirnames[:] = [d for d in dirnames if d not in SKIP_DIR_NAMES]
        for name in filenames:
            fp = Path(dirpath) / name
            if fp.suffix.lower() in SCAN_EXTS:
                out.append(to_posix(str(fp.relative_to(repo_root))))
    return sorted(out)


class Rewriter:
    def __init__(self, repo_root: Path, moves: dict[str, str], dry_run: bool):
        self.repo_root = repo_root
        self.moves = moves
        self.dry_run = dry_run
        # 引用方文件的新位置（不在映射中的文件位置不变）
        self.file_new_loc: dict[str, str] = {}
        # 精确匹配表：数据文件/文本中出现的各种路径形式 -> 新形式
        self.exact_map: dict[str, str] = {}
        # 去序号归一化表（兼容数据文件中的陈旧序号）：stripped(form) -> 新形式
        self.stripped_map: dict[str, str] = {}
        for old, new in moves.items():
            forms_o, forms_n = self.all_forms(old), self.all_forms(new)
            for so, sn in zip(forms_o, forms_n):
                self.exact_map.setdefault(so, sn)
                self.stripped_map.setdefault(strip_numbers(so), sn)
        # 统计
        self.file_changes: dict[str, int] = defaultdict(int)
        self.unresolved: list[tuple[str, str]] = []  # (引用方旧路径, 原始目标)
        self.all_md_old: set[str] = set()

    def all_forms(self, rel: str) -> list[str]:
        """一个仓库相对路径可能出现的所有书写形式（顺序与 new 一一对应）。"""
        forms = [rel, "concept:" + rel]
        if rel.startswith("concept/"):
            cr = rel[len("concept/"):]
            forms += [cr, "concept:" + cr]
        forms += self.abs_forms(rel)
        return forms

    def abs_forms(self, rel: str) -> list[str]:
        root = str(self.repo_root)
        variants = {root, root[0].upper() + root[1:], root[0].lower() + root[1:]}
        forms = []
        for r in variants:
            forms.append(r.replace("/", "\\") + "\\" + rel.replace("/", "\\"))
            forms.append(r.replace("\\", "/") + "/" + rel)
        return list(dict.fromkeys(forms))

    def text_forms(self, old: str, new: str, fo: str, fn: str, is_md: bool) -> list[tuple[str, str]]:
        """为映射条目生成 (搜索串, 替换串) 列表（相对引用方文件位置）。"""
        forms: list[tuple[str, str]] = [(old, new)]  # 仓库相对形式
        for so, sn in zip(self.abs_forms(old), self.abs_forms(new)):
            forms.append((so, sn))
        if old.startswith("concept/"):
            forms.append((old[len("concept/"):], new[len("concept/"):]))  # concept 相对形式
        if is_md:
            ro = posixpath.relpath(old, posixpath.dirname(fo) or ".")
            rn = posixpath.relpath(new, posixpath.dirname(fn) or ".")
            forms.append((ro, rn))
            if not ro.startswith(".."):
                forms.append(("./" + ro, "./" + rn))
        # 去重并保持顺序
        seen: set[str] = set()
        uniq: list[tuple[str, str]] = []
        for s, r in forms:
            if s != r and s not in seen:
                seen.add(s)
                uniq.append((s, r))
        return uniq

    @staticmethod
    def _sub_bounded(text: str, search: str, replace: str) -> tuple[str, int]:
        pat = re.compile(r"(?<![\w/\\.\-])" + re.escape(search) + r"(?![\w/\\.\-])")
        return pat.subn(replace, text)

    # ---------- Markdown 链接 ----------
    def rewrite_md_links(self, text: str, fo: str, fn: str) -> str:
        dir_o = posixpath.dirname(fo) or "."
        dir_n = posixpath.dirname(fn) or "."

        def repl(m: re.Match) -> str:
            prefix, raw, suffix = m.group(1), m.group(2), m.group(3)
            target = raw.strip()
            wrap = ""
            if target.startswith("<") and target.endswith(">"):
                target, wrap = target[1:-1], "<>"
            title = ""
            mt = re.match(r"^(\S+)(\s+\"[^\"]*\")$", target)
            if mt:
                target, title = mt.group(1), mt.group(2)
            if SCHEME_RE.match(target) or target.startswith(("#", "/")):
                return m.group(0)
            path, _, anchor = target.partition("#")
            if not path:
                return m.group(0)
            resolved = posixpath.normpath(posixpath.join(dir_o, path))
            if resolved in self.moves:
                new_target = posixpath.relpath(self.moves[resolved], dir_n)
                if anchor:
                    new_target += "#" + anchor
                inner = f"<{new_target}>" if wrap else new_target
                self.file_changes[fo] += 1
                return f"{prefix}{inner}{title}{suffix}"
            if path.endswith(".md") and resolved not in self.all_md_old \
                    and not any(resolved.startswith(s + "/") for s in SKIP_DIR_NAMES) \
                    and len(self.unresolved) < 20000:
                self.unresolved.append((fo, target))
            return m.group(0)

        return MD_LINK_RE.sub(repl, text)

    # ---------- 结构化 JSON 更新 ----------
    def rewrite_json_value(self, v) -> str:
        if not isinstance(v, str) or ".md" not in v:
            return v
        hit = self.exact_map.get(v)
        if hit is not None:
            return hit
        # 去序号归一化兼容（数据文件中的陈旧序号，如 kg_index 的 03_bloom_taxonomy.md）
        return self.stripped_map.get(strip_numbers(v), v)

    def rewrite_json_obj(self, obj):
        if isinstance(obj, dict):
            return {k: self.rewrite_json_obj(v) for k, v in obj.items()}
        if isinstance(obj, list):
            return [self.rewrite_json_obj(v) for v in obj]
        if isinstance(obj, str):
            return self.rewrite_json_value(obj)
        return obj


def regenerate_summary(repo_root: Path, scope: str, moves: dict[str, str], out_path: Path) -> int:
    """按映射重写 <scope>/SUMMARY.md 的链接路径，输出到 out_path。返回替换处数。"""
    summary = repo_root / scope / "SUMMARY.md"
    if not summary.exists():
        return 0
    count = 0
    lines_out: list[str] = []
    for line in summary.read_text(encoding="utf-8").splitlines():
        m = SUMMARY_LINK_RE.match(line)
        if m:
            target = m.group(4).strip()
            if not SCHEME_RE.match(target) and target.endswith(".md"):
                full = posixpath.normpath(posixpath.join(scope, target.split("#")[0]))
                if full in moves:
                    anchor = "#" + target.split("#", 1)[1] if "#" in target else ""
                    new_rel = posixpath.relpath(moves[full], scope)
                    line = f"{m.group(1)}{m.group(2)}{m.group(3)}{new_rel}{anchor}{m.group(5)}"
                    count += 1
        lines_out.append(line)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text("\n".join(lines_out) + "\n", encoding="utf-8")
    return count


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--mapping", required=True, help="plan_renumber.py 生成的映射 CSV")
    ap.add_argument("--scope", default="concept", help="只处理映射中该前缀的行（空串=全部）")
    ap.add_argument("--dry-run", dest="dry_run", action="store_true", default=True)
    ap.add_argument("--apply", dest="dry_run", action="store_false",
                    help="实际执行移动与改写（默认 dry-run）")
    ap.add_argument("--repo-root", default=str(DEFAULT_REPO_ROOT))
    ap.add_argument("--log", default="tmp/renumber/apply_log.md")
    ap.add_argument("--summary-out", default="tmp/renumber/SUMMARY.new.md")
    args = ap.parse_args()

    repo_root = Path(args.repo_root).resolve()
    mapping_path = Path(args.mapping)
    if not mapping_path.is_absolute():
        mapping_path = repo_root / mapping_path
    moves, rows = load_mapping(mapping_path, args.scope)
    mode = "DRY-RUN" if args.dry_run else "APPLY"
    print(f"[apply] mode={mode} scope={args.scope!r} moves={len(moves)} rows={len(rows)}")

    # ---- 校验：目标是否与“不参与移动且已存在”的文件冲突 ----
    problems = []
    for old, new in moves.items():
        if not (repo_root / old).exists():
            problems.append(f"源文件不存在: {old}")
        tgt = repo_root / new
        if tgt.exists() and new not in moves:
            problems.append(f"目标已存在且不会被移走: {new} (来自 {old})")
    if problems:
        for p in problems[:20]:
            print("ERROR:", p, file=sys.stderr)
        print(f"共 {len(problems)} 个映射问题，终止。", file=sys.stderr)
        return 2

    rw = Rewriter(repo_root, moves, args.dry_run)
    scanned = scan_files(repo_root)
    rw.all_md_old = {f for f in scanned if f.endswith(".md")}
    for f in scanned:
        rw.file_new_loc[f] = moves.get(f, f)

    # ---- 阶段 1：移动文件（两阶段，仅 --apply） ----
    moved = 0
    if not args.dry_run:
        tmp_tag = f".renum_tmp_{uuid.uuid4().hex[:8]}"
        staged: list[tuple[str, str, str]] = []  # (old, tmp, new)
        for old, new in moves.items():
            tmp = old + tmp_tag
            (repo_root / old).rename(repo_root / tmp)
            staged.append((old, tmp, new))
        for old, tmp, new in staged:
            (repo_root / tmp).rename(repo_root / new)
            moved += 1
        print(f"[apply] moved {moved} files (two-phase os.rename)")

    # ---- 阶段 2：SUMMARY 重新生成（只写 tmp，供人工 diff） ----
    # 必须在通用链接重写之前读取原始 SUMMARY.md，否则 --apply 时磁盘上的
    # SUMMARY.md 已被就地重写，替换计数会失真。
    summary_repl = 0
    summary_out = Path(args.summary_out)
    if not summary_out.is_absolute():
        summary_out = repo_root / summary_out
    if args.scope:
        summary_repl = regenerate_summary(repo_root, args.scope.strip("/"), moves, summary_out)

    # ---- 阶段 3：链接重写 ----
    rewritten_files = 0
    total_repl = 0
    json_files = {"concept_kb.json", "kg_data.json", "kg_data_v3.json", "kg_index.json"}
    for fo in scanned:
        fn = rw.file_new_loc[fo]
        disk_path = repo_root / (fo if args.dry_run else fn)
        if not disk_path.exists():
            continue
        try:
            text = disk_path.read_text(encoding="utf-8")
        except (UnicodeDecodeError, OSError):
            continue
        orig = text
        is_md = fo.endswith(".md")
        before = rw.file_changes.get(fo, 0)
        if is_md:
            text = rw.rewrite_md_links(text, fo, fn)
        # 文本兜底（仓库相对/绝对/concept相对/同目录相对 形式）
        for old, new in sorted(moves.items(), key=lambda kv: -len(kv[0])):
            # 快速跳过：basename 与 concept/ 前缀都不在文本中
            base = posixpath.basename(old)
            if base not in text and "concept/" not in text:
                continue
            for s, r in rw.text_forms(old, new, fo, fn, is_md):
                if s in text:
                    text, n = rw._sub_bounded(text, s, r)
                    if n:
                        rw.file_changes[fo] += n
        # 结构化 JSON 兜底（陈旧序号归一化等）
        if posixpath.basename(fo) in json_files:
            try:
                obj = json.loads(text)
                obj2 = rw.rewrite_json_obj(obj)
                if obj2 != obj:
                    text = json.dumps(obj2, ensure_ascii=False, indent=2)
                    rw.file_changes[fo] += 1
            except json.JSONDecodeError:
                pass
        if text != orig:
            rewritten_files += 1
            total_repl += rw.file_changes.get(fo, 0) - before
            if not args.dry_run:
                disk_path.write_text(text, encoding="utf-8")

    # ---- 阶段 4：日志 ----
    unresolved = list(dict.fromkeys(rw.unresolved))
    log_lines = [
        f"# 重编号执行日志（{mode}）",
        "",
        f"- 映射: `{args.mapping}`（scope=`{args.scope or '(全部)'}`，{len(rows)} 行）",
        f"- 文件移动: **{moved if not args.dry_run else len(moves)}** "
        + ("（已执行）" if not args.dry_run else "（dry-run：将移动，未执行）"),
        f"- 链接/引用重写: **{rewritten_files}** 个文件，约 **{total_repl}** 处",
        f"- SUMMARY 重写: **{summary_repl}** 处 → `{args.summary_out}`（供人工 diff，未覆盖原文件）",
        f"- 未能解析的引用: **{len(unresolved)}** 处（需人工 review；多为映射前就存在的死链）",
        "",
        "## 各文件重写处数（Top 50）",
        "",
        "| 文件（移动前路径） | 处数 |",
        "|---|---:|",
    ]
    for f, n in sorted(rw.file_changes.items(), key=lambda kv: -kv[1])[:50]:
        if n:
            log_lines.append(f"| `{f}` | {n} |")
    log_lines += ["", "## 未能解析的引用清单（最多 200 条）", ""]
    log_lines += [f"- `{fo}` → `{t}`" for fo, t in unresolved[:200]] or ["- （无）"]
    if len(unresolved) > 200:
        log_lines.append(f"- …… 其余 {len(unresolved) - 200} 条省略")
    log_path = Path(args.log)
    if not log_path.is_absolute():
        log_path = repo_root / log_path
    log_path.parent.mkdir(parents=True, exist_ok=True)
    log_path.write_text("\n".join(log_lines) + "\n", encoding="utf-8")

    print(f"[apply] rewritten_files={rewritten_files} replacements~={total_repl} "
          f"summary_repl={summary_repl} unresolved={len(unresolved)}")
    print(f"[apply] log -> {args.log}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
