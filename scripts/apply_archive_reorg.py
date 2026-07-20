#!/usr/bin/env python3
"""
apply_archive_reorg.py

读取 archive 重组映射 CSV，执行 git mv / git rm / stub 创建，并生成迁移日志。

CSV 格式（UTF-8，无 BOM）：
    source_path,target_path,action,note

action 取值：
    move    - 使用 git mv 迁移（默认）
    delete  - 删除冗余/重复文件（需有 note 说明）
    stub    - 在 target_path 创建重定向 stub

用法：
    python scripts/apply_archive_reorg.py --mapping tmp/archive_reorg_map.csv --apply
    python scripts/apply_archive_reorg.py --mapping tmp/archive_reorg_map.csv --dry-run

退出码：
    0 - 成功
    1 - 参数错误或文件不存在
    2 - 迁移过程中出现致命错误
"""

from __future__ import annotations

import argparse
import csv
import os
import shutil
import subprocess
import sys
from datetime import datetime
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
ARCHIVE_ROOT = PROJECT_ROOT / "archive"
LOG_PATH = PROJECT_ROOT / "tmp" / f"archive_reorg_apply_{datetime.now().strftime('%Y_%m_%d_%H%M%S')}.log"


def run_git_mv(src: Path, dst: Path) -> None:
    """使用 git mv 迁移文件或目录，保留 Git 历史。"""
    rel_src = src.relative_to(PROJECT_ROOT)
    rel_dst = dst.relative_to(PROJECT_ROOT)
    subprocess.run(
        ["git", "mv", str(rel_src), str(rel_dst)],
        cwd=PROJECT_ROOT,
        check=True,
    )


def run_git_rm(path: Path) -> None:
    """使用 git rm 删除文件，保留删除历史。"""
    rel_path = path.relative_to(PROJECT_ROOT)
    subprocess.run(
        ["git", "rm", "-r", "-f", str(rel_path)],
        cwd=PROJECT_ROOT,
        check=True,
    )


def ensure_parent(path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)


def create_stub(target_path: Path, canonical_path: str, title: str = "") -> None:
    """创建符合 AGENTS.md 规范的重定向 stub。"""
    ensure_parent(target_path)
    title_line = f"# {title}" if title else "# 已归档内容"
    body = (
        f"{title_line}\n\n"
        f"> **权威来源**: 本文件为归档重定向 stub。\n"
        f"> 完整历史内容请见：[`{canonical_path}`](../../{canonical_path})\n\n"
        f"> 根据 AGENTS.md §2 Canonical 规则，本主题已在 `concept/` 或当前活跃目录中维护；\n"
        f"> 此处仅保留历史归档入口。\n"
    )
    target_path.write_text(body, encoding="utf-8", newline="\n")


def verify_inside_archive(path: Path) -> bool:
    """确认路径在 archive/ 下。"""
    try:
        path.relative_to(ARCHIVE_ROOT)
        return True
    except ValueError:
        return False


def apply_row(row: dict, dry_run: bool) -> dict:
    """处理单行映射。返回包含状态的字典。"""
    source = PROJECT_ROOT / row["source_path"].strip()
    target = PROJECT_ROOT / row["target_path"].strip()
    action = row["action"].strip().lower()
    note = row.get("note", "").strip()

    result = {
        "source": str(source.relative_to(PROJECT_ROOT)),
        "target": str(target.relative_to(PROJECT_ROOT)),
        "action": action,
        "note": note,
        "status": "pending",
        "error": "",
    }

    if not source.exists() and action != "stub":
        result["status"] = "skipped"
        result["error"] = "source not found"
        return result

    if action == "move":
        if not verify_inside_archive(source) or not verify_inside_archive(target):
            result["status"] = "error"
            result["error"] = "source or target not inside archive/"
            return result
        if dry_run:
            result["status"] = "dry-run"
        else:
            try:
                ensure_parent(target)
                run_git_mv(source, target)
                result["status"] = "moved"
            except subprocess.CalledProcessError as e:
                result["status"] = "error"
                result["error"] = f"git mv failed: {e}"

    elif action == "delete":
        if not verify_inside_archive(source):
            result["status"] = "error"
            result["error"] = "source not inside archive/"
            return result
        if dry_run:
            result["status"] = "dry-run-delete"
        else:
            try:
                run_git_rm(source)
                result["status"] = "deleted"
            except subprocess.CalledProcessError as e:
                result["status"] = "error"
                result["error"] = f"git rm failed: {e}"

    elif action == "stub":
        canonical = row["source_path"].strip()  # 对于 stub，source_path 存的是 canonical 相对路径
        title = row.get("title", "已归档内容").strip()
        if dry_run:
            result["status"] = "dry-run-stub"
        else:
            try:
                create_stub(target, canonical, title)
                result["status"] = "stub-created"
            except Exception as e:
                result["status"] = "error"
                result["error"] = f"stub creation failed: {e}"
    else:
        result["status"] = "error"
        result["error"] = f"unknown action: {action}"

    return result


def main() -> int:
    parser = argparse.ArgumentParser(description="Apply archive reorganization mapping.")
    parser.add_argument("--mapping", required=True, help="Path to CSV mapping file.")
    parser.add_argument("--apply", action="store_true", help="Actually apply changes (default: dry-run).")
    parser.add_argument("--log", default=str(LOG_PATH), help="Path to log file.")
    args = parser.parse_args()

    mapping_path = Path(args.mapping).resolve()
    if not mapping_path.exists():
        print(f"ERROR: mapping file not found: {mapping_path}", file=sys.stderr)
        return 1

    log_path = Path(args.log).resolve()
    log_path.parent.mkdir(parents=True, exist_ok=True)

    # 检查 git 状态是否干净
    git_status = subprocess.run(
        ["git", "status", "--short"],
        cwd=PROJECT_ROOT,
        capture_output=True,
        text=True,
        check=True,
    )
    if git_status.stdout.strip() and args.apply:
        print("WARNING: working tree is not clean. Uncommitted changes may be mixed with reorg.", file=sys.stderr)
        # 不强制退出，因为用户可能已有意保存了冻结提示的修改

    mode = "APPLY" if args.apply else "DRY-RUN"
    print(f"=== Archive Reorganization: {mode} ===")
    print(f"Mapping: {mapping_path}")
    print(f"Log: {log_path}\n")

    log_lines = [f"# Archive Reorganization Log ({mode})\n\n"]
    log_lines.append(f"- Time: {datetime.now().isoformat()}\n")
    log_lines.append(f"- Mapping: {mapping_path}\n\n")
    log_lines.append("| # | source | target | action | status | note |\n")
    log_lines.append("|---|--------|--------|--------|--------|------|\n")

    errors = 0
    with mapping_path.open(encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for idx, row in enumerate(reader, 1):
            result = apply_row(row, dry_run=not args.apply)
            log_lines.append(
                f"| {idx} | `{result['source']}` | `{result['target']}` | {result['action']} | {result['status']} | {result['note']} |\n"
            )
            if result["status"] == "error":
                errors += 1
                print(f"[ERROR] {result['source']} -> {result['target']}: {result['error']}", file=sys.stderr)
            else:
                print(f"[{result['status']}] {result['source']} -> {result['target']}")

    log_lines.append(f"\n## Summary\n\n- Total rows: {idx}\n- Errors: {errors}\n")
    log_path.write_text("".join(log_lines), encoding="utf-8", newline="\n")

    print(f"\n=== Done ({mode}) ===")
    print(f"Errors: {errors}")
    print(f"Log saved: {log_path}")
    return 2 if errors > 0 else 0


if __name__ == "__main__":
    sys.exit(main())
