#!/usr/bin/env python3
"""
季度僵尸内容清理机制 (Quarterly Zombie Content Cleanup)

功能:
1. 扫描 concept/、knowledge/、docs/ 目录下的 .md 文件
2. 检测 90 天内无内部链接指向、无 git 提交的文件
3. 标记"僵尸内容"供人工审查
4. 生成季度清理报告

用法:
    python scripts/quarterly_zombie_cleanup.py [--mark] [--days 90]

配置:
    ZOMBIE_DAYS: 多少天无活动即视为僵尸（默认 90）
    EXCLUDE_DIRS: 排除的目录（archive/、00_meta/ 等）
"""

import argparse
import datetime
import os
import re
import subprocess
from pathlib import Path

# 配置
ZOMBIE_DAYS = 90
EXCLUDE_DIRS = {"archive", "00_meta", "deprecated", "sandbox"}
TARGET_DIRS = [Path("concept"), Path("knowledge"), Path("docs")]
REPORT_PATH = Path("reports/quarterly_zombie_report.md")


def get_git_last_commit(path: Path) -> datetime.datetime | None:
    """获取文件的最后提交时间"""
    try:
        result = subprocess.run(
            ["git", "log", "-1", "--format=%ci", str(path)],
            capture_output=True,
            text=True,
            check=True,
        )
        if result.stdout.strip():
            return datetime.datetime.fromisoformat(result.stdout.strip().replace(" ", "T").replace(" +", "+").split("+")[0])
    except (subprocess.CalledProcessError, ValueError):
        pass
    return None


def get_internal_link_count(path: Path, all_files: set[str]) -> int:
    """统计文件被多少其他文件链接"""
    try:
        content = path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return 0

    # 提取文件中的内部链接
    links = re.findall(r'\]\(([^)]+)\)', content)
    internal_links = 0
    for link in links:
        # 只计数指向 .md 文件的链接
        if link.endswith(".md") or "/" in link:
            internal_links += 1
    return internal_links


def find_zombies(days: int = ZOMBIE_DAYS) -> list[dict]:
    """查找僵尸内容"""
    cutoff = datetime.datetime.now() - datetime.timedelta(days=days)
    zombies = []

    for target_dir in TARGET_DIRS:
        if not target_dir.exists():
            continue
        for md_file in target_dir.rglob("*.md"):
            # 排除 archive/ 等目录
            if any(part in EXCLUDE_DIRS for part in md_file.parts):
                continue

            # 检查最后提交时间
            last_commit = get_git_last_commit(md_file)
            if last_commit and last_commit > cutoff:
                continue  # 近期有提交，不是僵尸

            # 检查内部链接数
            link_count = get_internal_link_count(md_file, set())
            if link_count > 2:
                continue  # 有较多内部链接，不是僵尸

            zombies.append({
                "path": md_file,
                "last_commit": last_commit,
                "link_count": link_count,
                "lines": len(md_file.read_text(encoding="utf-8").splitlines()),
            })

    # 按最后提交时间排序（最老的在前）
    zombies.sort(key=lambda x: x["last_commit"] or datetime.datetime.min)
    return zombies


def generate_report(zombies: list[dict], days: int) -> str:
    """生成报告"""
    now = datetime.datetime.now().strftime("%Y-%m-%d")
    report = f"""# 季度僵尸内容清理报告

> **生成日期**: {now}
> **僵尸定义**: {days} 天内无 git 提交且内部链接 ≤2 的文件
> **扫描范围**: concept/ · knowledge/ · docs/

## 统计摘要

| 指标 | 数值 |
|:---|---:|
| 僵尸文件数 | {len(zombies)} |
| 预估总影响 | {sum(z['lines'] for z in zombies)} 行 |

## 僵尸文件清单

| 路径 | 最后提交 | 内部链接 | 行数 | 建议操作 |
|:---|:---|---:|---:|:---|
"""

    for z in zombies[:50]:  # 最多显示 50 个
        commit_str = z["last_commit"].strftime("%Y-%m-%d") if z["last_commit"] else "未知"
        report += f"| {z['path']} | {commit_str} | {z['link_count']} | {z['lines']} | 人工审查 |\n"

    if len(zombies) > 50:
        report += f"\n> 还有 {len(zombies) - 50} 个文件未显示。\n"

    report += """
## 建议操作流程

1. **高优先级**（最老的 10 个）：人工审查，决定是否归档/删除/合并
2. **中优先级**（链接数 = 0 的）：检查是否为孤立文件，考虑删除
3. **低优先级**（链接数 = 1-2 的）：检查链接是否来自核心文件，考虑合并内容

## 自动化标记

运行以下命令为僵尸文件添加标记：

```bash
python scripts/quarterly_zombie_cleanup.py --mark
```

---

> **维护者**: Rust 学习项目团队
> **下次清理**: 本季度结束后（~90 天后）
"""

    return report


def mark_zombies(zombies: list[dict]) -> int:
    """为僵尸文件添加标记"""
    marked = 0
    for z in zombies:
        path = z["path"]
        try:
            content = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue

        if "[季度僵尸内容审查]" in content:
            continue

        # 在文件头部添加标记
        marker = f"> ⚠️ **[季度僵尸内容审查]** 本文件 {ZOMBIE_DAYS}+ 天无更新且内部链接较少。建议人工审查是否需要归档或合并。\n>\n"

        lines = content.splitlines()
        insert_idx = 1
        for i, line in enumerate(lines[1:], start=1):
            if line.strip() == "" or not line.strip().startswith(">"):
                insert_idx = i
                break

        new_lines = lines[:insert_idx] + [marker.rstrip()] + lines[insert_idx:]
        path.write_text("\n".join(new_lines), encoding="utf-8")
        marked += 1

    return marked


def main():
    parser = argparse.ArgumentParser(description="季度僵尸内容清理机制")
    parser.add_argument("--mark", action="store_true", help="为僵尸文件添加标记")
    parser.add_argument("--days", type=int, default=ZOMBIE_DAYS, help=f"僵尸阈值天数（默认 {ZOMBIE_DAYS}）")
    args = parser.parse_args()

    print(f"🔍 扫描僵尸内容（阈值: {args.days} 天）...")
    zombies = find_zombies(days=args.days)
    print(f"  发现 {len(zombies)} 个僵尸文件")

    if args.mark:
        marked = mark_zombies(zombies)
        print(f"  已标记 {marked} 个文件")

    # 生成报告
    report = generate_report(zombies, args.days)
    REPORT_PATH.write_text(report, encoding="utf-8")
    print(f"📄 报告已生成: {REPORT_PATH}")


if __name__ == "__main__":
    main()
