#!/usr/bin/env python3
"""
C 类大型目录价值评估脚本

评估 docs/12_research_notes/ 和 docs/rust-ownership-decidability/ 的维护价值
"""

from pathlib import Path
from datetime import datetime, timezone
from collections import defaultdict, Counter
import re

PROJECT_ROOT = Path(".")
CURRENT_DATE = datetime.now(timezone.utc).strftime("%Y-%m-%d")


def analyze_directory(dir_path):
    """分析一个目录中的 Markdown 文件"""
    files = list(dir_path.rglob("*.md"))

    # 排除 archive/
    files = [f for f in files if "archive" not in f.parts and "temp" not in f.parts]

    stats = {
        "total_files": len(files),
        "total_lines": 0,
        "date_distribution": Counter(),
        "size_distribution": {"small(<100)": 0, "medium(100-500)": 0, "large(500-1000)": 0, "xlarge(>1000)": 0},
        "orphan_files": 0,  # 没有最后更新日期的文件
        "recent_files": 0,  # 90 天内更新
        "old_files": 0,     # 超过 180 天未更新
    }

    for f in files:
        try:
            content = f.read_text(encoding="utf-8")
        except Exception:
            continue

        lines = content.count("\n") + 1
        stats["total_lines"] += lines

        # 大小分类
        if lines < 100:
            stats["size_distribution"]["small(<100)"] += 1
        elif lines < 500:
            stats["size_distribution"]["medium(100-500)"] += 1
        elif lines < 1000:
            stats["size_distribution"]["large(500-1000)"] += 1
        else:
            stats["size_distribution"]["xlarge(>1000)"] += 1

        # 查找最后更新日期
        date_match = re.search(r"最后更新.*?([\d]{4}-[\d]{2}-[\d]{2})", content)
        if date_match:
            date_str = date_match.group(1)
            try:
                file_date = datetime.strptime(date_str, "%Y-%m-%d")
                current = datetime.strptime(CURRENT_DATE, "%Y-%m-%d")
                days_old = (current - file_date).days
                if days_old <= 90:
                    stats["recent_files"] += 1
                elif days_old >= 180:
                    stats["old_files"] += 1

                # 按月份统计
                month = date_str[:7]
                stats["date_distribution"][month] += 1
            except ValueError:
                stats["orphan_files"] += 1
        else:
            stats["orphan_files"] += 1

    return stats


def main():
    print("=== C 类大型目录价值评估 ===")
    print(f"评估时间: {CURRENT_DATE}\n")

    dirs = [
        PROJECT_ROOT / "docs" / "research_notes",
        PROJECT_ROOT / "docs" / "rust-ownership-decidability",
    ]

    report_lines = [f"# C 类大型目录价值评估报告\n\n- **评估时间**: {CURRENT_DATE}\n\n"]

    for d in dirs:
        print(f"\n## 目录: {d.relative_to(PROJECT_ROOT)}")
        stats = analyze_directory(d)

        print(f"  总文件数: {stats['total_files']}")
        print(f"  总行数: {stats['total_lines']:,}")
        print(f"  平均每文件行数: {stats['total_lines'] // max(stats['total_files'], 1)}")
        print(f"  近期更新 (≤90天): {stats['recent_files']}")
        print(f"  长期未更新 (≥180天): {stats['old_files']}")
        print(f"  无更新日期: {stats['orphan_files']}")
        print(f"  文件大小分布: {dict(stats['size_distribution'])}")

        top_months = stats["date_distribution"].most_common(5)
        print(f"  最活跃月份: {top_months}")

        # 生成报告
        report_lines.append(f"## {d.relative_to(PROJECT_ROOT)}\n\n")
        report_lines.append(f"| 指标 | 数值 |\n")
        report_lines.append(f"|:---|---:|\n")
        report_lines.append(f"| 总文件数 | {stats['total_files']} |\n")
        report_lines.append(f"| 总行数 | {stats['total_lines']:,} |\n")
        report_lines.append(f"| 平均每文件行数 | {stats['total_lines'] // max(stats['total_files'], 1)} |\n")
        report_lines.append(f"| 近期更新 (≤90天) | {stats['recent_files']} |\n")
        report_lines.append(f"| 长期未更新 (≥180天) | {stats['old_files']} |\n")
        report_lines.append(f"| 无更新日期 | {stats['orphan_files']} |\n")
        report_lines.append(f"| 小型文件 (<100行) | {stats['size_distribution']['small(<100)']} |\n")
        report_lines.append(f"| 中型文件 (100-500行) | {stats['size_distribution']['medium(100-500)']} |\n")
        report_lines.append(f"| 大型文件 (500-1000行) | {stats['size_distribution']['large(500-1000)']} |\n")
        report_lines.append(f"| 超大型文件 (>1000行) | {stats['size_distribution']['xlarge(>1000)']} |\n")
        report_lines.append(f"\n**最活跃月份**: {', '.join(f'{m} ({c})' for m, c in top_months)}\n\n")

    # 建议
    report_lines.append("## 评估建议\n\n")
    report_lines.append("1. **research_notes/**: 研究笔记类文档，内容碎片化程度高。建议评估每篇笔记的引用频率，将高引用内容迁移到 knowledge/ 或 concept/。\n")
    report_lines.append("2. **rust-ownership-decidability/**: 专题目录规模大，需要评估与 concept/ 的重复度。建议提取核心结论到 concept/04_formal/，目录本身作为归档。\n")
    report_lines.append("3. **长期未更新文件**: 对 ≥180 天未更新的文件进行内容有效性复审。\n")
    report_lines.append("4. **无日期文件**: 建议补充 `最后更新` 元数据，便于维护决策。\n")

    # 保存报告
    report_path = PROJECT_ROOT / "reports" / f"C_CLASS_DIRECTORY_AUDIT_{CURRENT_DATE.replace('-', '_')}.md"
    report_path.parent.mkdir(exist_ok=True)
    report_path.write_text("".join(report_lines), encoding="utf-8")
    print(f"\n报告已保存: {report_path}")


if __name__ == "__main__":
    main()
