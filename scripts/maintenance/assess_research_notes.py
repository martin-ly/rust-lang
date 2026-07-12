#!/usr/bin/env python3
"""
评估 docs/12_research_notes/ 中 C 类文件的价值，输出迁移/归档/保留建议。

评估维度：
1. 最后更新日期（越旧越倾向归档）
2. 被 concept/ / knowledge/ / docs/（非 research_notes）引用次数
3. 文件大小与内容密度
4. 标题/主题是否已在 concept/ 或 knowledge/ 有对应覆盖
"""

from __future__ import annotations

import re
from collections import defaultdict
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RESEARCH_NOTES = ROOT / "docs" / "research_notes"
ACTIVE_DIRS = [
    ROOT / "concept",
    ROOT / "knowledge",
    ROOT / "docs" / "00_meta",
    ROOT / "docs" / "01_learning",
    ROOT / "docs" / "02_reference",
    ROOT / "docs" / "03_guides",
    ROOT / "docs" / "05_guides",
    ROOT / "docs" / "06_toolchain",
    ROOT / "docs" / "07_project",
]


def parse_last_update(text: str) -> datetime | None:
    """从 Markdown 元数据中提取最后更新日期。"""
    patterns = [
        r"\*\*最后更新\*\*[:：]\s*(\d{4}-\d{2}-\d{2})",
        r"最后更新[:：]\s*(\d{4}-\d{2}-\d{2})",
        r"updated[:：]\s*(\d{4}-\d{2}-\d{2})",
    ]
    for pat in patterns:
        m = re.search(pat, text)
        if m:
            return datetime.strptime(m.group(1), "%Y-%m-%d").replace(tzinfo=timezone.utc)
    return None


def get_title(text: str) -> str:
    """提取第一个 # 标题。"""
    m = re.search(r"^#\s+(.+)$", text, re.MULTILINE)
    return m.group(1).strip() if m else "(无标题)"


def collect_references() -> dict[Path, list[Path]]:
    """
    扫描 ACTIVE_DIRS 中的 Markdown 文件，记录它们对 research_notes/ 下文件的引用。
    返回：research_notes 文件 -> 引用它的 active 文件列表
    """
    refs: dict[Path, list[Path]] = defaultdict(list)

    for base in ACTIVE_DIRS:
        if not base.exists():
            continue
        for path in base.rglob("*.md"):
            text = path.read_text(encoding="utf-8", errors="ignore")
            for note in RESEARCH_NOTES.rglob("*.md"):
                rel = note.relative_to(ROOT).as_posix()
                # 匹配相对路径引用，如 ../research_notes/10_xxx.md 或 ./10_xxx.md
                escaped = re.escape(rel)
                if re.search(rf"\]\([^)]*{escaped}[)#]?", text):
                    refs[note].append(path)

    return refs


def assess_file(path: Path, refs: dict[Path, list[Path]]) -> dict:
    text = path.read_text(encoding="utf-8", errors="ignore")
    last_update = parse_last_update(text)
    age_days = (
        (datetime.now(timezone.utc) - last_update).days
        if last_update
        else None
    )
    ref_count = len(refs.get(path, []))
    line_count = len(text.splitlines())
    code_blocks = len(re.findall(r"```(?:rust)?", text))
    external_links = len(re.findall(r"https?://", text))

    # 简单规则评分
    score = 0
    if ref_count > 0:
        score += 20 * min(ref_count, 5)
    if age_days is not None and age_days <= 90:
        score += 15
    elif age_days is not None and age_days <= 180:
        score += 5
    if line_count >= 300:
        score += 10
    if code_blocks >= 3:
        score += 10
    if external_links >= 5:
        score += 5

    # 决策建议
    if ref_count >= 2:
        action = "保留或迁移到 knowledge/"
    elif score >= 30:
        action = "保留，定期复审"
    elif age_days is not None and age_days > 120 and ref_count == 0:
        action = "归档候选"
    elif line_count < 100 and ref_count == 0:
        action = "合并或删除候选"
    else:
        action = "需人工复审"

    return {
        "path": path,
        "title": get_title(text),
        "last_update": last_update,
        "age_days": age_days,
        "ref_count": ref_count,
        "line_count": line_count,
        "code_blocks": code_blocks,
        "external_links": external_links,
        "score": score,
        "action": action,
    }


def main() -> int:
    print("=== docs/12_research_notes/ C 类价值评估 ===\n")

    refs = collect_references()
    assessments = []

    for path in sorted(RESEARCH_NOTES.rglob("*.md")):
        assessments.append(assess_file(path, refs))

    # 按建议分类统计
    by_action: dict[str, list[dict]] = defaultdict(list)
    for a in assessments:
        by_action[a["action"]].append(a)

    print("## 建议分类统计\n")
    for action, items in sorted(by_action.items(), key=lambda x: -len(x[1])):
        print(f"- {action}: {len(items)} 个文件")

    print("\n## 高优先级处理建议\n")
    print("### 应迁移/保留的高引用文件（被 active 文档引用 ≥2 次）\n")
    high_ref = [a for a in assessments if a["ref_count"] >= 2]
    for a in sorted(high_ref, key=lambda x: -x["ref_count"])[:20]:
        print(
            f"- `{a['path'].relative_to(ROOT).as_posix()}` | "
            f"引用 {a['ref_count']} 次 | {a['title'][:50]}"
        )

    print("\n### 归档候选（>120 天未更新且未被引用）\n")
    archive_candidates = [
        a for a in assessments
        if a["age_days"] is not None and a["age_days"] > 120 and a["ref_count"] == 0
    ]
    for a in sorted(archive_candidates, key=lambda x: -x["age_days"])[:20]:
        print(
            f"- `{a['path'].relative_to(ROOT).as_posix()}` | "
            f"{a['age_days']} 天未更新 | {a['title'][:50]}"
        )

    print("\n### 合并/删除候选（<100 行且未被引用）\n")
    merge_candidates = [
        a for a in assessments if a["line_count"] < 100 and a["ref_count"] == 0
    ]
    for a in merge_candidates[:20]:
        print(
            f"- `{a['path'].relative_to(ROOT).as_posix()}` | "
            f"{a['line_count']} 行 | {a['title'][:50]}"
        )

    # 保存完整报告
    report_path = ROOT / "reports" / "RESEARCH_NOTES_C_CLASS_ASSESSMENT_2026_06_25.md"
    with report_path.open("w", encoding="utf-8") as f:
        f.write("# docs/12_research_notes/ C 类价值评估报告\n\n")
        f.write(f"- **评估时间**: 2026-06-25\n")
        f.write(f"- **总文件数**: {len(assessments)}\n\n")
        f.write("## 建议分类统计\n\n")
        for action, items in sorted(by_action.items(), key=lambda x: -len(x[1])):
            f.write(f"- **{action}**: {len(items)} 个\n")
        f.write("\n## 完整清单\n\n")
        f.write("| 文件 | 标题 | 最后更新 | 天龄 | 引用数 | 行数 | 建议 |\n")
        f.write("|---|---|---|---|---|---|---|\n")
        for a in sorted(assessments, key=lambda x: -x["score"]):
            lu = a["last_update"].strftime("%Y-%m-%d") if a["last_update"] else "未知"
            age = str(a["age_days"]) if a["age_days"] is not None else "未知"
            f.write(
                f"| `{a['path'].relative_to(RESEARCH_NOTES).as_posix()}` | "
                f"{a['title'][:40]} | {lu} | {age} | {a['ref_count']} | "
                f"{a['line_count']} | {a['action']} |\n"
            )

    print(f"\n完整报告已保存: {report_path.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
