#!/usr/bin/env python3
"""
为 archive/ 目录下的 md 文件统一添加归档头部模板。
跳过已有明确归档标记的文件。
"""

import os
import re
from datetime import datetime
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent.parent
ARCHIVE_DIR = PROJECT_ROOT / "archive"
ARCHIVE_DATE = datetime.now().strftime("%Y-%m-%d")

# 归档原因映射（基于子目录）
REASON_MAP = {
    "2026": "历史计划与报告归档",
    "backup_from_docs": "从 docs 目录迁移备份",
    "deprecated": "方案废弃，不再维护",
    "reports": "历史审计报告归档",
    "temp": "临时文件归档",
    "verification_reports": "验证报告归档",
}

# 已有归档标记的正则（忽略大小写）
ARCHIVE_MARKERS = re.compile(
    r'归档|archive|deprecated|历史参考|已过時|📦|>\s*\*\*状态\*\*',
    re.IGNORECASE | re.UNICODE
)

ARCHIVE_HEADER_TEMPLATE = """> **归档状态**: 📦 已归档
> **归档日期**: {date}
> **归档原因**: {reason}
>
> ⚠️ 本文档为历史归档，内容可能已过时，请以项目最新活跃文档为准。
>
> ---
>
"""


def get_reason(path: Path) -> str:
    """根据文件路径推断归档原因"""
    rel = path.relative_to(ARCHIVE_DIR)
    parts = rel.parts
    for part in parts:
        if part in REASON_MAP:
            return REASON_MAP[part]
    return "历史内容归档"


def needs_header(path: Path) -> bool:
    """检查文件是否需要添加归档头部"""
    with open(path, "r", encoding="utf-8") as f:
        first_15_lines = "".join(f.readline() for _ in range(15))
    return not ARCHIVE_MARKERS.search(first_15_lines)


def add_header(path: Path) -> bool:
    """为文件添加归档头部，返回是否修改"""
    with open(path, "r", encoding="utf-8") as f:
        content = f.read()

    if not content.strip():
        return False

    reason = get_reason(path)
    header = ARCHIVE_HEADER_TEMPLATE.format(date=ARCHIVE_DATE, reason=reason)

    # 如果文件以 # 标题开头，在标题前插入头部
    if content.startswith("#"):
        new_content = header + content
    else:
        # 否则在文件最前面插入
        new_content = header + content

    with open(path, "w", encoding="utf-8") as f:
        f.write(new_content)
    return True


def main():
    md_files = list(ARCHIVE_DIR.rglob("*.md"))
    total = len(md_files)
    skipped = 0
    added = 0

    for path in sorted(md_files):
        if needs_header(path):
            if add_header(path):
                added += 1
                print(f"  + {path.relative_to(PROJECT_ROOT)}")
        else:
            skipped += 1
            print(f"  · {path.relative_to(PROJECT_ROOT)} (已标记，跳过)")

    print(f"\n总计: {total} 个文件")
    print(f"  新增归档头部: {added}")
    print(f"  跳过 (已有标记): {skipped}")


if __name__ == "__main__":
    main()
