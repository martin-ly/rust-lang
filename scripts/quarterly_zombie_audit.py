#!/usr/bin/env python3
"""
季度僵尸内容清理机制：
90 天无内部链接指向、无 git 提交的文件自动标记为"僵尸内容"。
"""

import os
import subprocess
from pathlib import Path
from datetime import datetime, timedelta

ROOT = Path.cwd()
REPORTS_DIR = Path("reports")
ZOMBIE_DAYS = 90


def get_git_last_commit(path: Path) -> datetime:
    try:
        result = subprocess.run(
            ["git", "log", "-1", "--format=%ct", str(path)],
            capture_output=True, text=True, check=True
        )
        return datetime.fromtimestamp(int(result.stdout.strip()))
    except Exception:
        return datetime.now()


def count_internal_links(md_path: Path) -> int:
    target = str(md_path.resolve().relative_to(ROOT.resolve())).replace("\\", "/")
    count = 0
    for root, _, files in os.walk(ROOT):
        for f in files:
            if f.endswith(".md"):
                fpath = Path(root) / f
                try:
                    content = fpath.read_text(encoding="utf-8", errors="ignore")
                    if target in content:
                        count += 1
                except Exception:
                    pass
    return count


def main():
    # 扫描 concept/、knowledge/、docs/ 中的 Markdown 文件
    scan_dirs = ["concept", "knowledge", "docs"]
    zombies = []
    
    for dir_name in scan_dirs:
        dir_path = ROOT / dir_name
        if not dir_path.exists():
            continue
        for md_path in sorted(dir_path.rglob("*.md")):
            if "archive" in str(md_path) or "sources" in str(md_path):
                continue
            
            last_commit = get_git_last_commit(md_path)
            days_since = (datetime.now() - last_commit).days
            links = count_internal_links(md_path)
            
            if days_since > ZOMBIE_DAYS and links == 0:
                rel = str(md_path.relative_to(ROOT)).replace("\\", "/")
                zombies.append((rel, days_since))
    
    # 输出报告
    report_path = REPORTS_DIR / "ZOMBIE_CONTENT_AUDIT_2026_06_03.md"
    with open(report_path, "w", encoding="utf-8") as f:
        f.write("# 季度僵尸内容审计报告\n\n")
        f.write(f"> **生成时间**: {datetime.now().isoformat()}\n")
        f.write(f"> **僵尸定义**: {ZOMBIE_DAYS} 天无提交 + 无内部链接\n")
        f.write(f"> **僵尸文件数**: {len(zombies)}\n\n")
        f.write("## 建议处理清单\n\n")
        f.write("| 文件 | 距最后提交（天） | 建议操作 |\n")
        f.write("|:---|:---:|:---|\n")
        for rel, days in zombies:
            f.write(f"| `{rel}` | {days} | 审查后归档或删除 |\n")
        f.write("\n## 自动化建议\n\n")
        f.write("- 在 CI 中每月运行此脚本\n")
        f.write("- 新标记僵尸文件不阻断构建，但需在下个季度 review 中处理\n")
    
    print(f"僵尸内容审计完成: {len(zombies)} 个文件")
    print(f"报告保存至: {report_path}")


if __name__ == "__main__":
    main()
