#!/usr/bin/env python3
"""
archive/ 主题索引同步脚本

用途：
    1. 扫描 archive/ 下新增/未编入 THEMATIC_INDEX.md 的 Markdown 文件。
    2. 按路径/标题关键词自动归类到 8 大主题，生成建议索引条目。
    3. 检测可能的重复标题或 MD5 相同文件，输出待人工确认列表。
    4. 监控 archive/ 内部重复堆积，每月运行一次。

用法：
    python scripts/archive_index_sync.py
    python scripts/archive_index_sync.py --report tmp/archive_index_sync_report.md

输出：
    - 标准输出：新增/未索引文件、重复文件摘要、分类建议。
    - 报告文件（--report）：结构化 Markdown 报告。
"""
from pathlib import Path
from collections import defaultdict
import re, hashlib, argparse, sys
from datetime import datetime

PROJECT_ROOT = Path(__file__).resolve().parent.parent
ARCHIVE = PROJECT_ROOT / "archive"
INDEX_FILE = ARCHIVE / "THEMATIC_INDEX.md"
RELATIONSHIP_FILE = ARCHIVE / "RELATIONSHIP_MAP.md"


def extract_title(filepath):
    """提取文件第一个 # 标题。"""
    try:
        content = filepath.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return ""
    m = re.search(r"^#\s+(.+)$", content, re.MULTILINE)
    return m.group(1).strip() if m else ""


def md5_hash(filepath):
    try:
        return hashlib.md5(filepath.read_bytes()).hexdigest()
    except Exception:
        return ""


# 主题分类规则：关键词 -> (主题, 子主题)
CLASSIFICATION_RULES = [
    # 治理与元数据
    (("archive_policy", "README.md", "PROJECT_", "PHASE", "CRITICAL_AUDIT",
      "SYMMETRIC_DIFFERENCE", "root_meta", "concept_kb.json"),
     "1. 治理与元数据", "1.2 项目级计划与跟进报告"),
    # 版本与权威来源
    (("RUST_19", "verification_reports", "version_reports", "FEATURE_ALIGNMENT",
      "REFERENCE_GAP"),
     "2. Rust 版本与权威来源对齐", "2.1 版本跟踪与特性对齐"),
    # 概念页历史
    (("concept_archive", "/knowledge/", "/guides/", "AI_ASSISTED"),
     "3. 概念页历史与迁移", "3.1 旧版概念页"),
    # Crate 完成报告
    (("crates_reports", "crates_c08", "cargo_package_management"),
     "4. Crate 完成与增强报告", "4.1 按 Crate 组织的完成报告"),
    # 形式化/所有权
    (("rust-ownership-decidability", "formal-engineering-system",
      "rust-ownership-chinese", "formal_methods", "formal_modules", "type_theory"),
     "5. 形式化方法与所有权可判定性", "5.1 核心教程与可判定性分析"),
    # 生态深度
    (("content/ecosystem", "content/scenarios", "content/production",
      "content/emerging", "content/representations"),
     "6. 生态深度内容", "6.1 异步运行时与网络"),
    # 研究笔记
    (("research_notes", "software_design_theory"),
     "7. 研究笔记与实验", "7.1 版本特性研究笔记"),
    # 质量审计/临时文件
    (("LINK_CHECK", "CONTENT_OVERLAP", "CONTENT_COMPLETENESS", "I18N",
      "/reports/", "backup_from_docs", "/temp/", "deprecated"),
     "8. 质量审计、链路检查与临时文件", "8.1 链路健康与死链报告"),
]


def classify_file(path: Path) -> tuple:
    """根据路径和标题关键词返回建议的主题分类。"""
    rel = str(path.relative_to(ARCHIVE)).lower()
    title = extract_title(path).lower()
    for keywords, theme, subtheme in CLASSIFICATION_RULES:
        for kw in keywords:
            if kw.lower() in rel or kw.lower() in title:
                return theme, subtheme
    return "8. 质量审计、链路检查与临时文件", "8.6 备份与重组历史"


def load_indexed_paths():
    """从 THEMATIC_INDEX.md 中粗略提取已索引路径。"""
    if not INDEX_FILE.exists():
        return set()
    text = INDEX_FILE.read_text(encoding="utf-8", errors="ignore")
    indexed = set()
    for m in re.finditer(r"\]\(([^)]+)\)", text):
        link = m.group(1).split("#")[0]
        if link.startswith("../"):
            # 跳过活跃目录链接
            continue
        if not link.startswith("http"):
            indexed.add(link.strip("/"))
    return indexed


def main():
    parser = argparse.ArgumentParser(description="archive/ 主题索引同步脚本")
    parser.add_argument("--report", type=str, help="输出 Markdown 报告路径")
    args = parser.parse_args()

    md_files = sorted(ARCHIVE.rglob("*.md"))
    indexed = load_indexed_paths()

    # 排除索引文件本身
    scan_files = [p for p in md_files if p.name not in ("THEMATIC_INDEX.md", "RELATIONSHIP_MAP.md", "README.md")]

    # 分类统计
    classified = defaultdict(list)
    unindexed = []
    for f in scan_files:
        rel = f.relative_to(ARCHIVE).as_posix()
        theme, subtheme = classify_file(f)
        classified[(theme, subtheme)].append(rel)
        # 粗略判断是否在索引中（路径字符串匹配）
        if not any(rel.startswith(idx) or idx in rel for idx in indexed):
            unindexed.append((rel, theme, subtheme, extract_title(f)))

    # 重复检测
    title_map = defaultdict(list)
    hash_map = defaultdict(list)
    for f in scan_files:
        rel = f.relative_to(ARCHIVE).as_posix()
        title_map[extract_title(f)].append(rel)
        hash_map[md5_hash(f)].append(rel)

    duplicate_titles = {k: v for k, v in title_map.items() if len(v) > 1 and k}
    duplicate_hashes = {k: v for k, v in hash_map.items() if len(v) > 1 and k}

    # 输出
    lines = [
        f"# Archive 索引同步报告\n\n",
        f"> 生成时间: {datetime.now().isoformat()}\n",
        f"> 扫描文件数: {len(scan_files)}\n",
        f"> 未编入索引（疑似）: {len(unindexed)}\n",
        f"> 重复标题组: {len(duplicate_titles)}\n",
        f"> MD5 相同组: {len(duplicate_hashes)}\n\n",
    ]

    lines.append("## 分类统计\n\n")
    lines.append("| 主题 | 子主题 | 文件数 |\n|------|--------|--------|\n")
    for (theme, subtheme), files in sorted(classified.items()):
        lines.append(f"| {theme} | {subtheme} | {len(files)} |\n")

    lines.append("\n## 未编入索引的文件（建议补充）\n\n")
    if unindexed:
        for rel, theme, subtheme, title in unindexed[:200]:  # 限制数量
            lines.append(f"- **{theme} / {subtheme}**: `{rel}` — `{title[:60]}`\n")
        if len(unindexed) > 200:
            lines.append(f"\n... 还有 {len(unindexed) - 200} 项未显示。\n")
    else:
        lines.append("未发现明显未编入索引的文件。\n")

    lines.append("\n## 重复标题组（前 50）\n\n")
    for k, vals in sorted(duplicate_titles.items(), key=lambda x: -len(x[1]))[:50]:
        lines.append(f"### `{k[:80]}` ({len(vals)} 份)\n")
        for v in vals:
            lines.append(f"- {v}\n")

    lines.append("\n## MD5 相同组（前 50）\n\n")
    for k, vals in sorted(duplicate_hashes.items(), key=lambda x: -len(x[1]))[:50]:
        lines.append(f"### hash `{k[:12]}...` ({len(vals)} 份)\n")
        for v in vals:
            lines.append(f"- {v}\n")

    report_text = "".join(lines)

    if args.report:
        out_path = Path(args.report)
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(report_text, encoding="utf-8")
        print(f"报告已保存: {out_path}")
    else:
        print(report_text)

    print(f"\n扫描完成：{len(scan_files)} 文件，{len(unindexed)} 未编入索引，"
          f"{len(duplicate_titles)} 重复标题组，{len(duplicate_hashes)} MD5 相同组。")


if __name__ == "__main__":
    main()
