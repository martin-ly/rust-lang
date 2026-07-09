#!/usr/bin/env python3
"""
三轨内容相似度检测脚本

检测 concept/、knowledge/、docs/ 中标题相似或关键词重叠的文件对。
使用 Jaccard 相似度和标题匹配。

用法:
    python scripts/detect_content_overlap.py
"""

from pathlib import Path
from collections import defaultdict
import re
from datetime import datetime

PROJECT_ROOT = Path(".")
THRESHOLD = 0.6  # 相似度阈值


def extract_title(filepath):
    """提取文件标题（第一个 # 标题）"""
    try:
        content = filepath.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return ""

    # 查找第一个 # 标题
    match = re.search(r"^#\s+(.+)$", content, re.MULTILINE)
    if match:
        return match.group(1).strip()
    return ""


def is_redirect_stub(filepath):
    """检测文件是否为重定向/归档 stub（应排除在重复检测外）"""
    try:
        content = filepath.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return False

    lines = content.strip().splitlines()
    # 重定向 stub 通常很短
    if len(lines) > 25:
        return False

    stub_markers = [
        "历史内容已迁移",
        "本文件不再维护",
        "权威来源",
        "归档说明",
        "内容已整合",
        "内容已迁移",
        "已重定向",
        "superseded",
        "stub/archive redirect",
        "已移除",
        "正文已移除",
        "重定向 stub",
    ]
    lower_content = content.lower()
    marker_count = sum(1 for m in stub_markers if m.lower() in lower_content)
    return marker_count >= 2



def extract_keywords(filepath):
    """提取文件关键词（从标题和目录中的关键术语）"""
    try:
        content = filepath.read_text(encoding="utf-8", errors="ignore")
    except Exception:
        return set()

    # 提取所有 ## 和 ### 标题
    headers = re.findall(r"^#{2,3}\s+(.+)$", content, re.MULTILINE)

    # 提取关键术语（粗体、斜体、代码中的术语）
    terms = re.findall(r"\*\*([^*]+)\*\*|\*([^*]+)\*|`([^`]+)`", content)
    flat_terms = []
    for t in terms:
        flat_terms.extend([x for x in t if x])

    # 合并所有来源
    words = set()
    for text in [extract_title(filepath)] + headers + flat_terms[:50]:
        # 分词：中文按字，英文按空格
        text = text.lower()
        # 保留中文和英文单词
        cn_words = re.findall(r"[\u4e00-\u9fff]{2,}", text)
        en_words = re.findall(r"[a-z_]+(?:\s+[a-z_]+){0,2}", text)
        words.update(cn_words)
        words.update(w.strip() for w in en_words if len(w.strip()) > 2)

    return words


def jaccard_similarity(set1, set2):
    """计算两个集合的 Jaccard 相似度"""
    if not set1 or not set2:
        return 0.0
    intersection = len(set1 & set2)
    union = len(set1 | set2)
    return intersection / union if union > 0 else 0.0


def find_md_files(dirs, include_stubs=False):
    """查找目录中的所有 Markdown 文件"""
    files = []
    for d in dirs:
        for f in d.rglob("*.md"):
            if "archive" in f.parts or "temp" in f.parts or "swap" in f.parts:
                continue
            if f.name in ["README.md", "INDEX.md"]:
                continue
            if not include_stubs and is_redirect_stub(f):
                continue
            files.append(f)
    return files


def main():
    import sys

    include_stubs = "--include-stubs" in sys.argv

    print("=== 四轨内容相似度检测 ===\n")

    dirs = [
        PROJECT_ROOT / "concept",
        PROJECT_ROOT / "knowledge",
        PROJECT_ROOT / "docs",
        PROJECT_ROOT / "content",
    ]

    files = find_md_files(dirs, include_stubs=include_stubs)
    if include_stubs:
        print("模式: 包含重定向 stub")
    print(f"扫描文件数: {len(files)}")
    print(f"相似度阈值: {THRESHOLD}\n")

    # 提取每个文件的关键词
    file_keywords = {}
    file_titles = {}
    for f in files:
        file_keywords[f] = extract_keywords(f)
        file_titles[f] = extract_title(f)

    # 比较所有文件对（只比较不同目录间的）
    overlaps = []

    # 按目录分组
    dir_files = defaultdict(list)
    for f in files:
        # 确定文件属于哪个顶层目录
        rel = f.relative_to(PROJECT_ROOT)
        top_dir = rel.parts[0]
        dir_files[top_dir].append(f)

    # 只比较不同顶层目录间的文件
    top_dirs = list(dir_files.keys())
    for i in range(len(top_dirs)):
        for j in range(i + 1, len(top_dirs)):
            dir1, dir2 = top_dirs[i], top_dirs[j]
            print(f"比较 {dir1}/ vs {dir2}/ ...")

            for f1 in dir_files[dir1]:
                for f2 in dir_files[dir2]:
                    title1 = file_titles[f1]
                    title2 = file_titles[f2]

                    # 标题相似度（简单字符串包含）
                    title_sim = 0.0
                    if title1 and title2:
                        t1_words = set(title1.lower().split())
                        t2_words = set(title2.lower().split())
                        title_sim = jaccard_similarity(t1_words, t2_words)

                    # 关键词相似度
                    kw_sim = jaccard_similarity(file_keywords[f1], file_keywords[f2])

                    # 综合相似度（标题权重更高）
                    combined_sim = max(title_sim * 1.5, kw_sim)
                    combined_sim = min(combined_sim, 1.0)

                    if combined_sim >= THRESHOLD:
                        overlaps.append((combined_sim, f1, f2, title1, title2))

    # 排序并输出
    overlaps.sort(key=lambda x: x[0], reverse=True)

    print(f"\n=== 发现 {len(overlaps)} 对潜在重复文件 ===\n")

    report_lines = ["# 四轨内容相似度检测报告\n\n", f"- **扫描文件数**: {len(files)}\n", f"- **相似度阈值**: {THRESHOLD}\n", f"- **潜在重复对**: {len(overlaps)}\n\n"]
    report_lines.append("| 相似度 | 文件1 | 文件2 | 标题1 | 标题2 |\n")
    report_lines.append("|:---|:---|:---|:---|:---|\n")

    for sim, f1, f2, t1, t2 in overlaps[:50]:
        r1 = f1.relative_to(PROJECT_ROOT)
        r2 = f2.relative_to(PROJECT_ROOT)
        print(f"  [{sim:.2f}] {r1}")
        print(f"          vs {r2}")
        print(f"          '{t1[:40]}' vs '{t2[:40]}'")
        print()
        report_lines.append(f"| {sim:.2f} | `{r1}` | `{r2}` | {t1[:30]} | {t2[:30]} |\n")

    report_lines.append("\n## 建议\n\n")
    report_lines.append("1. 相似度 > 0.8 的文件对：优先人工复核，考虑合并或归档\n")
    report_lines.append("2. 相似度 0.6-0.8 的文件对：检查是否存在内容交叉引用需求\n")
    report_lines.append("3. concept/ 优先：知识应以 concept/ 为主轨，其他轨道迁移或引用\n")

    # 保存报告
    today = datetime.now().strftime("%Y_%m_%d")
    report_path = PROJECT_ROOT / "reports" / f"CONTENT_OVERLAP_DETECTION_{today}.md"
    report_path.parent.mkdir(exist_ok=True)
    report_path.write_text("".join(report_lines), encoding="utf-8", newline="\n")
    print(f"报告已保存: {report_path}")


if __name__ == "__main__":
    main()
