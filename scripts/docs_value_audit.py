#!/usr/bin/env python3
"""
docs/ 目录价值审计脚本

功能:
1. 扫描 docs/ 中所有 .md 文件（排除 archive/）
2. 检查版本声明是否最新（1.96.0+）
3. 检查"最后更新"日期
4. 检查损坏的内部链接
5. 生成审计报告

用法:
    python scripts/docs_value_audit.py
"""

import os
import re
import sys
from datetime import datetime, timezone
from pathlib import Path
from collections import defaultdict

PROJECT_ROOT = Path(__file__).parent.parent
DOCS_DIR = PROJECT_ROOT / "docs"

# 当前项目版本
CURRENT_RUST_VERSION = "1.96.0"
CURRENT_DATE = datetime.now(timezone.utc).strftime("%Y-%m-%d")


def is_archived(filepath: Path) -> bool:
    """判断文件是否属于已归档内容。

    规则：
    1. 文件自身元数据头含“已归档”/“归档级”/“ARCHIVED”。
    2. 所在目录（直到 docs/）的 README.md 标注该目录整体已归档。
    """
    archived_markers = ("已归档", "归档级", "ARCHIVED")

    # 检查文件自身元数据头
    try:
        head = filepath.read_text(encoding="utf-8")[:1500]
        if any(m in head for m in archived_markers):
            return True
    except Exception:
        pass

    # 检查父目录 README
    for parent in filepath.parents:
        if parent == DOCS_DIR:
            break
        readme = parent / "README.md"
        if readme.exists():
            try:
                head = readme.read_text(encoding="utf-8")[:1500]
                if any(m in head for m in archived_markers):
                    return True
            except Exception:
                pass
    return False


def find_md_files():
    """查找 docs/ 中所有 Markdown 文件（排除 archive/ 与已归档目录）"""
    files = []
    for f in DOCS_DIR.rglob("*.md"):
        if "archive" in f.parts or "temp" in f.parts or "swap" in f.parts:
            continue
        if is_archived(f):
            continue
        files.append(f)
    return sorted(files)


def check_version_declaration(content, filepath):
    """检查文件中的 Rust 版本声明"""
    issues = []

    # 查找版本声明模式
    # 注意：顺序很重要，先匹配更具体的模式
    version_patterns = [
        (r"> \*\*Rust 版本\*\*:\s*([\d.]+)", "文档版本头"),
        (r"\*\*对应 Rust 版本\*\*:\s*([\d.]+)", "文档版本尾"),
        (r"\*\*Rust 版本\*\*:\s*([\d.]+)", "文档版本尾"),
        (r"rust-version\s*=\s*\"([\d.]+)\"", "Cargo MSRV"),
    ]

    # 历史事实性版本声明模式（通常不需要更新）
    historical_patterns = [
        r"> \*\*稳定版本\*\*:\s*Rust ([\d.]+)",
        r"> \*\*版本\*\*:\s*Rust ([\d.]+)",
        r"> \*\*适用版本\*\*:\s*([\d.]+)",
    ]

    # 历史上下文关键词
    historical_keywords = [
        "引入", "稳定化于", "稳定版", "release notes", "tracking issue",
        "FCP", "RFC", "behavior", "行为变更", "历史", "回顾", "对比",
        "introduced", "stabilized", "release", "changelog", "版本发布",
        "起始版本", "起始", "edition", "起始", "对比", "comparison",
        "vs", "versus", "比较", "迁移", "migration",
    ]

    found_versions = []
    for pattern, _ in version_patterns:
        for match in re.finditer(pattern, content):
            found_versions.append((match.group(1), match.start(), match.group(0), "msrv"))

    for pattern in historical_patterns:
        for match in re.finditer(pattern, content):
            found_versions.append((match.group(1), match.start(), match.group(0), "historical"))

    for ver, pos, text, kind in found_versions:
        # 获取匹配位置前后 120 个字符的上下文
        context_start = max(0, pos - 120)
        context_end = min(len(content), pos + len(text) + 120)
        context = content[context_start:context_end]

        # 如果上下文包含历史关键词，视为历史事实引用，跳过
        if any(kw in context for kw in historical_keywords):
            continue

        # 如果是明确的历史声明模式，跳过
        if kind == "historical":
            continue

        # 排除"1.90–1.93"范围引用（注意使用 en dash，不是 hyphen）
        if "–" in context:
            continue

        # 排除 nightly 预览上下文
        if "Nightly" in context or "nightly" in context or "preview" in context.lower():
            continue

        # 比较版本号
        try:
            parts = ver.split(".")
            current_parts = CURRENT_RUST_VERSION.split(".")
            if len(parts) >= 2 and len(current_parts) >= 2:
                if int(parts[0]) < int(current_parts[0]) or \
                   (int(parts[0]) == int(current_parts[0]) and int(parts[1]) < int(current_parts[1])):
                    issues.append(f"旧版本声明: '{text}' → 建议更新为 {CURRENT_RUST_VERSION}+")
        except ValueError:
            pass

    return issues


def check_last_updated(content, filepath):
    """检查最后更新日期"""
    issues = []

    # 查找最后更新日期
    date_patterns = [
        r"最后更新\*\*:\s*(\d{4}-\d{2}-\d{2})",
        r"最后更新.*?(\d{4}-\d{2}-\d{2})",
        r"> \*\*最后更新\*\*.*?([\d-]+)",
    ]

    for pattern in date_patterns:
        match = re.search(pattern, content)
        if match:
            date_str = match.group(1)
            try:
                file_date = datetime.strptime(date_str, "%Y-%m-%d")
                current = datetime.strptime(CURRENT_DATE, "%Y-%m-%d")
                days_old = (current - file_date).days
                if days_old > 90:
                    issues.append(f"最后更新: {date_str}（{days_old} 天前，建议复审）")
            except ValueError:
                pass
            break

    return issues


def check_internal_links(content, filepath):
    """检查内部链接是否指向存在的文件"""
    issues = []

    # 移除代码块内容，避免代码示例中的方括号被误匹配
    # 使用非贪婪匹配移除 ```...``` 代码块
    content_without_codeblocks = re.sub(r"```[\s\S]*?```", "", content)
    # 移除行内代码 ``...``
    content_without_codeblocks = re.sub(r"`[^`]+`", "", content_without_codeblocks)

    # Markdown 链接模式: [text](path)
    link_pattern = r"\[([^\]]+)\]\(([^)]+)\)"

    for match in re.finditer(link_pattern, content_without_codeblocks):
        text, link = match.groups()

        # 跳过外部链接
        if link.startswith("http://") or link.startswith("https://") or link.startswith("#"):
            continue

        # 跳过锚点-only 链接
        if link.startswith("#"):
            continue

        # 跳过 rustdoc 内部链接（Self::method, crate::path, super::path）
        if link.startswith("Self::") or link.startswith("crate::") or link.startswith("super::"):
            continue

        # 跳过特殊协议
        if link.startswith("mailto:") or link.startswith("tel:"):
            continue

        # 处理相对路径（Markdown 链接总是相对于当前文件所在目录）
        if link.startswith("/"):
            # 以 / 开头的路径：从项目根开始
            target = PROJECT_ROOT / link.lstrip("/").split("#")[0]
        elif not link.startswith("#"):
            # 相对路径：从当前文件所在目录解析
            target = filepath.parent / link.split("#")[0]

        # 规范化路径
        try:
            target = target.resolve()
            if not target.exists():
                issues.append(f"损坏链接: [{text}]({link})")
        except (OSError, ValueError):
            issues.append(f"无效链接: [{text}]({link})")

    return issues


def classify_file(filepath):
    """对文件进行 A/B/C 价值分类"""
    relative = filepath.relative_to(DOCS_DIR)
    parts = relative.parts

    # A 类: 核心参考文档、速查表、学习路径
    if any(d in parts for d in ["02_reference", "01_learning", "01_core"]):
        return "A"
    # B 类: 指南、工具链、实践
    if any(d in parts for d in ["03_guides", "03_practice", "05_guides", "06_toolchain", "07_project"]):
        return "B"
    # C 类: 研究笔记、思考记录、生态系统综述
    if any(d in parts for d in ["research_notes", "04_thinking", "04_research", "content", "07_future"]):
        return "C"
    # 特殊大型目录
    if "rust-ownership-decidability" in parts:
        return "C"
    if "rust-formal-engineering-system" in parts:
        return "C"

    return "B"


def main():
    print(f"=== docs/ 目录价值审计 ===")
    print(f"审计时间: {CURRENT_DATE}")
    print(f"当前 Rust 版本: {CURRENT_RUST_VERSION}")
    print(f"项目根目录: {PROJECT_ROOT}")
    print()

    files = find_md_files()
    print(f"扫描文件数: {len(files)}")
    print()

    # 分类统计
    class_counts = defaultdict(int)
    class_issues = defaultdict(list)

    # 详细问题列表
    all_issues = []

    for filepath in files:
        relative = filepath.relative_to(PROJECT_ROOT)
        file_class = classify_file(filepath)
        class_counts[file_class] += 1

        try:
            content = filepath.read_text(encoding="utf-8")
        except Exception as e:
            all_issues.append((str(relative), f"读取错误: {e}"))
            continue

        issues = []
        issues.extend(check_version_declaration(content, filepath))
        issues.extend(check_last_updated(content, filepath))
        issues.extend(check_internal_links(content, filepath))

        if issues:
            for issue in issues:
                all_issues.append((str(relative), issue))
            class_issues[file_class].extend(issues)

    # 输出统计
    print("=== 文件分类统计 ===")
    for cls in ["A", "B", "C"]:
        count = class_counts[cls]
        issue_count = len(class_issues[cls])
        print(f"  [{cls}类] {count:4d} 文件 | 发现问题: {issue_count}")
    print()

    # 输出问题汇总
    print("=== 问题汇总（按文件分组） ===")
    current_file = None
    for filepath, issue in sorted(all_issues):
        if filepath != current_file:
            current_file = filepath
            print(f"\n📄 {filepath}")
        print(f"   ⚠️ {issue}")

    # 输出摘要
    print()
    print("=== 审计摘要 ===")
    print(f"总文件数: {len(files)}")
    print(f"问题文件数: {len(set(f for f, _ in all_issues))}")
    print(f"总问题数: {len(all_issues)}")
    print()
    print("建议优先处理:")
    print("  1. [A类] 02_reference/ 速查表中的旧版本声明")
    print("  2. [A类] 损坏的内部链接（影响导航）")
    print("  3. [B类] 工具链文档中超过 90 天未更新的文件")
    print("  4. [C类] 评估 research_notes/ 和 rust-ownership-decidability/ 的维护价值")

    # 保存报告
    report_path = PROJECT_ROOT / "reports" / f"DOCS_VALUE_AUDIT_{CURRENT_DATE.replace('-', '_')}.md"
    report_path.parent.mkdir(exist_ok=True)

    with open(report_path, "w", encoding="utf-8") as f:
        f.write(f"# docs/ 目录价值审计报告\n\n")
        f.write(f"- **审计时间**: {CURRENT_DATE}\n")
        f.write(f"- **当前 Rust 版本**: {CURRENT_RUST_VERSION}\n")
        f.write(f"- **扫描文件数**: {len(files)}\n\n")

        f.write("## 文件分类统计\n\n")
        f.write("| 分类 | 文件数 | 问题数 | 说明 |\n")
        f.write("|:---|:---:|:---:|:---|\n")
        f.write(f"| A (核心参考) | {class_counts['A']} | {len(class_issues['A'])} | 速查表、学习路径、核心参考 |\n")
        f.write(f"| B (指南工具) | {class_counts['B']} | {len(class_issues['B'])} | 指南、工具链、实践文档 |\n")
        f.write(f"| C (研究综述) | {class_counts['C']} | {len(class_issues['C'])} | 研究笔记、思考记录、大型专项 |\n")
        f.write("\n")

        f.write("## 详细问题列表\n\n")
        current_file = None
        for filepath, issue in sorted(all_issues):
            if filepath != current_file:
                current_file = filepath
                f.write(f"### {filepath}\n\n")
            f.write(f"- ⚠️ {issue}\n")
        f.write("\n")

        f.write("## 后续建议\n\n")
        f.write("1. **A类优先**: 速查表版本声明直接影响学习者体验\n")
        f.write("2. **链接修复**: 损坏的内部链接降低导航效率\n")
        f.write("3. **过期复审**: 超过 90 天未更新的文档需确认内容有效性\n")
        f.write("4. **C类评估**: 大型专项目录（如 rust-ownership-decidability/）需评估维护成本与价值\n")

    print(f"\n报告已保存至: {report_path}")

    return 0 if not all_issues else 1


if __name__ == "__main__":
    sys.exit(main())
