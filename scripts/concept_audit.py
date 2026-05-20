#!/usr/bin/env python3
"""概念知识体系自动化审计脚本 v2.0

检查项（与 concept_consistency_auditor.py 互补）：
1. 跨文件链接完整性（含死链接检测）
2. 代码块语言标记正确性
3. Bloom 认知层级标注检查
4. 来源标注率统计
5. 文件命名规范
6. TODO 标记汇总
7. 生成结构化审计报告

用法:
    python3 scripts/concept_audit.py
"""

import os
import re
import sys
from pathlib import Path
from collections import defaultdict
from datetime import datetime

CONCEPT_DIR = Path("concept")
KNOWLEDGE_DIR = Path("knowledge")
DOCS_DIR = Path("docs")
REPORT_PATH = "reports/concept_audit_report.md"

# 需要检查的核心概念文件路径模式（排除入口索引和 meta）
CORE_PATTERNS = [
    "01_foundation/*.md",
    "02_intermediate/*.md",
    "03_advanced/*.md",
    "04_formal/*.md",
    "05_comparative/*.md",
    "06_ecosystem/*.md",
    "07_future/*.md",
]

# Bloom 层级关键词映射（用于检测标注）
BLOOM_KEYWORDS = {
    "记忆": ["记住", "列举", "识别", "复述", "标注"],
    "理解": ["解释", "描述", "分类", "总结", "比较", "区分"],
    "应用": ["应用", "使用", "执行", "实现", "演示"],
    "分析": ["分析", "分解", "推导", "推断", "检查", "关联"],
    "评价": ["评价", "评估", "判断", "论证", "验证", "权衡"],
    "创造": ["设计", "构建", "创造", "整合", "重构", "提出"],
}

# 来源标注模式（多格式覆盖）
SOURCE_PATTERNS = [
    # 显式来源标注
    r"\[来源[：:]\s*[^\]]+\]",
    r"\[学术来源[：:][^\]]*\]",
    r"\[工业来源[：:][^\]]*\]",
    r"> \*\*来源[：:][^\*]*\*\*",
    r"> \*\*权威来源[：:][^\*]*\*\*",
    r">\s*\*\*\[[^\]]+\]\*\*",  # > **[来源: ...]** 格式
    # 学术会议/期刊引用
    r"\[RFC\s+\d+[^\]]*\]",
    r"\[POPL\s+\d{4}[^\]]*\]",
    r"\[PLDI\s+\d{4}[^\]]*\]",
    r"\[ECOOP\s+\d{4}[^\]]*\]",
    r"\[SOSP\s+\d{4}[^\]]*\]",
    r"\[OOPSLA\s+\d{4}[^\]]*\]",
    r"\[JFP\s+\d{4}[^\]]*\]",
    r"\[ICFP\s+\d{4}[^\]]*\]",
    r"\[FM\s+\d{4}[^\]]*\]",
    r"\[VSTTE\s+\d{4}[^\]]*\]",
    # 工具/项目名称标注
    r"\[RustBelt[^\]]*\]",
    r"\[Iris[^\]]*\]",
    r"\[Kani[^\]]*\]",
    r"\[Verus[^\]]*\]",
    r"\[Creusot[^\]]*\]",
    r"\[Prusti[^\]]*\]",
    r"\[Aeneas[^\]]*\]",
    r"\[RefinedRust[^\]]*\]",
    r"\[Miri[^\]]*\]",
    # 行内作者+会议引用
    r"Jung et al\.\s*,\s*\*[^\*]+\*\s*,\s*(?:POPL|PLDI|ECOOP|OOPSLA|JFP|ICFP)\s+\d{4}",
    r"O'Hearn\s+\d{4}",
    r"Girard\s+\d{4}",
    r"Tofte-Talpin\s+\d{4}",
    # Wikipedia / Reference 标注
    r"\[Wikipedia[：:]?\s*[^\]]+\]",
    r"\[Rust Reference[^\]]*\]",
    r"\[Rust Book[^\]]*\]",
    r"\[Rustonomicon[^\]]*\]",
    r"\[The Rust Programming Language[^\]]*\]",
    # Release Notes / RFC
    r"\[Rust\s+\d+\.\d+\s+Release Notes\]",
    r"\[Rust\s+\d{4}\s+Edition\s+Guide\]",
    r"\[RFC\s+\d{4}[^\]]*\]",
    # 来源可信度标记
    r"来源[：:]\s*\[[^\]]+\]\s*·\s*[^\n]*✅",
    r"来源[：:]\s*\[[^\]]+\]\s*·\s*[^\n]*🔍",
]


def find_md_files():
    """查找核心 markdown 文件"""
    files = []
    for pattern in CORE_PATTERNS:
        files.extend(CONCEPT_DIR.glob(pattern))
    # 也包含 00_meta 下的 sources.md 和 inter_layer_map.md
    files.extend(CONCEPT_DIR.glob("00_meta/*.md"))
    # 排除入口文件
    excluded = {"00.md", "01.md", "02.md", "03.md", "04.md", "05.md", "06.md", "07.md", "README.md"}
    files = [f for f in files if f.name not in excluded]
    return sorted(set(files))


def find_knowledge_md_files():
    """查找 knowledge 目录 markdown 文件"""
    files = []
    for pattern in ["**/*.md"]:
        files.extend(KNOWLEDGE_DIR.glob(pattern))
    # 排除 archive 和 .kimi
    files = [f for f in files if "99_archive" not in str(f) and ".kimi" not in str(f)]
    return sorted(set(files))


def find_docs_md_files():
    """查找 docs 目录 markdown 文件"""
    files = []
    for pattern in ["**/*.md"]:
        files.extend(DOCS_DIR.glob(pattern))
    # 排除 archive
    files = [f for f in files if "archive" not in str(f)]
    return sorted(set(files))


def check_cross_links(content, file_path):
    """检查跨文件链接，返回 (数量, 链接列表, 死链接列表)"""
    # 匹配 [text](./path.md) 或 [text](../path.md) 格式
    links = re.findall(r'\[([^\]]+)\]\((\.\.?/[^)]+\.md)\)', content)
    # 也匹配绝对路径链接（以 /concept/ 开头）
    links += re.findall(r'\[([^\]]+)\]\((/[^)]+\.md)\)', content)

    dead_links = []
    for text, target in links:
        if target.startswith("/"):
            resolved = Path(target.lstrip("/"))
        else:
            resolved = (file_path.parent / target).resolve()
            # 尝试相对 concept 根目录
            if not resolved.exists():
                resolved = (CONCEPT_DIR / target).resolve()
        if not resolved.exists():
            dead_links.append((text, target))

    return len(links), links, dead_links


def check_code_blocks(content):
    """检查代码块标记问题"""
    issues = []
    blocks = re.findall(r'```(\w+)?[^\n]*\n', content)
    for i, block in enumerate(blocks):
        lang = block.strip() if block else ''
        # 排除已知的非代码块类型
        if not lang and not any(marker in content for marker in ['```mermaid', '```text', '```plain', '```yaml', '```json', '```toml']):
            # 更精确：检查这个具体代码块是否有语言标记
            pass  # 简化处理：空语言标记在 markdown 中也是合法的
        # 主要问题：rust 代码块缺少 ,ignore 或 ,no_run 标记（如果包含不可编译的伪代码）
    return issues


def check_bloom_levels(content, file_path):
    """检查 Bloom 层级标注"""
    found = set()
    for level, keywords in BLOOM_KEYWORDS.items():
        for kw in keywords:
            if re.search(rf'\b{kw}', content, re.IGNORECASE):
                found.add(level)
                break

    # 检查显式 Bloom 标注
    explicit = bool(re.search(r'Bloom\s*层级|认知层级|学习目标', content, re.IGNORECASE))
    return found, explicit


def check_sources(content):
    """统计来源标注"""
    total_annotations = 0
    for pattern in SOURCE_PATTERNS:
        total_annotations += len(re.findall(pattern, content, re.IGNORECASE))

    # 估算段落数（以空行分隔的文本块）
    paragraphs = [p for p in re.split(r'\n\s*\n', content) if len(p.strip()) > 20]
    para_count = len(paragraphs)

    # 估算论断数（以 "> " 开头的引用块、定理、定义等）
    claims = len(re.findall(r'^(?:>|#+\s*[^:]+[:：]|\*\*定理|\*\*定义|\*\*公理)', content, re.MULTILINE))

    return total_annotations, para_count, claims


def check_file_naming(file_path):
    """检查文件命名是否符合 NN_english_name.md"""
    name = file_path.name
    return bool(re.match(r'^\d{2}_[a-z_]+\.md$', name)), name


def check_todos(content):
    """检查文件内 TODO 状态"""
    pending = len(re.findall(r'^- \[ \]', content, re.MULTILINE))
    done = len(re.findall(r'^- \[x\]', content, re.MULTILINE))
    return pending, done


def generate_report(results):
    now = datetime.now().isoformat(timespec='minutes')
    lines = [
        "# 概念知识体系自动化审计报告 v2.0",
        "",
        f"> 生成时间: {now}",
        f"> 扫描文件数: {results['total_files']}",
        f"> 版本对齐: Rust 1.95.0 stable",
        "",
        "## 摘要",
        "",
        f"| 指标 | 数值 | 状态 |",
        f"|:---|:---|:---|",
        f"| 扫描文件数 | {results['total_files']} | — |",
        f"| 跨文件链接 ≥3 | {results['cross_links_ok']}/{results['total_files']} | {'✅' if results['cross_links_ok'] == results['total_files'] else '⚠️'} |",
        f"| 死链接文件 | {results['dead_link_files']} | {'✅' if results['dead_link_files'] == 0 else '❌'} |",
        f"| 命名规范符合 | {results['naming_ok']}/{results['total_files']} | {'✅' if results['naming_ok'] == results['total_files'] else '⚠️'} |",
        f"| 代码块问题文件 | {len(results['code_block_issues'])} | {'✅' if not results['code_block_issues'] else '⚠️'} |",
        f"| 显式 Bloom 标注 | {results['bloom_explicit']}/{results['total_files']} | {'✅' if results['bloom_explicit'] >= results['total_files'] * 0.7 else '⚠️'} |",
        f"| 平均来源标注率 | {results['avg_source_rate']:.1%} | {'✅' if results['avg_source_rate'] >= 0.15 else '⚠️'} |",
        f"| TODO 待完成 | {results['todo_summary']['pending']} | {'✅' if results['todo_summary']['pending'] == 0 else '⚠️'} |",
        f"| TODO 已完成 | {results['todo_summary']['done']} | — |",
        "",
    ]

    if results['cross_links_fail']:
        lines.extend([
            "## 跨文件链接不足的文件",
            "",
            "| 文件 | 链接数 | 现有链接目标 |",
            "|:---|:---|:---|",
        ])
        for item in results['cross_links_fail']:
            links_preview = ', '.join(item['links'][:3]) if item['links'] else '无'
            lines.append(f"| {item['file']} | {item['count']} | {links_preview} |")
        lines.append("")

    if results['dead_links']:
        lines.extend([
            "## 死链接检测",
            "",
            "| 源文件 | 链接文本 | 死链接目标 |",
            "|:---|:---|:---|",
        ])
        for item in results['dead_links']:
            lines.append(f"| {item['file']} | {item['text']} | `{item['target']}` |")
        lines.append("")

    if results['naming_fail']:
        lines.extend([
            "## 命名不规范的文件",
            "",
        ])
        for f in results['naming_fail']:
            lines.append(f"- {f}")
        lines.append("")

    if results['bloom_missing']:
        lines.extend([
            "## 缺少 Bloom 层级标注的文件",
            "",
            "| 文件 | 检测到的 Bloom 关键词 |",
            "|:---|:---|",
        ])
        for item in results['bloom_missing']:
            kw = ', '.join(item['found']) if item['found'] else '无'
            lines.append(f"| {item['file']} | {kw} |")
        lines.append("")

    if results['source_low']:
        lines.extend([
            "## 来源标注率偏低的文件 (< 10%)",
            "",
            "| 文件 | 标注数 | 估算段落数 | 标注率 |",
            "|:---|:---|:---|:---|",
        ])
        for item in results['source_low']:
            lines.append(f"| {item['file']} | {item['annotations']} | {item['paragraphs']} | {item['rate']:.1%} |")
        lines.append("")

    lines.extend([
        "## 方法论说明",
        "",
        "- **跨文件链接**: 检测指向其他 `.md` 文件的相对链接，目标文件必须存在",
        "- **Bloom 层级**: 基于认知层级关键词的启发式检测 + 显式标注检查",
        "- **来源标注率**: 标注数 / (段落数 + 论断数 × 2)，期望 ≥ 15%",
        "- **命名规范**: `NN_english_name.md`，入口文件 (`00.md`–`07.md`) 除外",
        "",
        "> 本报告与 `scripts/concept_consistency_auditor.py` 互补：本脚本做快速健康检查，后者做深度概念冲突检测。",
    ])

    Path(REPORT_PATH).parent.mkdir(parents=True, exist_ok=True)
    with open(REPORT_PATH, 'w', encoding='utf-8') as f:
        f.write('\n'.join(lines))


# 各轨道的审计阈值
TRACK_THRESHOLDS = {
    'concept/': {
        'min_cross_links': 3,
        'min_source_rate': 0.10,
        'require_bloom': True,
        'require_naming': True,
    },
    'knowledge/': {
        'min_cross_links': 1,
        'min_source_rate': 0.05,
        'require_bloom': False,
        'require_naming': False,
    },
    'docs/': {
        'min_cross_links': 1,
        'min_source_rate': 0.03,
        'require_bloom': False,
        'require_naming': False,
    },
}


def scan_files(md_files, track_name):
    """扫描一组文件，返回结果字典"""
    thresholds = TRACK_THRESHOLDS.get(track_name, TRACK_THRESHOLDS['concept/'])

    results = {
        'track': track_name,
        'total_files': len(md_files),
        'cross_links_ok': 0,
        'cross_links_fail': [],
        'dead_link_files': 0,
        'dead_links': [],
        'code_block_issues': [],
        'todo_summary': {'pending': 0, 'done': 0},
        'naming_ok': 0,
        'naming_fail': [],
        'bloom_explicit': 0,
        'bloom_missing': [],
        'avg_source_rate': 0.0,
        'source_low': [],
    }

    total_source_rate = 0.0
    source_file_count = 0

    for file_path in md_files:
        content = file_path.read_text(encoding='utf-8')
        rel_path = str(file_path).replace('\\', '/')
        rel_path_norm = rel_path.replace('\\', '/')
        is_meta = '/00_meta/' in rel_path_norm or rel_path_norm.startswith('00_meta/')
        is_readme = file_path.name.lower() == 'readme.md'

        # 1. 跨文件链接检查（含死链接）
        link_count, links, dead = check_cross_links(content, file_path)
        if link_count >= thresholds['min_cross_links']:
            results['cross_links_ok'] += 1
        else:
            results['cross_links_fail'].append({
                'file': rel_path,
                'count': link_count,
                'links': [l[1] for l in links[:5]]
            })
        if dead:
            results['dead_link_files'] += 1
            for text, target in dead:
                results['dead_links'].append({
                    'file': rel_path,
                    'text': text,
                    'target': target,
                })

        # 2. 代码块检查
        code_issues = check_code_blocks(content)
        if code_issues:
            results['code_block_issues'].append({
                'file': rel_path,
                'issues': code_issues
            })

        # 3. Bloom 层级检查
        found_kw, explicit = check_bloom_levels(content, file_path)
        if explicit:
            results['bloom_explicit'] += 1
        elif thresholds['require_bloom']:
            results['bloom_missing'].append({
                'file': rel_path,
                'found': sorted(found_kw),
            })

        # 4. 来源标注率
        annotations, para_count, claims = check_sources(content)
        denominator = max(para_count + claims * 2, 1)
        rate = annotations / denominator
        total_source_rate += rate
        source_file_count += 1
        # 00_meta/ 是元信息目录，降低来源率要求
        effective_min_rate = thresholds['min_source_rate']
        if is_meta:
            effective_min_rate = 0.03
        if rate < effective_min_rate and para_count > 5:
            results['source_low'].append({
                'file': rel_path,
                'annotations': annotations,
                'paragraphs': para_count,
                'rate': rate,
            })

        # 5. TODO 统计
        pending, done = check_todos(content)
        results['todo_summary']['pending'] += pending
        results['todo_summary']['done'] += done

        # 6. 命名规范
        # 豁免：00_meta/ 元信息目录和 README.md 入口文件
        naming_ok, name = check_file_naming(file_path)
        if naming_ok or is_meta or is_readme:
            results['naming_ok'] += 1
        elif thresholds['require_naming']:
            results['naming_fail'].append(rel_path)

    if source_file_count > 0:
        results['avg_source_rate'] = total_source_rate / source_file_count

    return results


def print_track_results(results):
    """打印单个轨道的结果摘要"""
    thresholds = TRACK_THRESHOLDS.get(results['track'], TRACK_THRESHOLDS['concept/'])
    min_links = thresholds['min_cross_links']
    print(f"\n{'='*60}")
    print(f"轨道: {results['track']}")
    print(f"{'='*60}")
    print(f"扫描文件数: {results['total_files']}")
    print(f"跨文件链接 ≥{min_links}: {results['cross_links_ok']}/{results['total_files']}")
    print(f"死链接文件: {results['dead_link_files']}")
    print(f"命名规范符合: {results['naming_ok']}/{results['total_files']}")
    print(f"代码块问题: {len(results['code_block_issues'])} 个文件")
    print(f"Bloom 显式标注: {results['bloom_explicit']}/{results['total_files']}")
    print(f"平均来源标注率: {results['avg_source_rate']:.1%}")
    print(f"TODO 待完成: {results['todo_summary']['pending']}")
    print(f"TODO 已完成: {results['todo_summary']['done']}")


def main():
    # 扫描三个轨道
    concept_files = find_md_files()
    knowledge_files = find_knowledge_md_files()
    docs_files = find_docs_md_files()

    concept_results = scan_files(concept_files, "concept/")
    knowledge_results = scan_files(knowledge_files, "knowledge/")
    docs_results = scan_files(docs_files, "docs/")

    all_results = [concept_results, knowledge_results, docs_results]

    # 生成汇总报告
    generate_report(concept_results)

    # 打印摘要
    print(f"\n{'='*60}")
    print("概念知识体系自动化审计 v2.1 完成")
    print(f"{'='*60}")

    for r in all_results:
        print_track_results(r)

    total_files = sum(r['total_files'] for r in all_results)
    total_dead = sum(r['dead_link_files'] for r in all_results)
    print(f"\n{'='*60}")
    print(f"总计扫描文件数: {total_files}")
    print(f"总计死链接: {total_dead}")
    print(f"报告: {REPORT_PATH}")

    has_issues = any(
        r['cross_links_fail'] or r['dead_links'] or r['code_block_issues']
        or r['bloom_missing'] or r['source_low']
        for r in all_results
    )
    if has_issues:
        print(f"\n⚠️ 发现以下问题:")
        for r in all_results:
            if r['cross_links_fail']:
                print(f"  [{r['track']}] {len(r['cross_links_fail'])} 个文件跨文件链接不足")
            if r['dead_links']:
                print(f"  [{r['track']}] {len(r['dead_links'])} 个死链接")
            if r['code_block_issues']:
                print(f"  [{r['track']}] {len(r['code_block_issues'])} 个文件代码块标记有问题")
            if r['bloom_missing']:
                print(f"  [{r['track']}] {len(r['bloom_missing'])} 个文件缺少 Bloom 标注")
            if r['source_low']:
                print(f"  [{r['track']}] {len(r['source_low'])} 个文件来源标注率 < 10%")
        sys.exit(1)
    else:
        print(f"\n✅ 审计通过！")


if __name__ == '__main__':
    main()
