#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Markdown 内部链接检查工具
扫描 docs 目录中的所有 Markdown 文件，检查内部链接的有效性
"""

import os
import re
import json
from pathlib import Path
from collections import defaultdict
from datetime import datetime

# 配置
DOCS_PATH = Path("e:/_src/rust-lang/docs")
REPORT_FILE = Path("e:/_src/rust-lang/docs/LINK_CHECK_REPORT.md")
JSON_REPORT = Path("e:/_src/rust-lang/docs/link_check_report.json")

# 匹配 Markdown 链接的正则表达式 (排除 http/https 链接)
# 格式: [链接文本](链接目标)
LINK_PATTERN = re.compile(r'\[([^\]]+)\]\((?!https?://)([^)]+)\)')

def get_all_markdown_files(docs_path: Path) -> list[Path]:
    """获取所有 Markdown 文件"""
    return list(docs_path.rglob("*.md"))

def resolve_link(link_target: str, source_file: Path, docs_path: Path) -> Path | None:
    """
    解析链接目标为绝对路径
    
    支持的链接格式:
    - /absolute/path.md - 相对于 docs 目录的绝对路径
    - ./relative/path.md - 相对于当前文件的相对路径
    - ../relative/path.md - 相对于当前文件的父目录
    - relative/path.md - 相对于当前文件的相对路径
    """
    # 跳过锚点链接（# 开头）
    if link_target.startswith('#'):
        return None
    
    # 处理 URL 中的锚点部分
    if '#' in link_target:
        link_target = link_target.split('#')[0]
    
    # 如果链接为空（只有锚点），跳过
    if not link_target.strip():
        return None
    
    source_dir = source_file.parent
    
    if link_target.startswith('/'):
        # 绝对路径（相对于 docs 目录）
        target_path = docs_path / link_target.lstrip('/')
    elif link_target.startswith('./') or link_target.startswith('../'):
        # 相对路径
        target_path = source_dir / link_target
    else:
        # 无明确前缀的相对路径
        target_path = source_dir / link_target
    
    # 规范化路径
    try:
        target_path = target_path.resolve()
    except Exception:
        return None
    
    return target_path

def check_link_exists(target_path: Path) -> tuple[bool, Path | None]:
    """
    检查链接目标是否存在
    返回: (是否存在, 实际存在的路径)
    """
    if not target_path:
        return False, None
    
    # 首先检查原路径
    if target_path.exists() and target_path.is_file():
        return True, target_path
    
    # 尝试添加 .md 扩展名
    md_path = Path(str(target_path) + '.md')
    if md_path.exists() and md_path.is_file():
        return True, md_path
    
    # 尝试添加 /index.md (对于目录)
    if target_path.is_dir():
        index_path = target_path / 'index.md'
        if index_path.exists():
            return True, index_path
    
    return False, None

def find_similar_files(target_name: str, docs_path: Path, max_results: int = 3) -> list[str]:
    """查找可能相似的文件"""
    suggestions = []
    target_stem = Path(target_name).stem.lower()
    
    for md_file in docs_path.rglob("*.md"):
        if target_stem in md_file.stem.lower():
            rel_path = md_file.relative_to(docs_path).as_posix()
            suggestions.append(rel_path)
            if len(suggestions) >= max_results:
                break
    
    return suggestions

def analyze_broken_link(link_target: str, resolved_path: Path, source_file: Path, docs_path: Path) -> str:
    """分析断链原因并提供修复建议"""
    suggestions = []
    
    # 检查是否是扩展名问题
    if not link_target.endswith('.md'):
        md_version = link_target + '.md'
        md_resolved = resolve_link(md_version, source_file, docs_path)
        if md_resolved:
            exists, _ = check_link_exists(md_resolved)
            if exists:
                suggestions.append(f"添加 .md 扩展名: 将 `{link_target}` 改为 `{md_version}`")
    
    # 检查是否是大小写问题 (Windows 不区分大小写，但可能需要检查)
    # 检查是否是路径层级问题
    if '../' in link_target or './' in link_target:
        # 尝试基于文件名搜索
        target_name = Path(link_target).name
        similar = find_similar_files(target_name, docs_path)
        if similar:
            suggestions.append("可能的正确路径:")
            for s in similar[:3]:
                suggestions.append(f"  - `{s}`")
    
    # 检查文件是否被移动或重命名
    target_stem = Path(link_target).stem
    if target_stem:
        similar = find_similar_files(target_stem, docs_path)
        if similar and not suggestions:
            suggestions.append("相似文件:")
            for s in similar[:3]:
                suggestions.append(f"  - `{s}`")
    
    if not suggestions:
        suggestions.append("文件不存在，请检查路径是否正确或创建该文件")
    
    return "\n".join(suggestions)

def main():
    print("=" * 60)
    print("  Markdown 内部链接检查工具")
    print("=" * 60)
    print()
    
    # 获取所有 Markdown 文件
    md_files = get_all_markdown_files(DOCS_PATH)
    total_files = len(md_files)
    print(f"找到 {total_files} 个 Markdown 文件需要检查")
    print()
    
    # 统计数据
    total_links = 0
    valid_links = 0
    broken_links = 0
    
    # 按文件分组的断链信息
    broken_by_file = defaultdict(list)
    
    # 检查每个文件
    for idx, md_file in enumerate(md_files, 1):
        if idx % 100 == 0:
            print(f"  进度: {idx}/{total_files} 文件...")
        
        try:
            content = md_file.read_text(encoding='utf-8')
        except Exception as e:
            print(f"  警告: 无法读取文件 {md_file}: {e}")
            continue
        
        # 查找所有链接
        matches = LINK_PATTERN.findall(content)
        
        for link_text, link_target in matches:
            total_links += 1
            
            # 解析链接
            resolved_path = resolve_link(link_target, md_file, DOCS_PATH)
            
            if resolved_path is None:
                # 锚点链接，跳过
                total_links -= 1
                continue
            
            # 检查链接是否存在
            exists, actual_path = check_link_exists(resolved_path)
            
            if exists:
                valid_links += 1
            else:
                broken_links += 1
                rel_file_path = md_file.relative_to(DOCS_PATH).as_posix()
                broken_by_file[rel_file_path].append({
                    'link_text': link_text,
                    'link_target': link_target,
                    'resolved_path': str(resolved_path),
                    'suggestion': analyze_broken_link(link_target, resolved_path, md_file, DOCS_PATH)
                })
    
    # 输出统计结果
    print()
    print("=" * 60)
    print("  检查结果统计")
    print("=" * 60)
    print(f"总检查文件数: {total_files}")
    print(f"总检查链接数: {total_links}")
    print(f"有效链接数: {valid_links}")
    print(f"断链数量: {broken_links}")
    print()
    
    # 生成报告
    report_lines = []
    report_lines.append("# Markdown 内部链接检查报告")
    report_lines.append("")
    report_lines.append(f"**扫描时间:** {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
    report_lines.append("")
    report_lines.append("## 统计信息")
    report_lines.append("")
    report_lines.append(f"- **总检查文件数:** {total_files}")
    report_lines.append(f"- **总检查链接数:** {total_links}")
    report_lines.append(f"- **有效链接数:** {valid_links}")
    report_lines.append(f"- **断链数量:** {broken_links}")
    report_lines.append("")
    
    if broken_links == 0:
        print("✓ 恭喜！未发现断链。")
        report_lines.append("## 检查结果")
        report_lines.append("")
        report_lines.append("✓ **恭喜！未发现断链。**")
    else:
        print(f"✗ 发现 {broken_links} 个断链！")
        print()
        print("=" * 60)
        print("  断链详情（按文件分组）")
        print("=" * 60)
        print()
        
        report_lines.append("## 断链详情（按文件分组）")
        report_lines.append("")
        
        for file_path, links in sorted(broken_by_file.items()):
            print(f"文件: {file_path}")
            print(f"  位置: {DOCS_PATH / file_path}")
            print()
            
            report_lines.append(f"### `{file_path}`")
            report_lines.append("")
            
            for link in links:
                print(f"  • 链接文本: \"{link['link_text']}\"")
                print(f"    链接目标: `{link['link_target']}`")
                print(f"    解析路径: {link['resolved_path']}")
                print(f"    修复建议:")
                for line in link['suggestion'].split('\n'):
                    print(f"      {line}")
                print()
                
                report_lines.append(f"- **链接文本:** `{link['link_text']}`")
                report_lines.append(f"  - **链接目标:** `{link['link_target']}`")
                report_lines.append(f"  - **解析路径:** `{link['resolved_path']}`")
                report_lines.append(f"  - **修复建议:**")
                for line in link['suggestion'].split('\n'):
                    report_lines.append(f"    - {line}")
                report_lines.append("")
            
            print()
        
        # 添加修复建议汇总
        report_lines.append("## 修复建议汇总")
        report_lines.append("")
        report_lines.append("### 常见修复方案")
        report_lines.append("")
        report_lines.append("1. **添加 .md 扩展名**")
        report_lines.append("   - 如果链接指向一个 Markdown 文件但没有扩展名，添加 `.md`")
        report_lines.append("")
        report_lines.append("2. **修正相对路径**")
        report_lines.append("   - `./file.md` - 同一目录下的文件")
        report_lines.append("   - `../file.md` - 上级目录的文件")
        report_lines.append("   - `subdir/file.md` - 子目录的文件")
        report_lines.append("")
        report_lines.append("3. **使用绝对路径**")
        report_lines.append("   - `/path/to/file.md` - 相对于 docs 目录的绝对路径")
        report_lines.append("")
        report_lines.append("4. **创建缺失的文件**")
        report_lines.append("   - 如果文件确实不存在，需要创建它或更新链接指向正确的文件")
        report_lines.append("")
    
    # 保存报告到文件
    report_content = "\n".join(report_lines)
    REPORT_FILE.write_text(report_content, encoding='utf-8')
    print(f"\n详细报告已保存到: {REPORT_FILE}")
    
    # 同时保存 JSON 格式的报告
    json_report = {
        'scan_time': datetime.now().isoformat(),
        'total_files': total_files,
        'total_links': total_links,
        'valid_links': valid_links,
        'broken_links': broken_links,
        'broken_by_file': dict(broken_by_file)
    }
    JSON_REPORT.write_text(json.dumps(json_report, indent=2, ensure_ascii=False), encoding='utf-8')
    print(f"JSON 报告已保存到: {JSON_REPORT}")

if __name__ == "__main__":
    main()
