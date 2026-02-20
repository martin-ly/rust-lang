#!/usr/bin/env python3
"""
检查 docs/ 目录下所有 Markdown 文件的本地链接有效性
"""
import re
import os
from pathlib import Path
from collections import defaultdict
from urllib.parse import urlparse

def find_all_md_files(base_path):
    """递归查找所有 Markdown 文件"""
    md_files = []
    for root, dirs, files in os.walk(base_path):
        # 跳过 .git 目录
        dirs[:] = [d for d in dirs if d != '.git']
        for f in files:
            if f.endswith('.md'):
                md_files.append(Path(root) / f)
    return md_files

def extract_links(content, file_path):
    """从 Markdown 内容中提取所有链接"""
    links = []
    
    # 匹配 [text](url) 格式
    pattern = r'\[([^\]]+)\]\(([^)]+)\)'
    matches = re.findall(pattern, content)
    
    for text, url in matches:
        links.append({
            'text': text,
            'url': url,
            'type': 'markdown'
        })
    
    # 匹配 <url> 格式 (自动链接)
    auto_link_pattern = r'<(https?://[^>]+)>'
    auto_matches = re.findall(auto_link_pattern, content)
    for url in auto_matches:
        links.append({
            'text': url,
            'url': url,
            'type': 'autolink'
        })
    
    return links

def is_external_link(url):
    """判断是否为外部链接"""
    parsed = urlparse(url)
    return bool(parsed.scheme and parsed.netloc)

def resolve_link(url, source_file, docs_base):
    """
    解析链接路径，返回绝对路径
    """
    # 去除锚点
    if '#' in url:
        url = url.split('#')[0]
    
    # 空路径（仅锚点）
    if not url:
        return None
    
    # 外部链接
    if is_external_link(url):
        return None
    
    # 绝对路径（从 docs 根目录开始）
    if url.startswith('/'):
        return docs_base / url.lstrip('/')
    
    # 相对路径
    source_dir = source_file.parent
    resolved = (source_dir / url).resolve()
    return resolved

def check_anchor(content, anchor):
    """检查锚点是否存在于文件中"""
    if not anchor:
        return True
    
    # 将锚点转换为标题格式
    anchor_lower = anchor.lower()
    
    # 检查各种标题格式
    # 1. Markdown 标题
    header_pattern = r'^#{1,6}\s+(.+)$'
    headers = re.findall(header_pattern, content, re.MULTILINE)
    for h in headers:
        # 生成锚点ID (GitHub 风格)
        header_anchor = re.sub(r'[^\w\s-]', '', h).strip().lower().replace(' ', '-')
        if header_anchor == anchor_lower:
            return True
    
    # 2. HTML 锚点
    anchor_pattern = r'<a[^>]*id=["\']([^"\']+)["\']'
    anchors = re.findall(anchor_pattern, content)
    if anchor_lower in [a.lower() for a in anchors]:
        return True
    
    # 3. name 属性
    name_pattern = r'<a[^>]*name=["\']([^"\']+)["\']'
    names = re.findall(name_pattern, content)
    if anchor_lower in [n.lower() for n in names]:
        return True
    
    return False

def main():
    docs_base = Path('e:/_src/rust-lang/docs')
    
    print(f"正在扫描 {docs_base} 下的 Markdown 文件...")
    md_files = find_all_md_files(docs_base)
    print(f"找到 {len(md_files)} 个 Markdown 文件")
    
    stats = {
        'total': 0,
        'valid': 0,
        'broken': 0,
        'external': 0,
        'anchor_only': 0
    }
    
    broken_links = []
    file_contents = {}  # 缓存文件内容用于锚点检查
    
    # 首先读取所有文件内容
    for md_file in md_files:
        try:
            with open(md_file, 'r', encoding='utf-8') as f:
                file_contents[md_file] = f.read()
        except Exception as e:
            print(f"警告: 无法读取 {md_file}: {e}")
    
    # 检查链接
    for md_file in md_files:
        content = file_contents.get(md_file, '')
        links = extract_links(content, md_file)
        
        for link in links:
            url = link['url']
            stats['total'] += 1
            
            # 外部链接
            if is_external_link(url):
                stats['external'] += 1
                continue
            
            # 分离路径和锚点
            anchor = None
            if '#' in url:
                parts = url.split('#', 1)
                url_path = parts[0]
                anchor = parts[1] if len(parts) > 1 else None
            else:
                url_path = url
            
            # 仅锚点链接（如 #section）
            if not url_path and anchor:
                stats['anchor_only'] += 1
                # 检查同文件锚点
                if not check_anchor(content, anchor):
                    stats['broken'] += 1
                    broken_links.append({
                        'source': md_file.relative_to(docs_base.parent),
                        'text': link['text'],
                        'url': link['url'],
                        'problem': f'同文件锚点不存在: #{anchor}'
                    })
                else:
                    stats['valid'] += 1
                continue
            
            # 解析目标路径
            target = resolve_link(url_path, md_file, docs_base)
            if target is None:
                continue
            
            # 检查文件是否存在
            if not target.exists():
                stats['broken'] += 1
                broken_links.append({
                    'source': md_file.relative_to(docs_base.parent),
                    'text': link['text'],
                    'url': link['url'],
                    'problem': f'文件不存在: {target.relative_to(docs_base.parent) if docs_base.parent in target.parents else target}'
                })
                continue
            
            # 检查锚点
            if anchor:
                target_content = file_contents.get(target, '')
                if not target_content:
                    try:
                        with open(target, 'r', encoding='utf-8') as f:
                            target_content = f.read()
                            file_contents[target] = target_content
                    except Exception as e:
                        stats['broken'] += 1
                        broken_links.append({
                            'source': md_file.relative_to(docs_base.parent),
                            'text': link['text'],
                            'url': link['url'],
                            'problem': f'无法读取目标文件: {e}'
                        })
                        continue
                
                if not check_anchor(target_content, anchor):
                    stats['broken'] += 1
                    broken_links.append({
                        'source': md_file.relative_to(docs_base.parent),
                        'text': link['text'],
                        'url': link['url'],
                        'problem': f'锚点不存在: #{anchor}'
                    })
                    continue
            
            stats['valid'] += 1
    
    # 生成报告
    report_lines = []
    report_lines.append("# 链接有效性检查报告")
    report_lines.append("")
    report_lines.append("## 统计")
    report_lines.append("| 类别 | 数量 |")
    report_lines.append("|:---|:---:|")
    report_lines.append(f"| 总链接数 | {stats['total']} |")
    report_lines.append(f"| 有效链接 | {stats['valid']} |")
    report_lines.append(f"| 损坏链接 | {stats['broken']} |")
    report_lines.append(f"| 外部链接 | {stats['external']} |")
    report_lines.append(f"| 仅锚点链接 | {stats['anchor_only']} |")
    report_lines.append("")
    
    # 按问题类型分组
    problems_by_type = defaultdict(list)
    for bl in broken_links:
        # 提取问题类型
        if '文件不存在' in bl['problem']:
            problem_type = '文件不存在'
        elif '锚点不存在' in bl['problem']:
            problem_type = '锚点不存在'
        elif '无法读取' in bl['problem']:
            problem_type = '文件读取失败'
        elif '同文件锚点不存在' in bl['problem']:
            problem_type = '同文件锚点不存在'
        else:
            problem_type = '其他'
        problems_by_type[problem_type].append(bl)
    
    report_lines.append("## 损坏链接清单（按问题类型分组）")
    report_lines.append("")
    
    for ptype, items in sorted(problems_by_type.items(), key=lambda x: -len(x[1])):
        report_lines.append(f"### {ptype} ({len(items)}个)")
        report_lines.append("")
        report_lines.append("| 源文件 | 链接文本 | 链接路径 | 问题 |")
        report_lines.append("|:---|:---|:---|:---|")
        for bl in items:
            # 转义表格中的管道符号
            text = bl['text'].replace('|', '\\|')
            url = bl['url'].replace('|', '\\|')
            problem = bl['problem'].replace('|', '\\|')
            report_lines.append(f"| {bl['source']} | {text} | `{url}` | {problem} |")
        report_lines.append("")
    
    # 修复建议
    report_lines.append("## 修复建议")
    report_lines.append("")
    report_lines.append("### 1. 文件不存在问题")
    report_lines.append("- 检查链接路径是否正确")
    report_lines.append("- 确认目标文件是否已被移动或删除")
    report_lines.append("- 更新链接指向正确的文件位置")
    report_lines.append("")
    report_lines.append("### 2. 锚点不存在问题")
    report_lines.append("- 检查锚点ID是否与目标文件中的标题匹配")
    report_lines.append("- GitHub风格锚点：将标题转换为小写，空格替换为连字符，移除标点")
    report_lines.append("- 示例：`## Hello World!` -> `#hello-world`")
    report_lines.append("")
    report_lines.append("### 3. 同文件锚点问题")
    report_lines.append("- 检查文档中是否存在对应的标题")
    report_lines.append("- 可能是文档结构已更改但目录未更新")
    report_lines.append("")
    
    # 汇总统计
    report_lines.append("## 源文件问题统计")
    report_lines.append("")
    source_file_counts = defaultdict(int)
    for bl in broken_links:
        source_file_counts[bl['source']] += 1
    
    report_lines.append("| 源文件 | 损坏链接数 |")
    report_lines.append("|:---|:---:|")
    for src, count in sorted(source_file_counts.items(), key=lambda x: -x[1])[:50]:
        report_lines.append(f"| {src} | {count} |")
    
    if len(source_file_counts) > 50:
        report_lines.append(f"| ... 还有 {len(source_file_counts) - 50} 个文件 | |")
    
    report_lines.append("")
    report_lines.append(f"**总计 {len(source_file_counts)} 个文件包含损坏链接**")
    
    # 写入报告文件
    report_path = Path('e:/_src/rust-lang/docs/LINK_CHECK_REPORT.md')
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(report_lines))
    
    print(f"\n报告已保存到: {report_path}")
    print(f"\n摘要:")
    print(f"  - 总链接数: {stats['total']}")
    print(f"  - 有效链接: {stats['valid']}")
    print(f"  - 损坏链接: {stats['broken']}")
    print(f"  - 外部链接: {stats['external']}")
    print(f"  - 仅锚点链接: {stats['anchor_only']}")
    print(f"  - 问题文件数: {len(source_file_counts)}")
    
    return stats, broken_links

if __name__ == '__main__':
    main()
