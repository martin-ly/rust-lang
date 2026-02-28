#!/usr/bin/env python3
"""
检查项目中所有Markdown文件中的链接
"""
import re
import os
from pathlib import Path
from collections import defaultdict

def find_all_markdown_files(root_dir):
    """查找所有Markdown文件"""
    md_files = []
    for path in Path(root_dir).rglob('*.md'):
        md_files.append(str(path))
    return sorted(md_files)

def extract_links(content, file_path):
    """从Markdown内容中提取所有链接"""
    # 匹配Markdown链接: [text](url) 和 [text](./path) 和 [text](../path)
    link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
    links = re.findall(link_pattern, content)
    
    # 也匹配HTML中的链接
    html_link_pattern = r'<a\s+href=["\']([^"\']+)["\'][^>]*>'
    html_links = re.findall(html_link_pattern, content)
    
    result = []
    for text, url in links:
        result.append({
            'text': text,
            'url': url,
            'line': get_line_number(content, text, url),
            'type': 'markdown'
        })
    
    for url in html_links:
        result.append({
            'text': '',
            'url': url,
            'line': get_line_number(content, '', url),
            'type': 'html'
        })
    
    return result

def get_line_number(content, text, url):
    """获取链接所在的行号"""
    search = f'[{text}]({url})' if text else f'href="{url}"'
    lines = content.split('\n')
    for i, line in enumerate(lines, 1):
        if search in line:
            return i
    return 0

def resolve_link(url, base_file):
    """解析链接为绝对路径"""
    # 忽略外部链接和锚点链接
    if url.startswith('http://') or url.startswith('https://') or \
       url.startswith('mailto:') or url.startswith('#'):
        return None, 'external'
    
    # 忽略纯锚点
    if url.startswith('#'):
        return None, 'anchor'
    
    # 获取基础目录
    base_dir = os.path.dirname(base_file)
    
    # 处理相对路径
    if url.startswith('./'):
        resolved = os.path.normpath(os.path.join(base_dir, url[2:]))
        return resolved, 'relative'
    elif url.startswith('../'):
        resolved = os.path.normpath(os.path.join(base_dir, url))
        return resolved, 'parent'
    elif url.startswith('/'):
        # 相对于项目根目录
        resolved = os.path.normpath(os.path.join(os.path.dirname(__file__), url[1:]))
        return resolved, 'root'
    else:
        # 同级目录
        resolved = os.path.normpath(os.path.join(base_dir, url))
        return resolved, 'sibling'

def check_link(url, base_file):
    """检查链接是否有效"""
    resolved, link_type = resolve_link(url, base_file)
    
    if resolved is None:
        return {'valid': True, 'type': link_type, 'path': url}
    
    # 处理带锚点的链接
    if '#' in resolved:
        resolved = resolved.split('#')[0]
        if not resolved:  # 纯锚点
            return {'valid': True, 'type': 'anchor', 'path': url}
    
    exists = os.path.exists(resolved)
    is_archive = 'archive' in resolved.lower() or 'archive' in url.lower()
    
    return {
        'valid': exists,
        'type': link_type,
        'path': resolved,
        'url': url,
        'is_archive': is_archive
    }

def main():
    root_dir = os.path.dirname(os.path.abspath(__file__))
    
    print("=" * 80)
    print("Markdown 链接检查报告")
    print("=" * 80)
    print(f"项目根目录: {root_dir}")
    print()
    
    # 查找所有Markdown文件
    md_files = find_all_markdown_files(root_dir)
    print(f"找到 {len(md_files)} 个Markdown文件")
    print()
    
    # 统计数据
    stats = {
        'total_links': 0,
        'broken_links': 0,
        'archive_links': 0,
        'external_links': 0,
        'valid_links': 0
    }
    
    broken_links = []
    archive_links = []
    
    for md_file in md_files:
        try:
            with open(md_file, 'r', encoding='utf-8') as f:
                content = f.read()
        except Exception as e:
            print(f"警告: 无法读取文件 {md_file}: {e}")
            continue
        
        links = extract_links(content, md_file)
        
        for link in links:
            url = link['url']
            stats['total_links'] += 1
            
            result = check_link(url, md_file)
            
            if result['type'] == 'external':
                stats['external_links'] += 1
                continue
            elif result['type'] == 'anchor':
                stats['valid_links'] += 1
                continue
            
            if not result['valid']:
                stats['broken_links'] += 1
                broken_links.append({
                    'source': md_file,
                    'url': url,
                    'text': link['text'],
                    'line': link['line'],
                    'type': result['type'],
                    'resolved_path': result['path']
                })
            elif result['is_archive']:
                stats['archive_links'] += 1
                archive_links.append({
                    'source': md_file,
                    'url': url,
                    'text': link['text'],
                    'line': link['line'],
                    'type': result['type'],
                    'resolved_path': result['path']
                })
            else:
                stats['valid_links'] += 1
    
    # 打印统计
    print("=" * 80)
    print("统计摘要")
    print("=" * 80)
    print(f"总链接数: {stats['total_links']}")
    print(f"有效链接: {stats['valid_links']}")
    print(f"外部链接: {stats['external_links']}")
    print(f"断链数量: {stats['broken_links']}")
    print(f"指向归档的链接: {stats['archive_links']}")
    print()
    
    # 打印断链详情
    if broken_links:
        print("=" * 80)
        print("断链详情")
        print("=" * 80)
        print()
        
        # 按源文件分组
        by_source = defaultdict(list)
        for link in broken_links:
            by_source[link['source']].append(link)
        
        for source, links in sorted(by_source.items()):
            rel_source = os.path.relpath(source, root_dir)
            print(f"\n文件: {rel_source}")
            print("-" * 60)
            for link in links:
                print(f"  行 {link['line']}: [{link['text']}] ({link['url']})")
                print(f"    类型: {link['type']}")
                print(f"    解析路径: {os.path.relpath(link['resolved_path'], root_dir)}")
                
                # 建议修复方式
                if link['url'].startswith('../'):
                    print(f"    建议: 检查上级目录路径是否正确")
                elif link['url'].startswith('./'):
                    print(f"    建议: 检查同级目录路径是否正确")
                else:
                    print(f"    建议: 检查相对路径是否正确")
                print()
    
    # 打印指向归档的链接
    if archive_links:
        print("\n" + "=" * 80)
        print("指向归档目录的链接")
        print("=" * 80)
        print()
        
        # 按源文件分组
        by_source = defaultdict(list)
        for link in archive_links:
            by_source[link['source']].append(link)
        
        for source, links in sorted(by_source.items()):
            rel_source = os.path.relpath(source, root_dir)
            print(f"\n文件: {rel_source}")
            print("-" * 60)
            for link in links:
                print(f"  行 {link['line']}: [{link['text']}] ({link['url']})")
                print(f"    解析路径: {os.path.relpath(link['resolved_path'], root_dir)}")
                print(f"    建议: 考虑更新链接到非归档位置或移除")
                print()
    
    # 保存详细报告
    report_path = os.path.join(root_dir, 'BROKEN_LINKS_REPORT.md')
    with open(report_path, 'w', encoding='utf-8') as f:
        f.write("# Markdown 链接检查报告\n\n")
        f.write(f"生成时间: {os.popen('date').read().strip() if os.name != 'nt' else 'N/A'}\n\n")
        
        f.write("## 统计摘要\n\n")
        f.write(f"- 总链接数: {stats['total_links']}\n")
        f.write(f"- 有效链接: {stats['valid_links']}\n")
        f.write(f"- 外部链接: {stats['external_links']}\n")
        f.write(f"- 断链数量: {stats['broken_links']}\n")
        f.write(f"- 指向归档的链接: {stats['archive_links']}\n\n")
        
        if broken_links:
            f.write("## 断链详情\n\n")
            by_source = defaultdict(list)
            for link in broken_links:
                by_source[link['source']].append(link)
            
            for source, links in sorted(by_source.items()):
                rel_source = os.path.relpath(source, root_dir)
                f.write(f"### {rel_source}\n\n")
                for link in links:
                    f.write(f"- **行 {link['line']}**: `[{link['text']}]({link['url']})`\n")
                    f.write(f"  - 类型: {link['type']}\n")
                    f.write(f"  - 解析路径: `{os.path.relpath(link['resolved_path'], root_dir)}`\n")
                    f.write(f"  - 建议: 检查路径是否正确\n\n")
        
        if archive_links:
            f.write("## 指向归档目录的链接\n\n")
            by_source = defaultdict(list)
            for link in archive_links:
                by_source[link['source']].append(link)
            
            for source, links in sorted(by_source.items()):
                rel_source = os.path.relpath(source, root_dir)
                f.write(f"### {rel_source}\n\n")
                for link in links:
                    f.write(f"- **行 {link['line']}**: `[{link['text']}]({link['url']})`\n")
                    f.write(f"  - 解析路径: `{os.path.relpath(link['resolved_path'], root_dir)}`\n")
                    f.write(f"  - 建议: 考虑更新链接到非归档位置\n\n")
    
    print(f"\n详细报告已保存到: {report_path}")

if __name__ == '__main__':
    main()
