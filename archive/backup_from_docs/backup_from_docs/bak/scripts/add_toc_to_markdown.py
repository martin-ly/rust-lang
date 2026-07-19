#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
为Markdown文件自动添加目录(Table of Contents)

功能：
1. 扫描所有.md文件
2. 检测是否已有目录
3. 自动生成目录
4. 插入到文件开头
"""

import os
import re
from pathlib import Path
from typing import List, Tuple, Optional

class MarkdownTOCGenerator:
    def __init__(self, root_dir: str):
        self.root_dir = Path(root_dir)
        self.stats = {
            'total': 0,
            'with_toc': 0,
            'without_toc': 0,
            'added_toc': 0,
            'skipped': 0,
            'errors': 0
        }
        
    def has_toc(self, content: str) -> bool:
        """检测文档是否已有目录"""
        # 常见的目录标识
        toc_patterns = [
            r'##?\s*目录',
            r'##?\s*📊\s*目录',
            r'##?\s*Table of Contents',
            r'##?\s*TOC',
            r'<!-- TOC -->',
            r'\[TOC\]',
        ]
        
        for pattern in toc_patterns:
            if re.search(pattern, content, re.IGNORECASE):
                return True
        return False
    
    def extract_headers(self, content: str) -> List[Tuple[int, str, str]]:
        """提取所有标题
        返回: [(level, title, anchor), ...]
        """
        headers = []
        lines = content.split('\n')
        
        for line in lines:
            # 匹配 Markdown 标题
            match = re.match(r'^(#{1,6})\s+(.+)$', line)
            if match:
                level = len(match.group(1))
                title = match.group(2).strip()
                
                # 跳过第一级标题（文档标题）
                if level == 1:
                    continue
                
                # 生成锚点
                anchor = self.generate_anchor(title)
                headers.append((level, title, anchor))
        
        return headers
    
    def generate_anchor(self, title: str) -> str:
        """生成GitHub风格的锚点"""
        # 移除emoji和特殊字符
        anchor = re.sub(r'[^\w\s\u4e00-\u9fff-]', '', title)
        # 转小写并替换空格为-
        anchor = anchor.lower().strip().replace(' ', '-')
        # 移除连续的-
        anchor = re.sub(r'-+', '-', anchor)
        return anchor
    
    def generate_toc(self, headers: List[Tuple[int, str, str]]) -> str:
        """生成目录内容"""
        if not headers:
            return ""
        
        toc_lines = ["## 📊 目录\n"]
        
        for level, title, anchor in headers:
            # 缩进（从二级标题开始，二级标题不缩进）
            indent = "  " * (level - 2)
            toc_lines.append(f"{indent}- [{title}](#{anchor})")
        
        toc_lines.append("")  # 空行
        return "\n".join(toc_lines)
    
    def should_skip_file(self, file_path: Path) -> bool:
        """判断是否应该跳过该文件"""
        skip_patterns = [
            'README.md',
            'CHANGELOG.md',
            'LICENSE.md',
            'CONTRIBUTING.md',
            '/target/',
            '/node_modules/',
            '/.git/',
        ]
        
        file_str = str(file_path)
        for pattern in skip_patterns:
            if pattern in file_str:
                return True
        return False
    
    def add_toc_to_file(self, file_path: Path, dry_run: bool = False) -> bool:
        """为文件添加目录
        
        Args:
            file_path: 文件路径
            dry_run: 如果为True，只检测不修改
            
        Returns:
            是否成功添加
        """
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 检查是否已有目录
            if self.has_toc(content):
                self.stats['with_toc'] += 1
                return False
            
            self.stats['without_toc'] += 1
            
            # 提取标题
            headers = self.extract_headers(content)
            
            # 如果标题太少，跳过
            if len(headers) < 3:
                self.stats['skipped'] += 1
                return False
            
            # 生成目录
            toc = self.generate_toc(headers)
            
            if not toc:
                self.stats['skipped'] += 1
                return False
            
            # 找到插入位置（在文档元信息之后）
            lines = content.split('\n')
            insert_pos = 0
            
            # 跳过文档标题和元信息
            for i, line in enumerate(lines):
                if i == 0 and line.startswith('#'):
                    insert_pos = i + 1
                    continue
                if line.startswith('>'):
                    insert_pos = i + 1
                    continue
                if line.strip() == '---':
                    insert_pos = i + 1
                    continue
                if line.strip() == '':
                    continue
                break
            
            # 跳过空行
            while insert_pos < len(lines) and lines[insert_pos].strip() == '':
                insert_pos += 1
            
            if not dry_run:
                # 插入目录
                new_content = '\n'.join(lines[:insert_pos]) + '\n\n' + toc + '\n' + '\n'.join(lines[insert_pos:])
                
                with open(file_path, 'w', encoding='utf-8') as f:
                    f.write(new_content)
                
                self.stats['added_toc'] += 1
                print(f"✅ Added TOC: {file_path}")
            else:
                print(f"🔍 Would add TOC: {file_path}")
            
            return True
            
        except Exception as e:
            self.stats['errors'] += 1
            print(f"❌ Error processing {file_path}: {e}")
            return False
    
    def process_directory(self, directory: str = None, dry_run: bool = False):
        """处理整个目录"""
        if directory is None:
            directory = self.root_dir
        else:
            directory = Path(directory)
        
        print(f"\n{'='*60}")
        print(f"扫描目录: {directory}")
        print(f"模式: {'检测模式 (不修改)' if dry_run else '修改模式'}")
        print(f"{'='*60}\n")
        
        md_files = list(directory.rglob('*.md'))
        self.stats['total'] = len(md_files)
        
        for md_file in md_files:
            if self.should_skip_file(md_file):
                continue
            
            self.add_toc_to_file(md_file, dry_run)
        
        self.print_stats()
    
    def print_stats(self):
        """打印统计信息"""
        print(f"\n{'='*60}")
        print("统计结果")
        print(f"{'='*60}")
        print(f"总文件数:       {self.stats['total']}")
        print(f"已有目录:       {self.stats['with_toc']}")
        print(f"缺少目录:       {self.stats['without_toc']}")
        print(f"添加目录:       {self.stats['added_toc']}")
        print(f"跳过文件:       {self.stats['skipped']} (标题太少或特殊文件)")
        print(f"处理错误:       {self.stats['errors']}")
        print(f"{'='*60}\n")


def main():
    import argparse
    
    parser = argparse.ArgumentParser(
        description='为Markdown文件自动添加目录',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
示例:
  # 检测模式（不修改文件）
  python add_toc_to_markdown.py --dry-run
  
  # 实际添加目录
  python add_toc_to_markdown.py
  
  # 指定目录
  python add_toc_to_markdown.py --dir crates/c01_ownership_borrow_scope
        """
    )
    
    parser.add_argument(
        '--dir',
        default='.',
        help='要处理的目录（默认: 当前目录）'
    )
    
    parser.add_argument(
        '--dry-run',
        action='store_true',
        help='检测模式，只显示会修改什么，不实际修改文件'
    )
    
    args = parser.parse_args()
    
    generator = MarkdownTOCGenerator(args.dir)
    generator.process_directory(dry_run=args.dry_run)


if __name__ == '__main__':
    main()

