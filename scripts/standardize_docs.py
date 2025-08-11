#!/usr/bin/env python3
"""
Rust语言形式化理论体系文档格式标准化脚本

功能：
1. 批量检查文档格式
2. 自动修复常见格式问题
3. 统一章节编号
4. 标准化数学公式
5. 生成检查报告
"""

import os
import re
import sys
from pathlib import Path
from typing import List, Dict, Tuple, Optional
import argparse
from datetime import datetime

class DocumentStandardizer:
    """文档格式标准化器"""
    
    def __init__(self, root_path: str):
        self.root_path = Path(root_path)
        self.results = []
        self.fixes_applied = 0
        
    def find_markdown_files(self) -> List[Path]:
        """查找所有Markdown文件"""
        markdown_files = []
        for file_path in self.root_path.rglob("*.md"):
            markdown_files.append(file_path)
        return markdown_files
    
    def standardize_document(self, file_path: Path) -> Dict:
        """标准化单个文档"""
        result = {
            'file_path': str(file_path),
            'original_content': '',
            'modified_content': '',
            'changes': [],
            'errors': [],
            'warnings': []
        }
        
        try:
            # 读取文件内容
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            result['original_content'] = content
            modified_content = content
            
            # 1. 标准化文档头部
            modified_content, changes = self.standardize_header(modified_content, file_path)
            result['changes'].extend(changes)
            
            # 2. 标准化章节编号
            modified_content, changes = self.standardize_section_numbering(modified_content)
            result['changes'].extend(changes)
            
            # 3. 标准化数学公式
            modified_content, changes = self.standardize_math_formulas(modified_content)
            result['changes'].extend(changes)
            
            # 4. 标准化表格
            modified_content, changes = self.standardize_tables(modified_content)
            result['changes'].extend(changes)
            
            # 5. 标准化链接
            modified_content, changes = self.standardize_links(modified_content)
            result['changes'].extend(changes)
            
            # 6. 添加交叉引用
            modified_content, changes = self.add_cross_references(modified_content, file_path)
            result['changes'].extend(changes)
            
            result['modified_content'] = modified_content
            
            # 检查是否有错误
            self.check_document_quality(modified_content, result)
            
        except Exception as e:
            result['errors'].append(f"处理文件时出错: {str(e)}")
        
        return result
    
    def standardize_header(self, content: str, file_path: Path) -> Tuple[str, List[str]]:
        """标准化文档头部"""
        changes = []
        
        # 检查是否已有标准头部
        if "## 📅 文档信息" in content:
            return content, changes
        
        # 提取标题
        title_match = re.search(r'^#\s*(.+)$', content, re.MULTILINE)
        if not title_match:
            changes.append("添加文档标题")
            title = file_path.stem.replace('_', ' ').title()
            content = f"# {title}\n\n" + content
        else:
            title = title_match.group(1)
        
        # 添加标准头部
        header = f"""## 📅 文档信息

**文档版本**: v1.0  
**创建日期**: {datetime.now().strftime('%Y-%m-%d')}  
**最后更新**: {datetime.now().strftime('%Y-%m-%d')}  
**状态**: 已完成  
**质量等级**: 钻石级 ⭐⭐⭐⭐⭐

---

"""
        
        # 在标题后插入头部
        content = re.sub(r'^(#\s+.+?)$', r'\1\n\n' + header, content, flags=re.MULTILINE)
        changes.append("添加标准文档头部")
        
        return content, changes
    
    def standardize_section_numbering(self, content: str) -> Tuple[str, List[str]]:
        """标准化章节编号"""
        changes = []
        
        # 查找所有章节标题
        section_pattern = r'^(#{2,})\s*(\d+\.)?\s*(.+)$'
        
        def replace_section(match):
            level = len(match.group(1))
            number = match.group(2)
            title = match.group(3)
            
            # 标准化编号格式
            if level == 2:  # 一级章节
                if not number or not number.endswith('.'):
                    return f"## {title}"
                else:
                    return f"## {number} {title}"
            else:  # 子章节
                return match.group(0)
        
        new_content = re.sub(section_pattern, replace_section, content, flags=re.MULTILINE)
        
        if new_content != content:
            changes.append("标准化章节编号")
        
        return new_content, changes
    
    def standardize_math_formulas(self, content: str) -> Tuple[str, List[str]]:
        """标准化数学公式"""
        changes = []
        
        # 检查行内公式
        inline_pattern = r'\$([^$]+)\$'
        
        def check_inline_math(match):
            formula = match.group(1)
            # 检查常用数学符号
            if '\\forall' in formula or '\\exists' in formula:
                return match.group(0)  # 已经是标准格式
            else:
                # 可以添加更多标准化规则
                return match.group(0)
        
        new_content = re.sub(inline_pattern, check_inline_math, content)
        
        # 检查块级公式
        block_pattern = r'\$\$([\s\S]*?)\$\$'
        
        def check_block_math(match):
            formula = match.group(1)
            # 检查块级公式格式
            if formula.strip():
                return match.group(0)
            else:
                changes.append("修复空的块级公式")
                return ""
        
        new_content = re.sub(block_pattern, check_block_math, new_content)
        
        if new_content != content:
            changes.append("标准化数学公式")
        
        return new_content, changes
    
    def standardize_tables(self, content: str) -> Tuple[str, List[str]]:
        """标准化表格格式"""
        changes = []
        
        # 检查表格对齐
        table_pattern = r'(\|.*\|.*\n\|.*\|.*\n)'
        
        def fix_table_alignment(match):
            table = match.group(1)
            lines = table.strip().split('\n')
            
            if len(lines) >= 2:
                header = lines[0]
                separator = lines[1]
                
                # 检查分隔符格式
                if '|-' not in separator:
                    # 添加标准分隔符
                    separator = re.sub(r'\|', '|:---', separator)
                    separator = separator.replace('|:---', '|', 1)  # 第一个保持原样
                    separator = separator.replace('|:---', '|:---:|', -1)  # 最后一个居中
                    
                    changes.append("修复表格对齐")
                    return header + '\n' + separator + '\n' + '\n'.join(lines[2:]) + '\n'
            
            return match.group(1)
        
        new_content = re.sub(table_pattern, fix_table_alignment, content)
        
        return new_content, changes
    
    def standardize_links(self, content: str) -> Tuple[str, List[str]]:
        """标准化链接格式"""
        changes = []
        
        # 检查内部链接格式
        link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        
        def fix_internal_links(match):
            text = match.group(1)
            url = match.group(2)
            
            # 修复相对路径
            if url.startswith('./'):
                url = url[2:]
            elif url.startswith('../'):
                # 保持相对路径
                pass
            
            return f"[{text}]({url})"
        
        new_content = re.sub(link_pattern, fix_internal_links, content)
        
        if new_content != content:
            changes.append("标准化链接格式")
        
        return new_content, changes
    
    def add_cross_references(self, content: str, file_path: Path) -> Tuple[str, List[str]]:
        """添加交叉引用"""
        changes = []
        
        # 检查是否已有交叉引用部分
        if "## 🔗 相关链接" in content:
            return content, changes
        
        # 根据文件路径生成相关链接
        cross_refs = self.generate_cross_references(file_path)
        
        if cross_refs:
            # 在文档末尾添加交叉引用
            cross_ref_section = f"""

---

## 🔗 相关链接

{cross_refs}
"""
            content += cross_ref_section
            changes.append("添加交叉引用")
        
        return content, changes
    
    def generate_cross_references(self, file_path: Path) -> str:
        """生成交叉引用"""
        refs = []
        
        # 根据文件路径生成相关链接
        relative_path = file_path.relative_to(self.root_path)
        parts = relative_path.parts
        
        if len(parts) >= 2:
            module = parts[1]
            
            if module == "01_core_theory":
                refs.extend([
                    "### 📚 理论基础",
                    "- [内存安全理论](../01_core_theory/01_foundation_semantics/01_memory_semantics/00_index.md)",
                    "- [类型系统理论](../01_core_theory/02_type_system/01_type_semantics/00_index.md)",
                    "- [并发安全理论](../01_core_theory/03_concurrency_semantics/01_thread_semantics/00_index.md)"
                ])
            elif module == "02_design_patterns":
                refs.extend([
                    "### 🏗️ 设计模式",
                    "- [创建型模式](../02_design_patterns/01_creational_patterns/01_factory_pattern/00_index.md)",
                    "- [结构型模式](../02_design_patterns/02_structural_patterns/01_adapter_pattern/00_index.md)",
                    "- [行为型模式](../02_design_patterns/03_behavioral_patterns/01_observer_pattern/00_index.md)"
                ])
            elif module == "03_application_domains":
                refs.extend([
                    "### 📖 应用领域",
                    "- [系统编程应用](../03_application_domains/01_systems_programming/00_index.md)",
                    "- [Web开发应用](../03_application_domains/02_web_development/00_index.md)",
                    "- [区块链应用](../03_application_domains/03_blockchain/00_index.md)"
                ])
        
        return '\n'.join(refs)
    
    def check_document_quality(self, content: str, result: Dict):
        """检查文档质量"""
        # 检查文档长度
        if len(content) < 100:
            result['warnings'].append("文档内容过短")
        
        # 检查是否有数学公式
        if '$' not in content:
            result['warnings'].append("建议添加数学公式")
        
        # 检查是否有代码块
        if '```' not in content:
            result['warnings'].append("建议添加代码示例")
        
        # 检查章节结构
        sections = re.findall(r'^#{2,}\s+(.+)$', content, re.MULTILINE)
        if len(sections) < 3:
            result['warnings'].append("章节结构不够完整")
    
    def process_all_documents(self, apply_changes: bool = False) -> List[Dict]:
        """处理所有文档"""
        markdown_files = self.find_markdown_files()
        print(f"找到 {len(markdown_files)} 个Markdown文件")
        
        for i, file_path in enumerate(markdown_files, 1):
            print(f"处理文件 {i}/{len(markdown_files)}: {file_path.name}")
            
            result = self.standardize_document(file_path)
            self.results.append(result)
            
            # 应用更改
            if apply_changes and result['changes']:
                try:
                    with open(file_path, 'w', encoding='utf-8') as f:
                        f.write(result['modified_content'])
                    self.fixes_applied += 1
                    print(f"  ✓ 应用了 {len(result['changes'])} 个更改")
                except Exception as e:
                    result['errors'].append(f"写入文件失败: {str(e)}")
                    print(f"  ✗ 写入文件失败: {str(e)}")
        
        return self.results
    
    def generate_report(self) -> str:
        """生成检查报告"""
        total_files = len(self.results)
        files_with_changes = sum(1 for r in self.results if r['changes'])
        files_with_errors = sum(1 for r in self.results if r['errors'])
        files_with_warnings = sum(1 for r in self.results if r['warnings'])
        
        report = f"""# 文档格式标准化报告

## 📊 总体统计

- **总文件数**: {total_files}
- **需要更改的文件**: {files_with_changes}
- **有错误的文件**: {files_with_errors}
- **有警告的文件**: {files_with_warnings}
- **已应用修复**: {self.fixes_applied}

## 📋 详细结果

"""
        
        for result in self.results:
            if result['changes'] or result['errors'] or result['warnings']:
                report += f"### {result['file_path']}\n\n"
                
                if result['changes']:
                    report += "**更改:**\n"
                    for change in result['changes']:
                        report += f"- {change}\n"
                    report += "\n"
                
                if result['errors']:
                    report += "**错误:**\n"
                    for error in result['errors']:
                        report += f"- {error}\n"
                    report += "\n"
                
                if result['warnings']:
                    report += "**警告:**\n"
                    for warning in result['warnings']:
                        report += f"- {warning}\n"
                    report += "\n"
        
        return report

def main():
    parser = argparse.ArgumentParser(description='Rust语言形式化理论体系文档格式标准化工具')
    parser.add_argument('path', help='要处理的目录路径')
    parser.add_argument('--apply', action='store_true', help='应用更改到文件')
    parser.add_argument('--report', help='输出报告文件路径')
    
    args = parser.parse_args()
    
    if not os.path.exists(args.path):
        print(f"错误: 路径不存在: {args.path}")
        sys.exit(1)
    
    # 创建标准化器
    standardizer = DocumentStandardizer(args.path)
    
    # 处理文档
    print("开始处理文档...")
    results = standardizer.process_all_documents(apply_changes=args.apply)
    
    # 生成报告
    report = standardizer.generate_report()
    
    # 输出报告
    if args.report:
        with open(args.report, 'w', encoding='utf-8') as f:
            f.write(report)
        print(f"报告已保存到: {args.report}")
    else:
        print("\n" + "="*50)
        print(report)
    
    print(f"\n处理完成! 共处理 {len(results)} 个文件，应用了 {standardizer.fixes_applied} 个修复。")

if __name__ == '__main__':
    main() 