#!/usr/bin/env python3
"""
Rust软件工程质量检查脚本
自动检查文档质量、链接完整性、格式规范等
"""

import os
import re
import sys
from pathlib import Path
from typing import List, Dict, Tuple
import json
from datetime import datetime

class SoftwareQualityChecker:
    def __init__(self, base_path: str):
        self.base_path = Path(base_path)
        self.issues = []
        self.stats = {
            'total_files': 0,
            'checked_files': 0,
            'issues_found': 0,
            'links_checked': 0,
            'broken_links': 0
        }
    
    def check_markdown_format(self, file_path: Path) -> List[str]:
        """检查Markdown文件格式"""
        issues = []
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.split('\n')
            
            # 检查标题格式
            for i, line in enumerate(lines, 1):
                if line.startswith('#'):
                    # 检查标题层级
                    if line.startswith('##') and not line.startswith('###'):
                        if i > 1 and not lines[i-2].startswith('#'):
                            issues.append(f"第{i}行: 标题前应有空行")
                    
                    # 检查标题后空行
                    if i < len(lines) and lines[i].strip() != '':
                        issues.append(f"第{i}行: 标题后应有空行")
            
            # 检查链接格式
            link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
            links = re.findall(link_pattern, content)
            
            for link_text, link_url in links:
                self.stats['links_checked'] += 1
                
                # 检查相对链接
                if link_url.startswith('./') or not link_url.startswith(('http', '#')):
                    target_path = file_path.parent / link_url
                    if not target_path.exists():
                        issues.append(f"断链: {link_text} -> {link_url}")
                        self.stats['broken_links'] += 1
            
            # 检查代码块格式
            code_block_pattern = r'```(\w+)?\n(.*?)\n```'
            code_blocks = re.findall(code_block_pattern, content, re.DOTALL)
            
            for lang, code in code_blocks:
                if not lang and code.strip():
                    issues.append("代码块应指定语言")
        
        except Exception as e:
            issues.append(f"文件读取错误: {e}")
        
        return issues
    
    def check_file_structure(self, file_path: Path) -> List[str]:
        """检查文件结构规范"""
        issues = []
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # 检查必需章节
            required_sections = ['## 元数据', '## 摘要', '## 主要内容大纲']
            for section in required_sections:
                if section not in content:
                    issues.append(f"缺少必需章节: {section}")
            
            # 检查元数据格式
            if '## 元数据' in content:
                metadata_section = content.split('## 元数据')[1].split('##')[0]
                if '更新时间' not in metadata_section:
                    issues.append("元数据缺少更新时间")
                if '相关主题' not in metadata_section:
                    issues.append("元数据缺少相关主题")
            
            # 检查交叉引用
            if '## 交叉引用' not in content:
                issues.append("缺少交叉引用章节")
        
        except Exception as e:
            issues.append(f"文件结构检查错误: {e}")
        
        return issues
    
    def check_directory_structure(self) -> List[str]:
        """检查目录结构规范"""
        issues = []
        
        # 检查必需文件
        required_files = [
            'README.md',
            '00_MASTER_INDEX.md',
            'LEARNING_PATHS.md',
            'QUALITY_GUIDE.md'
        ]
        
        for file_name in required_files:
            file_path = self.base_path / file_name
            if not file_path.exists():
                issues.append(f"缺少必需文件: {file_name}")
        
        # 检查模块目录
        module_dirs = [d for d in self.base_path.iterdir() 
                      if d.is_dir() and d.name.startswith(('0', '1', '2', '3', '4', '5', '6', '7', '8'))]
        
        for module_dir in module_dirs:
            # 检查模块索引文件
            index_file = module_dir / '00_index.md'
            if not index_file.exists():
                issues.append(f"模块 {module_dir.name} 缺少索引文件")
            
            # 检查子目录结构
            subdirs = [d for d in module_dir.iterdir() if d.is_dir()]
            for subdir in subdirs:
                if not any(subdir.glob('*.md')):
                    issues.append(f"子目录 {subdir} 缺少Markdown文件")
        
        return issues
    
    def generate_report(self) -> str:
        """生成质量检查报告"""
        report = f"""# Rust软件工程质量检查报告

## 📊 检查概览

- **检查时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
- **检查路径**: {self.base_path}
- **总文件数**: {self.stats['total_files']}
- **已检查文件**: {self.stats['checked_files']}
- **发现问题**: {self.stats['issues_found']}
- **链接检查**: {self.stats['links_checked']}
- **断链数量**: {self.stats['broken_links']}

## 🎯 检查结果

### 目录结构检查
"""
        
        # 添加目录结构问题
        dir_issues = self.check_directory_structure()
        if dir_issues:
            report += "\n#### 发现的问题:\n"
            for issue in dir_issues:
                report += f"- ❌ {issue}\n"
        else:
            report += "\n✅ 目录结构检查通过\n"
        
        # 添加文件检查结果
        report += "\n### 文件质量检查\n"
        
        if self.issues:
            report += "\n#### 发现的问题:\n"
            for file_path, issues in self.issues:
                report += f"\n**{file_path}**:\n"
                for issue in issues:
                    report += f"- ❌ {issue}\n"
        else:
            report += "\n✅ 所有文件质量检查通过\n"
        
        # 添加建议
        report += """
## 💡 改进建议

1. **格式规范**: 确保所有Markdown文件符合格式规范
2. **链接完整性**: 定期检查并修复断链
3. **内容完整性**: 补充缺失的章节和内容
4. **结构一致性**: 保持目录结构的一致性

## 🔧 自动化修复

运行以下命令进行自动修复:

```bash
# 格式化Markdown文件
python scripts/format_markdown.py

# 检查并修复链接
python scripts/fix_links.py

# 更新交叉引用
python scripts/update_references.py
```
"""
        
        return report
    
    def run_quality_check(self) -> bool:
        """运行完整的质量检查"""
        print("🔍 开始质量检查...")
        
        # 统计文件
        md_files = list(self.base_path.rglob('*.md'))
        self.stats['total_files'] = len(md_files)
        
        # 检查每个Markdown文件
        for file_path in md_files:
            print(f"检查文件: {file_path.relative_to(self.base_path)}")
            
            file_issues = []
            
            # 格式检查
            format_issues = self.check_markdown_format(file_path)
            file_issues.extend(format_issues)
            
            # 结构检查（仅对主文件）
            if file_path.name in ['README.md', '00_MASTER_INDEX.md'] or file_path.parent.name.startswith(('0', '1', '2', '3', '4', '5', '6', '7', '8')):
                structure_issues = self.check_file_structure(file_path)
                file_issues.extend(structure_issues)
            
            if file_issues:
                self.issues.append((file_path.relative_to(self.base_path), file_issues))
                self.stats['issues_found'] += len(file_issues)
            
            self.stats['checked_files'] += 1
        
        # 生成报告
        report = self.generate_report()
        
        # 保存报告
        report_path = self.base_path / 'QUALITY_CHECK_REPORT.md'
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write(report)
        
        print(f"✅ 质量检查完成，报告已保存到: {report_path}")
        print(f"📊 检查统计: {self.stats['checked_files']} 文件, {self.stats['issues_found']} 问题")
        
        return len(self.issues) == 0

def main():
    """主函数"""
    if len(sys.argv) > 1:
        base_path = sys.argv[1]
    else:
        base_path = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    
    checker = SoftwareQualityChecker(base_path)
    success = checker.run_quality_check()
    
    if success:
        print("🎉 所有质量检查通过!")
        sys.exit(0)
    else:
        print("⚠️ 发现质量问题，请查看报告进行修复")
        sys.exit(1)

if __name__ == "__main__":
    main()
