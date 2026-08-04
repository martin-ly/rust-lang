#!/usr/bin/env python3
"""
Rust软件工程文档链接检查器
自动检查并修复文档中的链接问题
"""

import os
import re
import sys
from pathlib import Path
from typing import List, Dict, Set, Tuple
from urllib.parse import urlparse
import requests
from datetime import datetime

class LinkChecker:
    def __init__(self, base_path: str):
        self.base_path = Path(base_path)
        self.broken_links = []
        self.valid_links = []
        self.stats = {
            'total_links': 0,
            'internal_links': 0,
            'external_links': 0,
            'broken_links': 0,
            'files_checked': 0
        }
    
    def extract_links(self, content: str, file_path: Path) -> List[Tuple[str, str, int]]:
        """提取文档中的链接"""
        links = []
        
        # Markdown链接格式: [text](url)
        link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        for match in re.finditer(link_pattern, content):
            link_text = match.group(1)
            link_url = match.group(2)
            line_number = content[:match.start()].count('\n') + 1
            links.append((link_text, link_url, line_number))
        
        # 引用链接格式: [text][ref]
        ref_pattern = r'\[([^\]]+)\]\[([^\]]+)\]'
        for match in re.finditer(ref_pattern, content):
            link_text = match.group(1)
            ref_id = match.group(2)
            line_number = content[:match.start()].count('\n') + 1
            links.append((link_text, f"#{ref_id}", line_number))
        
        return links
    
    def is_internal_link(self, url: str) -> bool:
        """判断是否为内部链接"""
        return (url.startswith('./') or 
                url.startswith('../') or 
                url.startswith('#') or
                (not url.startswith(('http://', 'https://', 'mailto:', 'ftp://'))))
    
    def resolve_internal_link(self, url: str, base_file: Path) -> Path:
        """解析内部链接路径"""
        if url.startswith('#'):
            return base_file  # 锚点链接
        
        if url.startswith('./'):
            return base_file.parent / url[2:]
        elif url.startswith('../'):
            return base_file.parent / url
        else:
            return base_file.parent / url
    
    def check_internal_link(self, url: str, base_file: Path) -> Tuple[bool, str]:
        """检查内部链接"""
        try:
            target_path = self.resolve_internal_link(url, base_file)
            
            if url.startswith('#'):
                # 检查锚点
                anchor = url[1:]
                if target_path.exists():
                    with open(target_path, 'r', encoding='utf-8') as f:
                        content = f.read()
                        # 查找标题作为锚点
                        if f"# {anchor}" in content or f"## {anchor}" in content:
                            return True, "锚点存在"
                        else:
                            return False, f"锚点 '{anchor}' 不存在"
                else:
                    return False, "目标文件不存在"
            else:
                # 检查文件或目录
                if target_path.exists():
                    return True, "目标存在"
                else:
                    return False, f"目标路径不存在: {target_path}"
        
        except Exception as e:
            return False, f"解析错误: {e}"
    
    def check_external_link(self, url: str) -> Tuple[bool, str]:
        """检查外部链接"""
        try:
            response = requests.head(url, timeout=10, allow_redirects=True)
            if response.status_code < 400:
                return True, f"状态码: {response.status_code}"
            else:
                return False, f"状态码: {response.status_code}"
        except requests.exceptions.RequestException as e:
            return False, f"请求错误: {e}"
    
    def check_file_links(self, file_path: Path) -> List[Dict]:
        """检查单个文件的链接"""
        file_issues = []
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            links = self.extract_links(content, file_path)
            
            for link_text, link_url, line_number in links:
                self.stats['total_links'] += 1
                
                if self.is_internal_link(link_url):
                    self.stats['internal_links'] += 1
                    is_valid, message = self.check_internal_link(link_url, file_path)
                else:
                    self.stats['external_links'] += 1
                    is_valid, message = self.check_external_link(link_url)
                
                if is_valid:
                    self.valid_links.append({
                        'file': str(file_path.relative_to(self.base_path)),
                        'line': line_number,
                        'text': link_text,
                        'url': link_url,
                        'status': 'valid'
                    })
                else:
                    self.stats['broken_links'] += 1
                    issue = {
                        'file': str(file_path.relative_to(self.base_path)),
                        'line': line_number,
                        'text': link_text,
                        'url': link_url,
                        'error': message,
                        'status': 'broken'
                    }
                    file_issues.append(issue)
                    self.broken_links.append(issue)
        
        except Exception as e:
            file_issues.append({
                'file': str(file_path.relative_to(self.base_path)),
                'line': 0,
                'text': '',
                'url': '',
                'error': f"文件读取错误: {e}",
                'status': 'error'
            })
        
        self.stats['files_checked'] += 1
        return file_issues
    
    def suggest_fixes(self, broken_link: Dict) -> List[str]:
        """为断链提供修复建议"""
        suggestions = []
        url = broken_link['url']
        
        if self.is_internal_link(url):
            # 内部链接修复建议
            if url.startswith('./'):
                # 检查可能的正确路径
                possible_paths = [
                    url.replace('./', ''),
                    url.replace('./', '../'),
                    url.replace('./', '../../')
                ]
                suggestions.extend([f"尝试路径: {path}" for path in possible_paths])
            
            elif not url.startswith(('http', '#')):
                # 相对路径建议
                suggestions.append(f"尝试添加 './' 前缀: ./{url}")
                suggestions.append(f"尝试添加 '../' 前缀: ../{url}")
        
        else:
            # 外部链接修复建议
            suggestions.append("检查URL是否正确")
            suggestions.append("检查网络连接")
            suggestions.append("考虑使用存档链接")
        
        return suggestions
    
    def generate_report(self) -> str:
        """生成链接检查报告"""
        report = f"""# Rust软件工程文档链接检查报告

## 📊 检查概览

- **检查时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
- **检查路径**: {self.base_path}
- **总链接数**: {self.stats['total_links']}
- **内部链接**: {self.stats['internal_links']}
- **外部链接**: {self.stats['external_links']}
- **断链数量**: {self.stats['broken_links']}
- **检查文件**: {self.stats['files_checked']}

## 🔗 链接检查结果

### 断链详情
"""
        
        if self.broken_links:
            # 按文件分组显示断链
            files_with_issues = {}
            for link in self.broken_links:
                file_path = link['file']
                if file_path not in files_with_issues:
                    files_with_issues[file_path] = []
                files_with_issues[file_path].append(link)
            
            for file_path, links in files_with_issues.items():
                report += f"\n#### {file_path}\n"
                for link in links:
                    report += f"- **第{link['line']}行**: [{link['text']}]({link['url']})\n"
                    report += f"  - ❌ 错误: {link['error']}\n"
                    
                    # 添加修复建议
                    suggestions = self.suggest_fixes(link)
                    if suggestions:
                        report += f"  - 💡 建议: {'; '.join(suggestions)}\n"
        else:
            report += "\n✅ 所有链接检查通过，未发现断链\n"
        
        # 添加统计信息
        report += f"""
## 📈 统计信息

- **链接健康度**: {((self.stats['total_links'] - self.stats['broken_links']) / max(self.stats['total_links'], 1) * 100):.1f}%
- **内部链接占比**: {(self.stats['internal_links'] / max(self.stats['total_links'], 1) * 100):.1f}%
- **外部链接占比**: {(self.stats['external_links'] / max(self.stats['total_links'], 1) * 100):.1f}%

## 🔧 修复建议

### 自动修复
```bash
# 运行自动修复脚本
python scripts/auto_fix_links.py

# 手动修复断链
python scripts/manual_fix_links.py
```

### 预防措施
1. **定期检查**: 建议每周运行一次链接检查
2. **CI集成**: 在CI/CD中集成链接检查
3. **链接验证**: 提交前验证所有链接
4. **存档备份**: 重要外部链接使用存档服务
"""
        
        return report
    
    def run_link_check(self) -> bool:
        """运行链接检查"""
        print("🔍 开始链接检查...")
        
        # 查找所有Markdown文件
        md_files = list(self.base_path.rglob('*.md'))
        
        for file_path in md_files:
            print(f"检查文件: {file_path.relative_to(self.base_path)}")
            self.check_file_links(file_path)
        
        # 生成报告
        report = self.generate_report()
        
        # 保存报告
        report_path = self.base_path / 'LINK_CHECK_REPORT.md'
        with open(report_path, 'w', encoding='utf-8') as f:
            f.write(report)
        
        print(f"✅ 链接检查完成，报告已保存到: {report_path}")
        print(f"📊 检查统计: {self.stats['total_links']} 链接, {self.stats['broken_links']} 断链")
        
        return len(self.broken_links) == 0

def main():
    """主函数"""
    if len(sys.argv) > 1:
        base_path = sys.argv[1]
    else:
        base_path = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    
    checker = LinkChecker(base_path)
    success = checker.run_link_check()
    
    if success:
        print("🎉 所有链接检查通过!")
        sys.exit(0)
    else:
        print("⚠️ 发现断链，请查看报告进行修复")
        sys.exit(1)

if __name__ == "__main__":
    main()
