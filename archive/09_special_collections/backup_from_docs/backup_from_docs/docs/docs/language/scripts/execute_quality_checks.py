#!/usr/bin/env python3
"""
Rust语言形式化理论体系 - 质量检查执行脚本

本脚本执行完整的质量检查流程，包括：
1. 加载质量配置
2. 执行各种质量检查
3. 生成质量报告
4. 提供修复建议

作者: Rust语言形式化理论项目组
版本: v2.0
日期: 2025年1月27日
"""

import os
import json
import re
import hashlib
from pathlib import Path
from typing import Dict, List, Set, Tuple, Optional
from dataclasses import dataclass
from datetime import datetime
import argparse
import logging

# 配置日志
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler('quality_checks.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

@dataclass
class QualityIssue:
    """质量问题"""
    category: str
    severity: str
    file_path: str
    line_number: int
    description: str
    suggestion: Optional[str] = None

@dataclass
class QualityReport:
    """质量报告"""
    timestamp: str
    overall_score: float
    issues: List[QualityIssue]
    statistics: Dict
    recommendations: List[str]

class QualityChecker:
    """质量检查器"""
    
    def __init__(self, config_path: str = "scripts/quality_config.json"):
        self.config_path = Path(config_path)
        self.config = self._load_config()
        self.issues: List[QualityIssue] = []
        self.statistics = {
            'total_files': 0,
            'total_links': 0,
            'broken_links': 0,
            'duplicate_files': 0,
            'format_issues': 0,
            'content_issues': 0
        }
        
    def _load_config(self) -> Dict:
        """加载质量配置"""
        try:
            with open(self.config_path, 'r', encoding='utf-8') as f:
                return json.load(f)
        except Exception as e:
            logger.error(f"加载配置失败: {e}")
            return {}
            
    def check_markdown_syntax(self, file_path: Path) -> List[QualityIssue]:
        """检查Markdown语法"""
        issues = []
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.splitlines()
                
            # 检查标题层次
            header_levels = []
            for i, line in enumerate(lines, 1):
                if line.startswith('#'):
                    level = len(line) - len(line.lstrip('#'))
                    header_levels.append(level)
                    
                    # 检查标题层次是否合理
                    if level > 6:
                        issues.append(QualityIssue(
                            category='format',
                            severity='normal',
                            file_path=str(file_path),
                            line_number=i,
                            description=f"标题层次过深: {level}",
                            suggestion="建议使用更浅的标题层次"
                        ))
                        
            # 检查标题层次跳跃
            for i in range(1, len(header_levels)):
                if header_levels[i] - header_levels[i-1] > 1:
                    issues.append(QualityIssue(
                        category='format',
                        severity='normal',
                        file_path=str(file_path),
                        line_number=i+1,
                        description="标题层次跳跃",
                        suggestion="建议保持标题层次连续性"
                    ))
                    
            # 检查代码块
            code_blocks = re.findall(r'```(\w+)?\n(.*?)\n```', content, re.DOTALL)
            for lang, code in code_blocks:
                if len(code) > 1000:
                    issues.append(QualityIssue(
                        category='content',
                        severity='normal',
                        file_path=str(file_path),
                        line_number=0,
                        description="代码块过长",
                        suggestion="建议将长代码块分解为多个部分"
                    ))
                    
            # 检查数学公式
            math_formulas = re.findall(r'\$\$(.*?)\$\$', content, re.DOTALL)
            for formula in math_formulas:
                if len(formula) > 500:
                    issues.append(QualityIssue(
                        category='content',
                        severity='normal',
                        file_path=str(file_path),
                        line_number=0,
                        description="数学公式过长",
                        suggestion="建议将长公式分解为多个部分"
                    ))
                    
        except Exception as e:
            issues.append(QualityIssue(
                category='system',
                severity='critical',
                file_path=str(file_path),
                line_number=0,
                description=f"文件读取失败: {e}",
                suggestion="检查文件权限和编码"
            ))
            
        return issues
        
    def check_links(self, file_path: Path) -> List[QualityIssue]:
        """检查链接"""
        issues = []
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                lines = content.splitlines()
                
            # 查找链接
            link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
            
            for i, line in enumerate(lines, 1):
                matches = re.finditer(link_pattern, line)
                for match in matches:
                    link_text = match.group(1)
                    target = match.group(2)
                    
                    # 检查链接文本
                    if not link_text.strip():
                        issues.append(QualityIssue(
                            category='content',
                            severity='important',
                            file_path=str(file_path),
                            line_number=i,
                            description="链接文本为空",
                            suggestion="为链接添加描述性文本"
                        ))
                        
                    # 检查链接目标
                    if not target.strip():
                        issues.append(QualityIssue(
                            category='content',
                            severity='important',
                            file_path=str(file_path),
                            line_number=i,
                            description="链接目标为空",
                            suggestion="为链接添加有效目标"
                        ))
                        
                    # 检查内部链接
                    if not target.startswith('http') and not target.startswith('#'):
                        target_path = file_path.parent / target
                        if not target_path.exists():
                            issues.append(QualityIssue(
                                category='link',
                                severity='important',
                                file_path=str(file_path),
                                line_number=i,
                                description=f"链接目标不存在: {target}",
                                suggestion="检查链接路径是否正确"
                            ))
                            
                    # 检查链接长度
                    if len(target) > 200:
                        issues.append(QualityIssue(
                            category='format',
                            severity='normal',
                            file_path=str(file_path),
                            line_number=i,
                            description="链接过长",
                            suggestion="考虑使用短链接或重命名文件"
                        ))
                        
        except Exception as e:
            issues.append(QualityIssue(
                category='system',
                severity='critical',
                file_path=str(file_path),
                line_number=0,
                description=f"链接检查失败: {e}",
                suggestion="检查文件权限和编码"
            ))
            
        return issues
        
    def check_content_quality(self, file_path: Path) -> List[QualityIssue]:
        """检查内容质量"""
        issues = []
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # 检查文件大小
            file_size = len(content)
            if file_size > 100000:  # 100KB
                issues.append(QualityIssue(
                    category='content',
                    severity='normal',
                    file_path=str(file_path),
                    line_number=0,
                    description="文件过大",
                    suggestion="考虑将大文件分解为多个小文件"
                ))
                
            # 检查行数
            line_count = len(content.splitlines())
            if line_count > 1000:
                issues.append(QualityIssue(
                    category='content',
                    severity='normal',
                    file_path=str(file_path),
                    line_number=0,
                    description="文件行数过多",
                    suggestion="考虑将长文件分解为多个短文件"
                ))
                
            # 检查TODO标记
            if 'TODO:' in content or 'FIXME:' in content or 'XXX:' in content:
                issues.append(QualityIssue(
                    category='content',
                    severity='suggestion',
                    file_path=str(file_path),
                    line_number=0,
                    description="包含未完成的标记",
                    suggestion="完成或移除TODO/FIXME/XXX标记"
                ))
                
            # 检查重复内容
            lines = content.splitlines()
            line_counts = {}
            for line in lines:
                if line.strip():
                    line_counts[line] = line_counts.get(line, 0) + 1
                    
            for line, count in line_counts.items():
                if count > 3:
                    issues.append(QualityIssue(
                        category='content',
                        severity='normal',
                        file_path=str(file_path),
                        line_number=0,
                        description=f"重复内容: {line[:50]}...",
                        suggestion="考虑提取重复内容为公共部分"
                    ))
                    
        except Exception as e:
            issues.append(QualityIssue(
                category='system',
                severity='critical',
                file_path=str(file_path),
                line_number=0,
                description=f"内容质量检查失败: {e}",
                suggestion="检查文件权限和编码"
            ))
            
        return issues
        
    def check_file_structure(self, file_path: Path) -> List[QualityIssue]:
        """检查文件结构"""
        issues = []
        
        # 检查文件命名
        if not file_path.name.endswith('.md'):
            issues.append(QualityIssue(
                category='structure',
                severity='normal',
                file_path=str(file_path),
                line_number=0,
                description="文件扩展名不是.md",
                suggestion="使用.md扩展名"
            ))
            
        # 检查文件名格式
        if '_' in file_path.name and not file_path.name.startswith('00_'):
            issues.append(QualityIssue(
                category='structure',
                severity='suggestion',
                file_path=str(file_path),
                line_number=0,
                description="文件名包含下划线",
                suggestion="考虑使用连字符或驼峰命名"
            ))
            
        # 检查目录结构
        if file_path.parent.name.startswith(('01_', '02_', '03_', '04_', '05_', '06_', '07_', '08_', '09_', '10_', '11_', '12_', '13_', '14_', '15_', '16_', '17_', '18_', '19_', '20_', '21_', '22_', '23_', '24_', '25_', '26_', '27_', '28_')):
            index_file = file_path.parent / '00_index.md'
            if not index_file.exists():
                issues.append(QualityIssue(
                    category='structure',
                    severity='important',
                    file_path=str(file_path),
                    line_number=0,
                    description="模块目录缺少索引文件",
                    suggestion="创建00_index.md文件"
                ))
                
        return issues
        
    def run_quality_checks(self, base_path: str = "docs/language") -> QualityReport:
        """运行质量检查"""
        logger.info("开始运行质量检查...")
        
        base = Path(base_path)
        all_issues = []
        
        # 扫描所有Markdown文件
        for md_file in base.rglob("*.md"):
            self.statistics['total_files'] += 1
            
            # 检查Markdown语法
            issues = self.check_markdown_syntax(md_file)
            all_issues.extend(issues)
            
            # 检查链接
            issues = self.check_links(md_file)
            all_issues.extend(issues)
            self.statistics['total_links'] += len(issues)
            
            # 检查内容质量
            issues = self.check_content_quality(md_file)
            all_issues.extend(issues)
            
            # 检查文件结构
            issues = self.check_file_structure(md_file)
            all_issues.extend(issues)
            
        # 统计问题
        for issue in all_issues:
            if issue.category == 'link':
                self.statistics['broken_links'] += 1
            elif issue.category == 'format':
                self.statistics['format_issues'] += 1
            elif issue.category == 'content':
                self.statistics['content_issues'] += 1
                
        # 计算质量分数
        total_issues = len(all_issues)
        if self.statistics['total_files'] > 0:
            quality_score = max(0, 100 - (total_issues / self.statistics['total_files']) * 10)
        else:
            quality_score = 100
            
        # 生成建议
        recommendations = self._generate_recommendations(all_issues)
        
        report = QualityReport(
            timestamp=datetime.now().isoformat(),
            overall_score=quality_score,
            issues=all_issues,
            statistics=self.statistics,
            recommendations=recommendations
        )
        
        logger.info(f"质量检查完成，质量分数: {quality_score:.2f}")
        return report
        
    def _generate_recommendations(self, issues: List[QualityIssue]) -> List[str]:
        """生成改进建议"""
        recommendations = []
        
        # 统计问题类型
        issue_counts = {}
        for issue in issues:
            issue_counts[issue.category] = issue_counts.get(issue.category, 0) + 1
            
        # 生成建议
        if issue_counts.get('link', 0) > 0:
            recommendations.append("修复损坏的链接，确保所有链接都指向有效目标")
            
        if issue_counts.get('format', 0) > 0:
            recommendations.append("统一文档格式，确保Markdown语法正确")
            
        if issue_counts.get('content', 0) > 0:
            recommendations.append("改进文档内容质量，移除重复和过时信息")
            
        if issue_counts.get('structure', 0) > 0:
            recommendations.append("优化文件结构，确保目录组织合理")
            
        if issue_counts.get('system', 0) > 0:
            recommendations.append("解决系统问题，确保文件可正常访问")
            
        return recommendations
        
    def save_report(self, report: QualityReport, output_file: str = "quality_check_report.json") -> None:
        """保存质量报告"""
        output_path = Path(output_file)
        
        # 转换为可序列化的格式
        report_data = {
            'timestamp': report.timestamp,
            'overall_score': report.overall_score,
            'issues': [
                {
                    'category': issue.category,
                    'severity': issue.severity,
                    'file_path': issue.file_path,
                    'line_number': issue.line_number,
                    'description': issue.description,
                    'suggestion': issue.suggestion
                }
                for issue in report.issues
            ],
            'statistics': report.statistics,
            'recommendations': report.recommendations
        }
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(report_data, f, ensure_ascii=False, indent=2)
            
        logger.info(f"质量报告已保存到: {output_path}")

def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='Rust语言形式化理论体系质量检查执行脚本')
    parser.add_argument('--path', default='docs/language', help='文档根目录路径')
    parser.add_argument('--config', default='scripts/quality_config.json', help='质量配置文件路径')
    parser.add_argument('--output', default='quality_check_report.json', help='输出报告文件名')
    parser.add_argument('--verbose', action='store_true', help='详细输出')
    
    args = parser.parse_args()
    
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)
        
    # 创建质量检查器
    checker = QualityChecker(args.config)
    
    # 运行质量检查
    report = checker.run_quality_checks(args.path)
    
    # 保存报告
    checker.save_report(report, args.output)
    
    # 输出摘要
    print(f"质量检查完成!")
    print(f"质量分数: {report.overall_score:.2f}")
    print(f"总文件数: {report.statistics['total_files']}")
    print(f"总问题数: {len(report.issues)}")
    print(f"损坏链接: {report.statistics['broken_links']}")
    print(f"格式问题: {report.statistics['format_issues']}")
    print(f"内容问题: {report.statistics['content_issues']}")
    
    if report.recommendations:
        print("\n改进建议:")
        for i, rec in enumerate(report.recommendations, 1):
            print(f"{i}. {rec}")

if __name__ == "__main__":
    main()
