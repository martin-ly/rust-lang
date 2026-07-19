#!/usr/bin/env python3
"""
Rust语言形式化理论体系 - 自动化维护脚本

本脚本提供自动化维护功能，包括：
1. 链接完整性检查
2. 文档格式验证
3. 重复内容检测
4. 目录结构验证
5. 质量报告生成

作者: Rust语言形式化理论项目组
版本: v2.0
日期: 2025年1月27日
"""

import os
import re
import json
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
        logging.FileHandler('maintenance.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

@dataclass
class LinkInfo:
    """链接信息"""
    source_file: str
    target_file: str
    line_number: int
    link_text: str
    is_valid: bool
    error_message: Optional[str] = None

@dataclass
class DocumentInfo:
    """文档信息"""
    file_path: str
    file_size: int
    line_count: int
    word_count: int
    last_modified: datetime
    content_hash: str
    links: List[LinkInfo]
    issues: List[str]

class MaintenanceAutomation:
    """自动化维护类"""
    
    def __init__(self, base_path: str = "docs/language"):
        self.base_path = Path(base_path)
        self.documents: Dict[str, DocumentInfo] = {}
        self.duplicate_files: Dict[str, List[str]] = {}
        self.broken_links: List[LinkInfo] = []
        self.quality_issues: List[str] = []
        
    def scan_documents(self) -> None:
        """扫描所有文档"""
        logger.info("开始扫描文档...")
        
        for md_file in self.base_path.rglob("*.md"):
            try:
                doc_info = self._analyze_document(md_file)
                self.documents[str(md_file)] = doc_info
            except Exception as e:
                logger.error(f"分析文档失败 {md_file}: {e}")
                
        logger.info(f"扫描完成，共发现 {len(self.documents)} 个文档")
        
    def _analyze_document(self, file_path: Path) -> DocumentInfo:
        """分析单个文档"""
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
            
        # 基本信息
        file_size = file_path.stat().st_size
        line_count = len(content.splitlines())
        word_count = len(content.split())
        last_modified = datetime.fromtimestamp(file_path.stat().st_mtime)
        content_hash = hashlib.md5(content.encode()).hexdigest()
        
        # 分析链接
        links = self._extract_links(str(file_path), content)
        
        # 检查问题
        issues = self._check_document_issues(content)
        
        return DocumentInfo(
            file_path=str(file_path),
            file_size=file_size,
            line_count=line_count,
            word_count=word_count,
            last_modified=last_modified,
            content_hash=content_hash,
            links=links,
            issues=issues
        )
        
    def _extract_links(self, file_path: str, content: str) -> List[LinkInfo]:
        """提取文档中的链接"""
        links = []
        lines = content.splitlines()
        
        # 匹配Markdown链接
        link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
        
        for i, line in enumerate(lines, 1):
            matches = re.finditer(link_pattern, line)
            for match in matches:
                link_text = match.group(1)
                target = match.group(2)
                
                # 检查链接有效性
                is_valid, error_msg = self._validate_link(file_path, target)
                
                link_info = LinkInfo(
                    source_file=file_path,
                    target_file=target,
                    line_number=i,
                    link_text=link_text,
                    is_valid=is_valid,
                    error_message=error_msg
                )
                
                links.append(link_info)
                
                if not is_valid:
                    self.broken_links.append(link_info)
                    
        return links
        
    def _validate_link(self, source_file: str, target: str) -> Tuple[bool, Optional[str]]:
        """验证链接有效性"""
        source_path = Path(source_file)
        
        # 处理不同类型的链接
        if target.startswith('http'):
            return True, None  # 外部链接，假设有效
            
        if target.startswith('#'):
            return True, None  # 锚点链接，假设有效
            
        # 相对路径链接
        if target.startswith('./') or target.startswith('../'):
            target_path = source_path.parent / target
        else:
            target_path = source_path.parent / target
            
        if target_path.exists():
            return True, None
        else:
            return False, f"文件不存在: {target_path}"
            
    def _check_document_issues(self, content: str) -> List[str]:
        """检查文档问题"""
        issues = []
        
        # 检查标题层次
        if not re.search(r'^# ', content, re.MULTILINE):
            issues.append("缺少主标题")
            
        # 检查代码块
        code_blocks = re.findall(r'```(\w+)?\n(.*?)\n```', content, re.DOTALL)
        for lang, code in code_blocks:
            if lang and lang not in ['rust', 'text', 'markdown', 'bash', 'python']:
                issues.append(f"未知代码语言: {lang}")
                
        # 检查数学公式
        math_formulas = re.findall(r'\$\$.*?\$\$', content, re.DOTALL)
        for formula in math_formulas:
            if len(formula) > 1000:
                issues.append("数学公式过长")
                
        # 检查链接格式
        malformed_links = re.findall(r'\[([^\]]*)\]\(([^)]*)\)', content)
        for text, url in malformed_links:
            if not text.strip():
                issues.append("链接文本为空")
            if not url.strip():
                issues.append("链接URL为空")
                
        return issues
        
    def detect_duplicates(self) -> None:
        """检测重复文件"""
        logger.info("开始检测重复文件...")
        
        hash_to_files = {}
        
        for file_path, doc_info in self.documents.items():
            content_hash = doc_info.content_hash
            
            if content_hash not in hash_to_files:
                hash_to_files[content_hash] = []
            hash_to_files[content_hash].append(file_path)
            
        # 找出重复文件
        for content_hash, files in hash_to_files.items():
            if len(files) > 1:
                self.duplicate_files[content_hash] = files
                
        logger.info(f"发现 {len(self.duplicate_files)} 组重复文件")
        
    def validate_directory_structure(self) -> List[str]:
        """验证目录结构"""
        logger.info("开始验证目录结构...")
        
        issues = []
        
        # 检查必要的目录
        required_dirs = [
            'core', 'advanced', 'system', 'applications', 
            'domains', 'research', 'ecosystem', 'verification',
            'navigation', 'archive'
        ]
        
        for dir_name in required_dirs:
            dir_path = self.base_path / dir_name
            if not dir_path.exists():
                issues.append(f"缺少必要目录: {dir_name}")
                
        # 检查模块目录结构
        for module_dir in self.base_path.iterdir():
            if module_dir.is_dir() and module_dir.name.startswith(('01_', '02_', '03_', '04_', '05_', '06_', '07_', '08_', '09_', '10_', '11_', '12_', '13_', '14_', '15_', '16_', '17_', '18_', '19_', '20_', '21_', '22_', '23_', '24_', '25_', '26_', '27_', '28_')):
                index_file = module_dir / '00_index.md'
                if not index_file.exists():
                    issues.append(f"模块 {module_dir.name} 缺少索引文件")
                    
        logger.info(f"目录结构验证完成，发现 {len(issues)} 个问题")
        return issues
        
    def generate_quality_report(self) -> Dict:
        """生成质量报告"""
        logger.info("开始生成质量报告...")
        
        total_documents = len(self.documents)
        total_links = sum(len(doc.links) for doc in self.documents.values())
        broken_links_count = len(self.broken_links)
        duplicate_groups = len(self.duplicate_files)
        
        # 计算质量分数
        quality_score = 100
        
        # 链接质量 (30%)
        if total_links > 0:
            link_quality = (total_links - broken_links_count) / total_links * 100
            quality_score -= (100 - link_quality) * 0.3
            
        # 重复文件 (20%)
        if total_documents > 0:
            duplicate_ratio = duplicate_groups / total_documents
            quality_score -= duplicate_ratio * 100 * 0.2
            
        # 文档问题 (20%)
        total_issues = sum(len(doc.issues) for doc in self.documents.values())
        if total_documents > 0:
            issue_ratio = total_issues / total_documents
            quality_score -= min(issue_ratio * 10, 20)
            
        # 目录结构 (30%)
        structure_issues = self.validate_directory_structure()
        if len(structure_issues) > 0:
            quality_score -= min(len(structure_issues) * 2, 30)
            
        report = {
            'timestamp': datetime.now().isoformat(),
            'total_documents': total_documents,
            'total_links': total_links,
            'broken_links': broken_links_count,
            'duplicate_groups': duplicate_groups,
            'quality_score': round(quality_score, 2),
            'structure_issues': structure_issues,
            'broken_links_details': [
                {
                    'source': link.source_file,
                    'target': link.target_file,
                    'line': link.line_number,
                    'error': link.error_message
                }
                for link in self.broken_links
            ],
            'duplicate_files': self.duplicate_files,
            'document_issues': {
                file_path: doc.issues
                for file_path, doc in self.documents.items()
                if doc.issues
            }
        }
        
        logger.info(f"质量报告生成完成，质量分数: {quality_score:.2f}")
        return report
        
    def save_report(self, report: Dict, output_file: str = "quality_report.json") -> None:
        """保存报告到文件"""
        output_path = self.base_path / output_file
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(report, f, ensure_ascii=False, indent=2)
            
        logger.info(f"报告已保存到: {output_path}")
        
    def run_full_check(self) -> Dict:
        """运行完整检查"""
        logger.info("开始运行完整检查...")
        
        # 扫描文档
        self.scan_documents()
        
        # 检测重复文件
        self.detect_duplicates()
        
        # 生成质量报告
        report = self.generate_quality_report()
        
        # 保存报告
        self.save_report(report)
        
        logger.info("完整检查完成")
        return report

def main():
    """主函数"""
    parser = argparse.ArgumentParser(description='Rust语言形式化理论体系自动化维护脚本')
    parser.add_argument('--path', default='docs/language', help='文档根目录路径')
    parser.add_argument('--output', default='quality_report.json', help='输出报告文件名')
    parser.add_argument('--check-links', action='store_true', help='检查链接完整性')
    parser.add_argument('--check-duplicates', action='store_true', help='检查重复文件')
    parser.add_argument('--check-structure', action='store_true', help='检查目录结构')
    parser.add_argument('--full-check', action='store_true', help='运行完整检查')
    
    args = parser.parse_args()
    
    # 创建维护实例
    maintenance = MaintenanceAutomation(args.path)
    
    if args.full_check:
        # 运行完整检查
        report = maintenance.run_full_check()
        print(f"质量分数: {report['quality_score']}")
        print(f"总文档数: {report['total_documents']}")
        print(f"损坏链接: {report['broken_links']}")
        print(f"重复文件组: {report['duplicate_groups']}")
        
    elif args.check_links:
        # 只检查链接
        maintenance.scan_documents()
        print(f"发现 {len(maintenance.broken_links)} 个损坏链接")
        
    elif args.check_duplicates:
        # 只检查重复文件
        maintenance.scan_documents()
        maintenance.detect_duplicates()
        print(f"发现 {len(maintenance.duplicate_files)} 组重复文件")
        
    elif args.check_structure:
        # 只检查目录结构
        issues = maintenance.validate_directory_structure()
        print(f"发现 {len(issues)} 个目录结构问题")
        
    else:
        # 默认运行完整检查
        report = maintenance.run_full_check()
        print(f"质量分数: {report['quality_score']}")

if __name__ == "__main__":
    main()
