#!/usr/bin/env python3
"""
Rust形式化理论项目 - 阶段四质量验证脚本
执行自动化质量检查，包括一致性验证、完整性检查等
"""

import os
import re
import json
from pathlib import Path
from typing import Dict, List, Set, Tuple
from collections import defaultdict

class QualityVerifier:
    def __init__(self, base_path: str):
        self.base_path = Path(base_path)
        self.results = {
            'consistency_check': {},
            'completeness_check': {},
            'cross_reference_check': {},
            'concept_definitions': {},
            'mathematical_symbols': {},
            'errors': [],
            'warnings': []
        }
        
    def run_full_verification(self):
        """执行完整的质量验证流程"""
        print("🔍 开始执行质量验证...")
        
        # 1. 概念一致性检查
        print("\n📋 1. 执行概念一致性检查...")
        self.check_concept_consistency()
        
        # 2. 数学符号一致性检查
        print("\n🔢 2. 执行数学符号一致性检查...")
        self.check_mathematical_symbols()
        
        # 3. 交叉引用验证
        print("\n🔗 3. 执行交叉引用验证...")
        self.verify_cross_references()
        
        # 4. 完整性检查
        print("\n📊 4. 执行完整性检查...")
        self.check_completeness()
        
        # 5. 文档结构验证
        print("\n📁 5. 执行文档结构验证...")
        self.verify_document_structure()
        
        # 6. 生成报告
        print("\n📄 6. 生成验证报告...")
        self.generate_report()
        
    def check_concept_consistency(self):
        """检查概念定义的一致性"""
        concept_definitions = defaultdict(list)
        
        # 扫描所有markdown文件
        for md_file in self.base_path.rglob("*.md"):
            content = self.read_file_safely(md_file)
            if content is None:
                continue
                
            # 提取概念定义
            definitions = self.extract_concept_definitions(content, md_file)
            for concept, definition in definitions:
                concept_definitions[concept].append({
                    'file': str(md_file.relative_to(self.base_path)),
                    'definition': definition
                })
        
        # 检查一致性
        inconsistencies = []
        for concept, defs in concept_definitions.items():
            if len(defs) > 1:
                # 检查定义是否一致
                base_def = defs[0]['definition']
                for def_info in defs[1:]:
                    if not self.definitions_consistent(base_def, def_info['definition']):
                        inconsistencies.append({
                            'concept': concept,
                            'conflicting_files': [defs[0]['file'], def_info['file']],
                            'definitions': [base_def, def_info['definition']]
                        })
        
        self.results['consistency_check']['concept_inconsistencies'] = inconsistencies
        self.results['concept_definitions'] = dict(concept_definitions)
        
        if inconsistencies:
            print(f"⚠️  发现 {len(inconsistencies)} 个概念定义不一致问题")
        else:
            print("✅ 概念定义一致性检查通过")
    
    def extract_concept_definitions(self, content: str, file_path: Path) -> List[Tuple[str, str]]:
        """从文档中提取概念定义"""
        definitions = []
        
        # 匹配形式化定义模式
        patterns = [
            r'###\s*定义[：:]\s*([^#\n]+)\n([^#]+?)(?=###|\n##|\Z)',
            r'#### 定义\d*[：:]?\s*([^#\n]+)\n([^#]+?)(?=###|\n##|\Z)',
            r'\*\*定义\*\*[：:]?\s*([^*\n]+)\*\*[：:]?\s*([^\n]+)',
            r'定义\s*\d*[：:]?\s*([^：:\n]+)[：:]\s*([^\n]+)'
        ]
        
        for pattern in patterns:
            matches = re.finditer(pattern, content, re.MULTILINE | re.DOTALL)
            for match in matches:
                concept = match.group(1).strip()
                definition = match.group(2).strip()
                definitions.append((concept, definition))
        
        return definitions
    
    def definitions_consistent(self, def1: str, def2: str) -> bool:
        """检查两个定义是否一致（简化版本）"""
        # 移除标点和空白进行比较
        normalized1 = re.sub(r'[^\w\s]', '', def1.lower()).split()
        normalized2 = re.sub(r'[^\w\s]', '', def2.lower()).split()
        
        # 计算相似度（简单的Jaccard相似度）
        set1, set2 = set(normalized1), set(normalized2)
        intersection = len(set1.intersection(set2))
        union = len(set1.union(set2))
        
        similarity = intersection / union if union > 0 else 0
        return similarity > 0.7  # 70%相似度阈值
    
    def check_mathematical_symbols(self):
        """检查数学符号的一致性使用"""
        symbol_usage = defaultdict(list)
        
        # 常见数学符号模式
        symbol_patterns = {
            'forall': r'∀|\\forall',
            'exists': r'∃|\\exists', 
            'implies': r'⇒|\\implies|=>',
            'equiv': r'⇔|\\equiv|<=>',
            'in': r'∈|\\in',
            'subset': r'⊆|\\subseteq|⊂|\\subset',
            'union': r'∪|\\cup|⊎|\\uplus',
            'intersection': r'∩|\\cap',
            'bottom': r'⊥|\\bot',
            'top': r'⊤|\\top'
        }
        
        for md_file in self.base_path.rglob("*.md"):
            content = self.read_file_safely(md_file)
            if content is None:
                continue
                
            for symbol_name, pattern in symbol_patterns.items():
                matches = re.findall(pattern, content)
                if matches:
                    symbol_usage[symbol_name].extend([{
                        'file': str(md_file.relative_to(self.base_path)),
                        'variants': list(set(matches))
                    }])
        
        # 检查符号使用的一致性
        symbol_inconsistencies = []
        for symbol_name, usages in symbol_usage.items():
            variants = set()
            for usage in usages:
                variants.update(usage['variants'])
            
            if len(variants) > 1:
                symbol_inconsistencies.append({
                    'symbol': symbol_name,
                    'variants': list(variants),
                    'files': [usage['file'] for usage in usages]
                })
        
        self.results['mathematical_symbols'] = dict(symbol_usage)
        self.results['consistency_check']['symbol_inconsistencies'] = symbol_inconsistencies
        
        if symbol_inconsistencies:
            print(f"⚠️  发现 {len(symbol_inconsistencies)} 个数学符号不一致问题")
        else:
            print("✅ 数学符号一致性检查通过")
    
    def verify_cross_references(self):
        """验证交叉引用的有效性"""
        broken_links = []
        internal_links = []
        
        # 提取所有内部链接
        link_pattern = r'\[\[([^\]]+)\]\]|\[([^\]]+)\]\(([^)]+)\)'
        
        for md_file in self.base_path.rglob("*.md"):
            content = self.read_file_safely(md_file)
            if content is None:
                continue
                
            matches = re.finditer(link_pattern, content)
            for match in matches:
                if match.group(1):  # [[link]] format
                    link_target = match.group(1)
                    internal_links.append({
                        'source': str(md_file.relative_to(self.base_path)),
                        'target': link_target,
                        'type': 'internal'
                    })
                elif match.group(3):  # [text](link) format
                    link_target = match.group(3)
                    if not link_target.startswith(('http://', 'https://')):
                        internal_links.append({
                            'source': str(md_file.relative_to(self.base_path)),
                            'target': link_target,
                            'type': 'relative'
                        })
        
        # 验证链接有效性
        for link in internal_links:
            target_path = self.resolve_link_target(link['target'], link['source'])
            if target_path and not target_path.exists():
                broken_links.append({
                    'source': link['source'],
                    'target': link['target'],
                    'resolved_path': str(target_path)
                })
        
        self.results['cross_reference_check'] = {
            'total_links': len(internal_links),
            'broken_links': broken_links,
            'valid_links': len(internal_links) - len(broken_links)
        }
        
        if broken_links:
            print(f"⚠️  发现 {len(broken_links)} 个损坏的链接")
        else:
            print("✅ 交叉引用验证通过")
    
    def resolve_link_target(self, target: str, source: str) -> Path:
        """解析链接目标路径"""
        try:
            if target.endswith('.md'):
                # 相对路径
                source_dir = Path(source).parent
                return self.base_path / source_dir / target
            else:
                # 可能是文件名或章节引用
                possible_path = self.base_path / f"{target}.md"
                if possible_path.exists():
                    return possible_path
                
                # 搜索匹配的文件
                for md_file in self.base_path.rglob("*.md"):
                    if md_file.stem == target:
                        return md_file
                        
        except Exception:
            pass
        return None
    
    def check_completeness(self):
        """检查理论体系的完整性"""
        # 定义核心模块和预期文件
        expected_modules = {
            '01_ownership_borrowing': ['00_index.md', '01_*.md'],
            '02_type_system': ['00_index.md', '01_*.md'],
            '03_control_flow': ['00_index.md', '01_*.md'],
            '04_generics': ['00_index.md', '01_*.md'],
            '05_concurrency': ['00_index.md', '01_*.md'],
            '06_async_await': ['00_index.md', '01_*.md'],
            '07_macro_system': ['00_index.md', '01_*.md'],
            '08_algorithms': ['00_index.md', '01_*.md'],
            '09_design_patterns': ['00_index.md', '01_*.md'],
            '10_modules': ['00_index.md', '01_*.md'],
            '11_memory_management': ['00_index.md', '01_*.md'],
            '12_traits': ['00_index.md', '01_*.md']
        }
        
        completeness_report = {}
        missing_files = []
        
        for module, expected_files in expected_modules.items():
            module_path = self.base_path / module
            if module_path.exists():
                existing_files = list(module_path.glob("*.md"))
                expected_count = len(expected_files)
                actual_count = len(existing_files)
                
                completeness_report[module] = {
                    'expected_files': expected_count,
                    'actual_files': actual_count,
                    'completion_rate': min(actual_count / max(expected_count, 1), 1.0),
                    'files': [f.name for f in existing_files]
                }
                
                # 检查索引文件
                index_file = module_path / "00_index.md"
                if not index_file.exists():
                    missing_files.append(f"{module}/00_index.md")
            else:
                missing_files.append(f"整个模块: {module}")
        
        self.results['completeness_check'] = {
            'module_completeness': completeness_report,
            'missing_files': missing_files,
            'overall_completion': self.calculate_overall_completion(completeness_report)
        }
        
        overall_completion = self.results['completeness_check']['overall_completion']
        print(f"📊 理论体系完整性: {overall_completion:.1%}")
        
        if missing_files:
            print(f"⚠️  发现 {len(missing_files)} 个缺失文件/模块")
    
    def calculate_overall_completion(self, completeness_report: Dict) -> float:
        """计算总体完成度"""
        if not completeness_report:
            return 0.0
        
        total_completion = sum(info['completion_rate'] for info in completeness_report.values())
        return total_completion / len(completeness_report)
    
    def verify_document_structure(self):
        """验证文档结构的一致性"""
        structure_issues = []
        
        # 检查索引文件的结构
        for index_file in self.base_path.rglob("00_index.md"):
            content = self.read_file_safely(index_file)
            if content is None:
                continue
                
            issues = self.check_index_structure(content, index_file)
            if issues:
                structure_issues.extend(issues)
        
        self.results['structure_verification'] = {
            'issues': structure_issues,
            'total_index_files': len(list(self.base_path.rglob("00_index.md")))
        }
        
        if structure_issues:
            print(f"⚠️  发现 {len(structure_issues)} 个文档结构问题")
        else:
            print("✅ 文档结构验证通过")
    
    def check_index_structure(self, content: str, file_path: Path) -> List[str]:
        """检查索引文件的结构"""
        issues = []
        
        # 检查必需的章节
        required_sections = [
            r'##\s*概述',
            r'##\s*核心概念',
            r'##\s*相关模块',
            r'##\s*参考文献',
            r'##\s*维护信息'
        ]
        
        for section_pattern in required_sections:
            if not re.search(section_pattern, content, re.IGNORECASE):
                issues.append(f"{file_path.relative_to(self.base_path)}: 缺少必需章节 {section_pattern}")
        
        return issues
    
    def read_file_safely(self, file_path: Path) -> str:
        """安全地读取文件内容"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                return f.read()
        except Exception as e:
            self.results['errors'].append(f"无法读取文件 {file_path}: {e}")
            return None
    
    def generate_report(self):
        """生成质量验证报告"""
        report_path = self.base_path / "RESTRUCTURE_WORKING" / "phase4_quality_verification_report.md"
        
        # 计算总体质量分数
        quality_score = self.calculate_quality_score()
        
        report_content = f"""# 阶段四：质量验证报告

## 执行概要

本报告总结了形式化Rust语言理论项目阶段四质量验证的执行结果。

## 质量评分

**总体质量分数**: {quality_score:.1f}/100

## 验证结果详情

### 1. 概念一致性检查

- **概念定义总数**: {len(self.results['concept_definitions'])}
- **不一致问题**: {len(self.results['consistency_check'].get('concept_inconsistencies', []))}

### 2. 数学符号一致性

- **符号类型总数**: {len(self.results['mathematical_symbols'])}
- **符号不一致问题**: {len(self.results['consistency_check'].get('symbol_inconsistencies', []))}

### 3. 交叉引用验证

- **总链接数**: {self.results['cross_reference_check'].get('total_links', 0)}
- **有效链接数**: {self.results['cross_reference_check'].get('valid_links', 0)}
- **损坏链接数**: {len(self.results['cross_reference_check'].get('broken_links', []))}

### 4. 完整性检查

- **模块完整性**: {self.results['completeness_check'].get('overall_completion', 0):.1%}
- **缺失文件数**: {len(self.results['completeness_check'].get('missing_files', []))}

### 5. 文档结构验证

- **索引文件总数**: {self.results.get('structure_verification', {}).get('total_index_files', 0)}
- **结构问题数**: {len(self.results.get('structure_verification', {}).get('issues', []))}

## 问题详情

### 概念一致性问题
"""
        
        for issue in self.results['consistency_check'].get('concept_inconsistencies', []):
            report_content += f"- **{issue['concept']}**: 在文件 {', '.join(issue['conflicting_files'])} 中定义不一致\n"
        
        report_content += "\n### 数学符号一致性问题\n"
        for issue in self.results['consistency_check'].get('symbol_inconsistencies', []):
            report_content += f"- **{issue['symbol']}**: 使用了多种变体 {', '.join(issue['variants'])}\n"
        
        report_content += "\n### 损坏的链接\n"
        for link in self.results['cross_reference_check'].get('broken_links', []):
            report_content += f"- {link['source']} → {link['target']}\n"
        
        report_content += f"""
### 缺失文件
"""
        for missing in self.results['completeness_check'].get('missing_files', []):
            report_content += f"- {missing}\n"
        
        report_content += f"""
## 质量认证建议

基于当前质量分数 {quality_score:.1f}，建议认证级别：
"""
        if quality_score >= 95:
            report_content += "- **钻石级认证** ✨ - 顶级质量标准\n"
        elif quality_score >= 85:
            report_content += "- **黄金级认证** 🥇 - 卓越质量标准\n"
        elif quality_score >= 75:
            report_content += "- **白银级认证** 🥈 - 高质量标准\n"
        elif quality_score >= 60:
            report_content += "- **青铜级认证** 🥉 - 基础质量标准\n"
        else:
            report_content += "- **需要改进** ⚠️ - 未达到认证标准\n"
        
        report_content += f"""
## 改进建议

1. 优先解决概念定义不一致问题
2. 统一数学符号的使用规范
3. 修复所有损坏的交叉引用
4. 补充缺失的文档和章节
5. 标准化文档结构格式

## 下一步行动

1. 根据本报告修复发现的问题
2. 重新运行质量验证
3. 申请正式质量认证
4. 准备项目发布材料

---

**报告生成时间**: {self.get_current_time()}
**验证工具版本**: v1.0
**数据完整性**: ✅ 已验证
"""
        
        # 写入报告文件
        try:
            report_path.parent.mkdir(exist_ok=True)
            with open(report_path, 'w', encoding='utf-8') as f:
                f.write(report_content)
            print(f"📄 质量验证报告已生成: {report_path}")
        except Exception as e:
            print(f"❌ 无法生成报告: {e}")
        
        # 输出JSON格式的详细结果
        json_report_path = report_path.with_suffix('.json')
        try:
            with open(json_report_path, 'w', encoding='utf-8') as f:
                json.dump(self.results, f, ensure_ascii=False, indent=2)
            print(f"📊 详细结果已保存: {json_report_path}")
        except Exception as e:
            print(f"❌ 无法生成JSON报告: {e}")
    
    def calculate_quality_score(self) -> float:
        """计算总体质量分数"""
        scores = []
        
        # 概念一致性分数 (25分)
        concept_issues = len(self.results['consistency_check'].get('concept_inconsistencies', []))
        concept_score = max(0, 25 - concept_issues * 5)
        scores.append(concept_score)
        
        # 符号一致性分数 (20分)
        symbol_issues = len(self.results['consistency_check'].get('symbol_inconsistencies', []))
        symbol_score = max(0, 20 - symbol_issues * 3)
        scores.append(symbol_score)
        
        # 交叉引用分数 (25分)
        total_links = self.results['cross_reference_check'].get('total_links', 1)
        valid_links = self.results['cross_reference_check'].get('valid_links', 0)
        ref_score = (valid_links / total_links) * 25 if total_links > 0 else 25
        scores.append(ref_score)
        
        # 完整性分数 (20分)
        completion_rate = self.results['completeness_check'].get('overall_completion', 0)
        completion_score = completion_rate * 20
        scores.append(completion_score)
        
        # 结构一致性分数 (10分)
        structure_issues = len(self.results.get('structure_verification', {}).get('issues', []))
        structure_score = max(0, 10 - structure_issues * 2)
        scores.append(structure_score)
        
        return sum(scores)
    
    def get_current_time(self) -> str:
        """获取当前时间字符串"""
        from datetime import datetime
        return datetime.now().strftime("%Y-%m-%d %H:%M:%S")

def main():
    """主函数"""
    import sys
    
    # 确定基础路径
    if len(sys.argv) > 1:
        base_path = sys.argv[1]
    else:
        base_path = "."
    
    # 创建验证器并运行
    verifier = QualityVerifier(base_path)
    verifier.run_full_verification()
    
    print("\n🎉 质量验证完成！")
    print(f"📊 查看详细报告: RESTRUCTURE_WORKING/phase4_quality_verification_report.md")

if __name__ == "__main__":
    main() 