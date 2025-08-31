#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Rust形式化理论项目术语一致性检查工具

功能：
1. 检查文档中的术语使用一致性
2. 识别禁用术语的使用
3. 验证术语引用格式
4. 生成术语使用统计报告
"""

import os
import re
import json
import argparse
from pathlib import Path
from typing import Dict, List, Set, Tuple
from collections import defaultdict, Counter

class TerminologyChecker:
    def __init__(self, project_root: str):
        self.project_root = Path(project_root)
        self.terminology_dict = self._load_terminology_dict()
        self.forbidden_terms = self._load_forbidden_terms()
        self.stats = Counter()
        
    def _load_terminology_dict(self) -> Dict[str, str]:
        """加载术语词典"""
        terminology = {
            # 所有权系统
            "ownership": "所有权",
            "borrowing": "借用", 
            "move semantics": "移动语义",
            "copy semantics": "复制语义",
            "drop": "析构",
            "borrow checker": "借用检查器",
            "lifetime": "生命周期",
            "lifetime elision": "生命周期省略",
            
            # 类型系统
            "trait": "特征",
            "generic": "泛型",
            "associated type": "关联类型",
            "const generic": "常量泛型",
            "type inference": "类型推断",
            "type safety": "类型安全",
            "type coercion": "类型强制转换",
            "variance": "变型",
            
            # 高级类型特征
            "GAT": "泛型关联类型",
            "higher-kinded types": "高阶类型",
            "dependent types": "依赖类型",
            "type-level programming": "类型级编程",
            "phantom types": "幻影类型",
            
            # 并发系统
            "async": "异步",
            "await": "等待",
            "future": "未来值",
            "executor": "执行器",
            "spawn": "生成",
            "Send": "发送",
            "Sync": "同步",
            "Arc": "原子引用计数",
            "Mutex": "互斥锁",
            
            # 内存管理
            "stack": "栈",
            "heap": "堆",
            "allocation": "分配",
            "deallocation": "释放",
            "memory safety": "内存安全",
            "Box": "装箱",
            "Rc": "引用计数",
            "Weak": "弱引用",
            
            # 错误处理
            "Result": "结果",
            "Option": "选项",
            "unwrap": "解包",
            "panic": "恐慌",
            "error propagation": "错误传播",
            
            # 形式化验证
            "formal semantics": "形式化语义",
            "type soundness": "类型可靠性",
            "progress": "进展性",
            "preservation": "保持性",
            "borrow checking": "借用检查",
            "lifetime analysis": "生命周期分析",
            
            # 工具链生态
            "rustc": "Rust编译器",
            "cargo": "包管理器",
            "rust-analyzer": "语言服务器",
            "clippy": "代码检查工具",
            "rustfmt": "代码格式化工具",
            
            # 宏系统
            "macro": "宏",
            "declarative macro": "声明宏",
            "procedural macro": "过程宏",
            "derive macro": "派生宏",
            "macro_rules": "宏规则",
            
            # 模块系统
            "module": "模块",
            "crate": "包",
            "workspace": "工作空间",
            "visibility": "可见性",
            "pub": "公开",
        }
        return terminology
    
    def _load_forbidden_terms(self) -> Dict[str, str]:
        """加载禁用术语"""
        forbidden = {
            "特质": "特征",
            "寿命": "生命周期",
            "引用": "借用",
            "易变性": "可变性",
            "方法": "函数",
            "类": "结构体/枚举",
            "继承": "组合",
            "属性": "特征",
            "property": "trait",
            "method": "function",
            "class": "struct/enum",
            "inheritance": "composition",
            "pointer": "reference/borrow",
        }
        return forbidden
    
    def check_file(self, file_path: Path) -> Dict:
        """检查单个文件的术语使用"""
        if not file_path.exists() or file_path.suffix != '.md':
            return {}
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except UnicodeDecodeError:
            try:
                with open(file_path, 'r', encoding='gbk') as f:
                    content = f.read()
            except UnicodeDecodeError:
                with open(file_path, 'r', encoding='latin-1') as f:
                    content = f.read()
        
        issues = []
        term_usage = defaultdict(int)
        
        # 检查禁用术语
        for forbidden, recommended in self.forbidden_terms.items():
            matches = re.finditer(rf'\b{re.escape(forbidden)}\b', content, re.IGNORECASE)
            for match in matches:
                issues.append({
                    'type': 'forbidden_term',
                    'term': forbidden,
                    'recommended': recommended,
                    'line': content[:match.start()].count('\n') + 1,
                    'context': self._get_context(content, match.start(), 50)
                })
        
        # 检查术语使用一致性
        for eng_term, chn_term in self.terminology_dict.items():
            # 检查英文术语
            eng_matches = re.finditer(rf'\b{re.escape(eng_term)}\b', content, re.IGNORECASE)
            for match in eng_matches:
                term_usage[eng_term] += 1
                # 检查是否有中文对照
                if not self._has_chinese_counterpart(content, match.start(), chn_term):
                    issues.append({
                        'type': 'missing_chinese',
                        'term': eng_term,
                        'chinese': chn_term,
                        'line': content[:match.start()].count('\n') + 1,
                        'context': self._get_context(content, match.start(), 50)
                    })
            
            # 检查中文术语
            chn_matches = re.finditer(rf'\b{re.escape(chn_term)}\b', content)
            for match in chn_matches:
                term_usage[chn_term] += 1
        
        return {
            'file': str(file_path.relative_to(self.project_root)),
            'issues': issues,
            'term_usage': dict(term_usage)
        }
    
    def _has_chinese_counterpart(self, content: str, pos: int, chn_term: str) -> bool:
        """检查英文术语附近是否有中文对照"""
        start = max(0, pos - 100)
        end = min(len(content), pos + 100)
        context = content[start:end]
        
        # 检查是否有中文术语
        if chn_term in context:
            return True
        
        # 检查是否有括号格式的中文对照
        pattern = rf'\([^)]*{re.escape(chn_term)}[^)]*\)'
        if re.search(pattern, context):
            return True
        
        return False
    
    def _get_context(self, content: str, pos: int, width: int) -> str:
        """获取术语周围的上下文"""
        start = max(0, pos - width)
        end = min(len(content), pos + width)
        return content[start:end].replace('\n', ' ').strip()
    
    def check_directory(self, directory: str = None) -> Dict:
        """检查整个目录的术语使用"""
        if directory is None:
            directory = self.project_root
        
        dir_path = Path(directory)
        results = []
        total_issues = 0
        
        # 遍历所有markdown文件
        for md_file in dir_path.rglob('*.md'):
            if 'node_modules' in str(md_file) or '.git' in str(md_file):
                continue
            
            result = self.check_file(md_file)
            if result:
                results.append(result)
                total_issues += len(result['issues'])
                
                # 更新统计
                for term, count in result['term_usage'].items():
                    self.stats[term] += count
        
        return {
            'total_files': len(results),
            'total_issues': total_issues,
            'results': results,
            'statistics': dict(self.stats)
        }
    
    def generate_report(self, check_results: Dict) -> str:
        """生成检查报告"""
        report = []
        report.append("# Rust形式化理论项目术语一致性检查报告")
        report.append("")
        report.append(f"**检查时间**: {self._get_current_time()}")
        report.append(f"**检查文件数**: {check_results['total_files']}")
        report.append(f"**发现问题数**: {check_results['total_issues']}")
        report.append("")
        
        # 问题分类统计
        issue_types = defaultdict(int)
        for result in check_results['results']:
            for issue in result['issues']:
                issue_types[issue['type']] += 1
        
        report.append("## 问题分类统计")
        report.append("")
        for issue_type, count in issue_types.items():
            report.append(f"- {issue_type}: {count}个")
        report.append("")
        
        # 术语使用统计
        report.append("## 术语使用统计")
        report.append("")
        report.append("| 术语 | 使用次数 |")
        report.append("|------|----------|")
        for term, count in sorted(check_results['statistics'].items(), key=lambda x: x[1], reverse=True)[:20]:
            report.append(f"| {term} | {count} |")
        report.append("")
        
        # 详细问题列表
        report.append("## 详细问题列表")
        report.append("")
        for result in check_results['results']:
            if result['issues']:
                report.append(f"### {result['file']}")
                report.append("")
                for issue in result['issues']:
                    report.append(f"- **{issue['type']}**: {issue['term']}")
                    if 'recommended' in issue:
                        report.append(f"  - 建议使用: {issue['recommended']}")
                    if 'chinese' in issue:
                        report.append(f"  - 中文对照: {issue['chinese']}")
                    report.append(f"  - 行号: {issue['line']}")
                    report.append(f"  - 上下文: `{issue['context']}`")
                    report.append("")
        
        return "\n".join(report)
    
    def _get_current_time(self) -> str:
        """获取当前时间"""
        from datetime import datetime
        return datetime.now().strftime("%Y-%m-%d %H:%M:%S")

def main():
    parser = argparse.ArgumentParser(description='Rust形式化理论项目术语一致性检查工具')
    parser.add_argument('--project-root', default='.', help='项目根目录')
    parser.add_argument('--output', help='输出报告文件路径')
    parser.add_argument('--recursive', action='store_true', help='递归检查子目录')
    
    args = parser.parse_args()
    
    checker = TerminologyChecker(args.project_root)
    
    if args.recursive:
        results = checker.check_directory()
    else:
        results = checker.check_directory(args.project_root)
    
    report = checker.generate_report(results)
    
    if args.output:
        with open(args.output, 'w', encoding='utf-8') as f:
            f.write(report)
        print(f"报告已保存到: {args.output}")
    else:
        print(report)

if __name__ == '__main__':
    main()
