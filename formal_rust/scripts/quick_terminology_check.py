#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Rust形式化理论项目快速术语检查工具

专注于检查关键术语的一致性和禁用术语的使用
"""

import os
import re
from pathlib import Path
from collections import Counter

class QuickTerminologyChecker:
    def __init__(self):
        # 关键术语映射
        self.key_terms = {
            "trait": "特征",
            "ownership": "所有权",
            "borrowing": "借用",
            "lifetime": "生命周期",
            "generic": "泛型",
            "async": "异步",
            "await": "等待",
            "Result": "结果",
            "Option": "选项",
            "Box": "装箱",
            "Arc": "原子引用计数",
            "Mutex": "互斥锁",
        }
        
        # 禁用术语
        self.forbidden_terms = {
            "特质": "特征",
            "寿命": "生命周期",
            "引用": "借用",
            "方法": "函数",
            "类": "结构体/枚举",
            "继承": "组合",
        }
    
    def check_file(self, file_path: Path):
        """检查单个文件"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
        except UnicodeDecodeError:
            return None
        
        issues = []
        term_counts = Counter()
        
        # 检查禁用术语
        for forbidden, recommended in self.forbidden_terms.items():
            if forbidden in content:
                issues.append(f"禁用术语: '{forbidden}' -> '{recommended}'")
        
        # 检查关键术语
        for eng, chn in self.key_terms.items():
            eng_count = len(re.findall(rf'\b{re.escape(eng)}\b', content, re.IGNORECASE))
            chn_count = len(re.findall(rf'\b{re.escape(chn)}\b', content))
            
            if eng_count > 0:
                term_counts[eng] = eng_count
            if chn_count > 0:
                term_counts[chn] = chn_count
        
        return {
            'file': str(file_path),
            'issues': issues,
            'term_counts': dict(term_counts)
        }
    
    def check_project(self, project_root: str = "."):
        """检查整个项目"""
        project_path = Path(project_root)
        results = []
        total_issues = 0
        global_term_counts = Counter()
        
        # 检查所有markdown文件
        for md_file in project_path.rglob("*.md"):
            if any(skip in str(md_file) for skip in ['.git', 'node_modules', 'target']):
                continue
            
            result = self.check_file(md_file)
            if result:
                results.append(result)
                total_issues += len(result['issues'])
                global_term_counts.update(result['term_counts'])
        
        return {
            'total_files': len(results),
            'total_issues': total_issues,
            'results': results,
            'global_terms': dict(global_term_counts)
        }
    
    def generate_summary(self, check_results):
        """生成摘要报告"""
        summary = []
        summary.append("# Rust形式化理论项目术语检查摘要")
        summary.append("")
        summary.append(f"**检查文件数**: {check_results['total_files']}")
        summary.append(f"**发现问题数**: {check_results['total_issues']}")
        summary.append("")
        
        # 问题统计
        if check_results['total_issues'] > 0:
            summary.append("## 发现的问题")
            summary.append("")
            for result in check_results['results']:
                if result['issues']:
                    summary.append(f"### {result['file']}")
                    for issue in result['issues']:
                        summary.append(f"- {issue}")
                    summary.append("")
        
        # 术语使用统计
        summary.append("## 术语使用统计 (前20个)")
        summary.append("")
        summary.append("| 术语 | 使用次数 |")
        summary.append("|------|----------|")
        for term, count in check_results['global_terms'].most_common(20):
            summary.append(f"| {term} | {count} |")
        
        return "\n".join(summary)

def main():
    checker = QuickTerminologyChecker()
    results = checker.check_project(".")
    summary = checker.generate_summary(results)
    
    # 保存摘要报告
    with open("terminology_summary.md", "w", encoding="utf-8") as f:
        f.write(summary)
    
    print("术语检查完成！")
    print(f"检查文件数: {results['total_files']}")
    print(f"发现问题数: {results['total_issues']}")
    print("详细报告已保存到: terminology_summary.md")

if __name__ == "__main__":
    main()
