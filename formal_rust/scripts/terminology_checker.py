#!/usr/bin/env python3
"""
Rust形式化理论项目术语检查工具
检查并修正术语不一致问题
"""

import os
import re
from pathlib import Path
from typing import Dict, List, Tuple

class TerminologyChecker:
    def __init__(self, root_dir: str = "."):
        self.root_dir = Path(root_dir)
        self.terminology_dict = {
            # 所有权系统
            "ownership": "所有权",
            "borrowing": "借用",
            "move semantics": "移动语义",
            "copy semantics": "复制语义",
            "drop": "析构",
            
            # 类型系统
            "trait": "特征",
            "lifetime": "生命周期",
            "generic": "泛型",
            "associated type": "关联类型",
            "const generic": "常量泛型",
            "GATs": "泛型关联类型",
            
            # 并发系统
            "async": "异步",
            "await": "等待",
            "future": "未来值",
            "executor": "执行器",
            "spawn": "生成",
            
            # 内存管理
            "stack": "栈",
            "heap": "堆",
            "allocation": "分配",
            "deallocation": "释放",
            "memory safety": "内存安全",
            
            # 错误处理
            "Result": "结果",
            "Option": "选项",
            "unwrap": "解包",
            "panic": "恐慌",
        }
        
        self.forbidden_terms = {
            "特质": "特征",
            "寿命": "生命周期",
            "引用": "借用",
            "易变性": "可变性",
        }
        
        self.issues = []
        
    def scan_terminology_issues(self) -> List[Dict]:
        """扫描术语问题"""
        print("🔍 开始扫描术语问题...")
        
        for file_path in self.root_dir.rglob("*.md"):
            if file_path.is_file():
                try:
                    content = file_path.read_text(encoding='utf-8')
                    file_issues = self.check_file_terminology(str(file_path), content)
                    self.issues.extend(file_issues)
                except Exception as e:
                    print(f"⚠️ 读取文件失败: {file_path} - {e}")
        
        return self.issues
    
    def check_file_terminology(self, file_path: str, content: str) -> List[Dict]:
        """检查单个文件的术语问题"""
        issues = []
        
        # 检查禁用术语
        for forbidden, correct in self.forbidden_terms.items():
            if forbidden in content:
                issues.append({
                    "file": file_path,
                    "type": "forbidden_term",
                    "issue": f"使用了禁用术语 '{forbidden}'，应改为 '{correct}'",
                    "line": self.find_line_number(content, forbidden)
                })
        
        # 检查术语一致性
        for english, chinese in self.terminology_dict.items():
            # 检查是否同时使用了英文和中文术语
            if english in content and chinese in content:
                issues.append({
                    "file": file_path,
                    "type": "mixed_terminology",
                    "issue": f"同时使用了英文术语 '{english}' 和中文术语 '{chinese}'",
                    "line": self.find_line_number(content, english)
                })
        
        return issues
    
    def find_line_number(self, content: str, term: str) -> int:
        """查找术语所在行号"""
        lines = content.split('\n')
        for i, line in enumerate(lines, 1):
            if term in line:
                return i
        return 0
    
    def generate_report(self) -> str:
        """生成术语检查报告"""
        report = f"""
# 术语检查报告

## 检查结果
- 扫描目录: {self.root_dir}
- 发现问题: {len(self.issues)} 个

## 问题分类
"""
        
        forbidden_count = len([i for i in self.issues if i["type"] == "forbidden_term"])
        mixed_count = len([i for i in self.issues if i["type"] == "mixed_terminology"])
        
        report += f"""
- 禁用术语问题: {forbidden_count} 个
- 术语混用问题: {mixed_count} 个

## 详细问题列表
"""
        
        for issue in self.issues:
            report += f"""
### {issue['file']} (第{issue['line']}行)
- 问题类型: {issue['type']}
- 问题描述: {issue['issue']}
"""
        
        return report

def main():
    """主函数"""
    checker = TerminologyChecker()
    
    # 扫描术语问题
    issues = checker.scan_terminology_issues()
    
    print(f"\n📊 术语检查结果:")
    print(f"  发现问题: {len(issues)} 个")
    
    # 生成报告
    report = checker.generate_report()
    with open("terminology_check_report.md", "w", encoding='utf-8') as f:
        f.write(report)
    
    print(f"\n📄 术语检查报告已保存到: terminology_check_report.md")

if __name__ == "__main__":
    main()
