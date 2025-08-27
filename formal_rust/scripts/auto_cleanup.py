#!/usr/bin/env python3
"""
Rust形式化理论项目自动清理脚本
直接执行清理操作，无需用户交互
"""

import os
import re
from pathlib import Path
from typing import List, Tuple

class AutoCleaner:
    def __init__(self, root_dir: str = "."):
        self.root_dir = Path(root_dir)
        self.low_quality_files = []
        self.duplicate_files = []
        self.cleaned_count = 0
        
    def scan_and_clean(self) -> int:
        """扫描并自动清理低质量文件"""
        print("🔍 开始扫描文件...")
        
        all_files = []
        file_contents = {}
        
        for file_path in self.root_dir.rglob("*.md"):
            if file_path.is_file():
                try:
                    content = file_path.read_text(encoding='utf-8')
                    all_files.append(str(file_path))
                    
                    # 检查文件质量
                    if self.is_low_quality(content):
                        self.low_quality_files.append(str(file_path))
                    
                    # 检查重复内容
                    content_hash = self.get_content_hash(content)
                    if content_hash in file_contents:
                        self.duplicate_files.append(str(file_path))
                    else:
                        file_contents[content_hash] = str(file_path)
                        
                except Exception as e:
                    print(f"⚠️ 读取文件失败: {file_path} - {e}")
        
        print(f"\n📊 扫描结果:")
        print(f"  低质量文件: {len(self.low_quality_files)} 个")
        print(f"  重复文件: {len(self.duplicate_files)} 个")
        
        # 自动清理低质量文件
        print(f"\n🗑️ 开始自动清理低质量文件...")
        for file_path in self.low_quality_files:
            try:
                # 跳过一些重要文件
                if self.should_skip_file(file_path):
                    print(f"  跳过重要文件: {file_path}")
                    continue
                    
                os.remove(file_path)
                print(f"  已删除: {file_path}")
                self.cleaned_count += 1
            except Exception as e:
                print(f"⚠️ 删除失败: {file_path} - {e}")
        
        return self.cleaned_count
    
    def should_skip_file(self, file_path: str) -> bool:
        """判断是否应该跳过某些重要文件"""
        skip_patterns = [
            "README.md",
            "index.md",
            "overview.md",
            "EXECUTION_PLAN",
            "TERMINOLOGY_STANDARD",
            "quality_cleanup_report.md"
        ]
        
        for pattern in skip_patterns:
            if pattern in file_path:
                return True
        return False
    
    def is_low_quality(self, content: str) -> bool:
        """判断文件是否为低质量"""
        lines = content.strip().split('\n')
        
        # 检查行数
        if len(lines) < 50:
            return True
        
        # 检查内容是否为空或只有标题
        non_empty_lines = [line for line in lines if line.strip() and not line.startswith('#')]
        if len(non_empty_lines) < 20:
            return True
        
        # 检查是否只有简单列表
        if len(re.findall(r'^- ', content)) > len(non_empty_lines) * 0.8:
            return True
        
        return False
    
    def get_content_hash(self, content: str) -> str:
        """获取内容的哈希值，用于检测重复"""
        # 移除空白字符和注释
        cleaned = re.sub(r'\s+', ' ', content.strip())
        cleaned = re.sub(r'<!--.*?-->', '', cleaned)
        return cleaned
    
    def generate_cleanup_report(self) -> str:
        """生成清理报告"""
        report = f"""
# 自动清理报告

## 清理结果
- 扫描目录: {self.root_dir}
- 发现低质量文件: {len(self.low_quality_files)} 个
- 发现重复文件: {len(self.duplicate_files)} 个
- 实际清理文件: {self.cleaned_count} 个

## 清理统计
- 清理成功率: {self.cleaned_count / len(self.low_quality_files) * 100:.1f}%
- 剩余文件: {len(self.low_quality_files) - self.cleaned_count} 个

## 清理完成时间
- 清理时间: {__import__('datetime').datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

**状态**: ✅ 自动清理完成
"""
        return report

def main():
    """主函数"""
    cleaner = AutoCleaner()
    
    # 执行自动清理
    cleaned_count = cleaner.scan_and_clean()
    
    # 生成报告
    report = cleaner.generate_cleanup_report()
    with open("auto_cleanup_report.md", "w", encoding='utf-8') as f:
        f.write(report)
    
    print(f"\n📄 清理报告已保存到: auto_cleanup_report.md")
    print(f"\n✅ 自动清理完成! 共清理 {cleaned_count} 个文件")

if __name__ == "__main__":
    main()
