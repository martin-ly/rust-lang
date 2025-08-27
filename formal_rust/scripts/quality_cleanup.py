#!/usr/bin/env python3
"""
Rust形式化理论项目质量清理脚本
自动识别和清理低质量文件
"""

import os
import re
from pathlib import Path
from typing import List, Tuple

class QualityCleaner:
    def __init__(self, root_dir: str = "."):
        self.root_dir = Path(root_dir)
        self.low_quality_files = []
        self.duplicate_files = []
        
    def scan_files(self) -> Tuple[List[str], List[str]]:
        """扫描所有文件，识别低质量文件和重复文件"""
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
        
        return self.low_quality_files, self.duplicate_files
    
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
    
    def cleanup_low_quality_files(self, dry_run: bool = True) -> int:
        """清理低质量文件"""
        print(f"\n🗑️ 开始清理低质量文件 (dry_run={dry_run})...")
        
        cleaned_count = 0
        for file_path in self.low_quality_files:
            try:
                if dry_run:
                    print(f"  将删除: {file_path}")
                else:
                    os.remove(file_path)
                    print(f"  已删除: {file_path}")
                cleaned_count += 1
            except Exception as e:
                print(f"⚠️ 删除失败: {file_path} - {e}")
        
        return cleaned_count
    
    def merge_duplicate_files(self, dry_run: bool = True) -> int:
        """合并重复文件"""
        print(f"\n🔗 开始合并重复文件 (dry_run={dry_run})...")
        
        merged_count = 0
        # 这里可以实现更复杂的合并逻辑
        for file_path in self.duplicate_files:
            try:
                if dry_run:
                    print(f"  将合并: {file_path}")
                else:
                    # 实现合并逻辑
                    pass
                merged_count += 1
            except Exception as e:
                print(f"⚠️ 合并失败: {file_path} - {e}")
        
        return merged_count
    
    def generate_report(self) -> str:
        """生成清理报告"""
        report = f"""
# 质量清理报告

## 扫描结果
- 扫描目录: {self.root_dir}
- 低质量文件: {len(self.low_quality_files)} 个
- 重复文件: {len(self.duplicate_files)} 个

## 低质量文件列表
"""
        
        for file_path in self.low_quality_files:
            report += f"- {file_path}\n"
        
        report += "\n## 重复文件列表\n"
        for file_path in self.duplicate_files:
            report += f"- {file_path}\n"
        
        return report

def main():
    """主函数"""
    cleaner = QualityCleaner()
    
    # 扫描文件
    low_quality, duplicates = cleaner.scan_files()
    
    print(f"\n📊 扫描结果:")
    print(f"  低质量文件: {len(low_quality)} 个")
    print(f"  重复文件: {len(duplicates)} 个")
    
    # 生成报告
    report = cleaner.generate_report()
    with open("quality_cleanup_report.md", "w", encoding='utf-8') as f:
        f.write(report)
    
    print(f"\n📄 报告已保存到: quality_cleanup_report.md")
    
    # 询问是否执行清理
    if low_quality or duplicates:
        response = input("\n是否执行清理? (y/N): ")
        if response.lower() == 'y':
            cleaner.cleanup_low_quality_files(dry_run=False)
            cleaner.merge_duplicate_files(dry_run=False)
            print("\n✅ 清理完成!")
        else:
            print("\n⏸️ 清理已取消")
    else:
        print("\n✅ 没有发现需要清理的文件")

if __name__ == "__main__":
    main()
