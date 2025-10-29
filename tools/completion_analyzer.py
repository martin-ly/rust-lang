#!/usr/bin/env python3
"""
Rust 形式化工程系统 - 完成度统计脚本
扫描目录结构，生成真实的完成度报告
"""

import os
from pathlib import Path
from collections import defaultdict
import json

class CompletionAnalyzer:
    def __init__(self, root_dir):
        self.root_dir = Path(root_dir)
        self.stats = defaultdict(dict)
        self.total_files = 0
        self.total_lines = 0
        
    def analyze_directory(self, dir_path, module_name):
        """分析单个目录"""
        md_files = list(dir_path.glob("*.md"))
        rs_files = list(dir_path.glob("*.rs"))
        
        total_lines = 0
        placeholder_count = 0
        full_content_count = 0
        
        for md_file in md_files:
            try:
                with open(md_file, 'r', encoding='utf-8') as f:
                    lines = len(f.readlines())
                    total_lines += lines
                    
                    # 判断是否为占位符（≤100行）
                    if lines <= 100:
                        placeholder_count += 1
                    else:
                        full_content_count += 1
            except Exception as e:
                print(f"Warning: Could not read {md_file}: {e}")
        
        # 计算完成度
        total_files = len(md_files)
        if total_files == 0:
            completion = 0
        elif placeholder_count == total_files:
            completion = 10  # 只有占位符
        else:
            # 基于完整内容文件的比例
            completion = min(100, int((full_content_count / total_files) * 100))
        
        return {
            'total_files': total_files,
            'rs_files': len(rs_files),
            'total_lines': total_lines,
            'placeholder_count': placeholder_count,
            'full_content_count': full_content_count,
            'completion': completion
        }
    
    def scan(self):
        """扫描整个项目"""
        print("🔍 扫描 Rust 形式化工程系统...")
        
        # 一级目录
        for module_dir in sorted(self.root_dir.iterdir()):
            if not module_dir.is_dir() or module_dir.name.startswith('.'):
                continue
            
            module_name = module_dir.name
            print(f"  📁 {module_name}...")
            
            module_stats = self.analyze_directory(module_dir, module_name)
            
            # 扫描子目录
            subdirs = [d for d in module_dir.iterdir() if d.is_dir()]
            subdir_stats = []
            
            for subdir in sorted(subdirs):
                sub_stats = self.analyze_directory(subdir, subdir.name)
                subdir_stats.append({
                    'name': subdir.name,
                    **sub_stats
                })
            
            self.stats[module_name] = {
                'main': module_stats,
                'subdirs': subdir_stats
            }
            
            self.total_files += module_stats['total_files']
            self.total_lines += module_stats['total_lines']
        
        print(f"✅ 扫描完成: {self.total_files} 个 Markdown 文件, {self.total_lines} 行")
    
    def generate_report(self):
        """生成完成度报告"""
        report = []
        report.append("# Rust 形式化工程系统 - 真实完成度报告\n")
        report.append(f"**生成日期**: 2025-10-30\n")
        report.append(f"**Rust 版本**: 1.90.0\n\n")
        report.append("---\n\n")
        
        report.append("## 📊 总体统计\n\n")
        report.append(f"- **总文件数**: {self.total_files} 个 Markdown 文件\n")
        report.append(f"- **总行数**: {self.total_lines:,} 行\n")
        report.append(f"- **一级模块**: {len(self.stats)} 个\n\n")
        
        report.append("---\n\n")
        report.append("## 📈 各模块完成度\n\n")
        report.append("| 模块 | 文件数 | 完整文档 | 占位符 | 完成度 | 状态 |\n")
        report.append("|------|--------|---------|--------|--------|------|\n")
        
        total_completion = 0
        for module_name, module_data in sorted(self.stats.items()):
            main = module_data['main']
            completion = main['completion']
            total_completion += completion
            
            status = "✅" if completion >= 80 else "⚠️" if completion >= 50 else "❌"
            
            report.append(f"| {module_name} | {main['total_files']} | {main['full_content_count']} | {main['placeholder_count']} | {completion}% | {status} |\n")
        
        avg_completion = total_completion / len(self.stats) if self.stats else 0
        
        report.append(f"\n**平均完成度**: {avg_completion:.1f}%\n\n")
        
        report.append("---\n\n")
        report.append("## 🔍 详细分析\n\n")
        
        for module_name, module_data in sorted(self.stats.items()):
            main = module_data['main']
            subdirs = module_data['subdirs']
            
            report.append(f"### {module_name}\n\n")
            report.append(f"- **文件数**: {main['total_files']}\n")
            report.append(f"- **代码文件**: {main['rs_files']}\n")
            report.append(f"- **总行数**: {main['total_lines']:,}\n")
            report.append(f"- **完整文档**: {main['full_content_count']}\n")
            report.append(f"- **占位符**: {main['placeholder_count']}\n")
            report.append(f"- **完成度**: {main['completion']}%\n\n")
            
            if subdirs:
                report.append("**子目录**:\n\n")
                for subdir in subdirs[:10]:  # 只显示前10个
                    report.append(f"- `{subdir['name']}`: {subdir['total_files']} 文件, {subdir['completion']}% 完成\n")
                if len(subdirs) > 10:
                    report.append(f"- ... 还有 {len(subdirs) - 10} 个子目录\n")
                report.append("\n")
        
        report.append("---\n\n")
        report.append("## 💡 建议\n\n")
        report.append("### 高优先级（立即改进）\n\n")
        report.append("1. **版本同步**: 更新所有文档中的 Rust 版本号（1.89 → 1.90）\n")
        report.append("2. **完成度重评**: 基于实际内容重新评估完成度\n")
        report.append("3. **占位符标注**: 明确标注占位符文件，提供替代资源\n\n")
        
        report.append("### 中优先级（本月完成）\n\n")
        report.append("1. **核心模块完善**: 优先完善完成度 < 50% 的核心模块\n")
        report.append("2. **主项目整合**: 与 `crates/` 建立双向链接\n")
        report.append("3. **内容审核**: 建立内容质量标准\n\n")
        
        report.append("### 低优先级（3个月内）\n\n")
        report.append("1. **扩展模块**: 逐步完善占位符目录\n")
        report.append("2. **工具更新**: 更新工具链文档\n")
        report.append("3. **社区化**: 建立贡献机制\n\n")
        
        report.append("---\n\n")
        report.append("**报告生成**: 2025-10-30\n")
        report.append("**生成工具**: completion_analyzer.py\n")
        
        return "".join(report)
    
    def save_report(self, output_file='COMPLETION_STATUS_REAL.md'):
        """保存报告"""
        report_content = self.generate_report()
        output_path = self.root_dir / output_file
        
        with open(output_path, 'w', encoding='utf-8') as f:
            f.write(report_content)
        
        print(f"\n✅ 完成度报告已保存: {output_path}")
        
        # 同时保存 JSON 格式
        json_path = self.root_dir / 'completion_stats.json'
        json_data = {
            'generated_date': '2025-10-30',
            'total_files': self.total_files,
            'total_lines': self.total_lines,
            'modules': {}
        }
        
        for module_name, module_data in self.stats.items():
            json_data['modules'][module_name] = {
                'completion': module_data['main']['completion'],
                'files': module_data['main']['total_files'],
                'lines': module_data['main']['total_lines']
            }
        
        with open(json_path, 'w', encoding='utf-8') as f:
            json.dump(json_data, f, indent=2, ensure_ascii=False)
        
        print(f"✅ 统计数据已保存: {json_path}")

def main():
    import sys
    
    # 获取项目根目录
    script_dir = Path(__file__).parent
    project_root = script_dir.parent
    formal_system_dir = project_root / 'docs' / 'rust-formal-engineering-system'
    
    if not formal_system_dir.exists():
        print(f"❌ 错误: 未找到目录 {formal_system_dir}")
        sys.exit(1)
    
    print("📊 Rust 形式化工程系统 - 完成度分析器")
    print("━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n")
    
    analyzer = CompletionAnalyzer(formal_system_dir)
    analyzer.scan()
    analyzer.save_report()
    
    print("\n🎉 分析完成！")

if __name__ == '__main__':
    main()

