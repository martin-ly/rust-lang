#!/usr/bin/env python3
"""
Rust语言形式化理论体系 - 快速维护脚本

本脚本提供快速维护功能，包括：
1. 快速链接检查
2. 重复文件检测
3. 目录结构验证
4. 质量报告生成

作者: Rust语言形式化理论项目组
版本: v2.0
日期: 2025年1月27日
"""

import os
import re
import json
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Set

def quick_link_check(base_path: str = "docs/language") -> Dict:
    """快速链接检查"""
    print("🔍 开始快速链接检查...")
    
    base = Path(base_path)
    broken_links = []
    total_links = 0
    
    # 收集所有文件
    all_files = set()
    for md_file in base.rglob("*.md"):
        all_files.add(md_file)
        
    for md_file in base.rglob("*.md"):
        try:
            with open(md_file, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # 查找链接
            links = re.findall(r'\[([^\]]+)\]\(([^)]+)\)', content)
            
            for link_text, target in links:
                total_links += 1
                
                # 跳过外部链接和锚点
                if target.startswith('http') or target.startswith('#'):
                    continue
                    
                # 检查相对路径
                if target.startswith('./') or target.startswith('../'):
                    target_path = md_file.parent / target
                else:
                    target_path = md_file.parent / target
                    
                if not target_path.exists():
                    broken_links.append({
                        'source': str(md_file),
                        'target': target,
                        'text': link_text
                    })
                    
        except Exception as e:
            print(f"❌ 处理文件失败 {md_file}: {e}")
            
    print(f"✅ 链接检查完成: {total_links} 个链接, {len(broken_links)} 个损坏")
    return {
        'total_links': total_links,
        'broken_links': broken_links,
        'broken_count': len(broken_links)
    }

def quick_duplicate_check(base_path: str = "docs/language") -> Dict:
    """快速重复文件检查"""
    print("🔍 开始快速重复文件检查...")
    
    base = Path(base_path)
    file_hashes = {}
    duplicates = []
    
    for md_file in base.rglob("*.md"):
        try:
            with open(md_file, 'r', encoding='utf-8') as f:
                content = f.read()
                
            # 简单哈希
            content_hash = hash(content)
            
            if content_hash in file_hashes:
                duplicates.append({
                    'hash': content_hash,
                    'files': [file_hashes[content_hash], str(md_file)]
                })
            else:
                file_hashes[content_hash] = str(md_file)
                
        except Exception as e:
            print(f"❌ 处理文件失败 {md_file}: {e}")
            
    print(f"✅ 重复文件检查完成: {len(duplicates)} 组重复文件")
    return {
        'duplicates': duplicates,
        'duplicate_count': len(duplicates)
    }

def quick_structure_check(base_path: str = "docs/language") -> Dict:
    """快速目录结构检查"""
    print("🔍 开始快速目录结构检查...")
    
    base = Path(base_path)
    issues = []
    
    # 检查必要目录
    required_dirs = [
        'core', 'advanced', 'system', 'applications', 
        'domains', 'research', 'ecosystem', 'verification',
        'navigation', 'archive'
    ]
    
    for dir_name in required_dirs:
        dir_path = base / dir_name
        if not dir_path.exists():
            issues.append(f"缺少目录: {dir_name}")
            
    # 检查模块索引文件
    for item in base.iterdir():
        if item.is_dir() and item.name.startswith(('01_', '02_', '03_', '04_', '05_', '06_', '07_', '08_', '09_', '10_', '11_', '12_', '13_', '14_', '15_', '16_', '17_', '18_', '19_', '20_', '21_', '22_', '23_', '24_', '25_', '26_', '27_', '28_')):
            index_file = item / '00_index.md'
            if not index_file.exists():
                issues.append(f"模块 {item.name} 缺少索引文件")
                
    print(f"✅ 目录结构检查完成: {len(issues)} 个问题")
    return {
        'issues': issues,
        'issue_count': len(issues)
    }

def generate_quick_report(base_path: str = "docs/language") -> Dict:
    """生成快速报告"""
    print("📊 开始生成快速报告...")
    
    # 运行检查
    link_result = quick_link_check(base_path)
    duplicate_result = quick_duplicate_check(base_path)
    structure_result = quick_structure_check(base_path)
    
    # 计算质量分数
    quality_score = 100
    
    # 链接质量 (40%)
    if link_result['total_links'] > 0:
        link_quality = (link_result['total_links'] - link_result['broken_count']) / link_result['total_links'] * 100
        quality_score -= (100 - link_quality) * 0.4
        
    # 重复文件 (30%)
    if duplicate_result['duplicate_count'] > 0:
        quality_score -= min(duplicate_result['duplicate_count'] * 5, 30)
        
    # 目录结构 (30%)
    if structure_result['issue_count'] > 0:
        quality_score -= min(structure_result['issue_count'] * 3, 30)
        
    report = {
        'timestamp': datetime.now().isoformat(),
        'quality_score': round(quality_score, 2),
        'link_check': link_result,
        'duplicate_check': duplicate_result,
        'structure_check': structure_result,
        'summary': {
            'total_links': link_result['total_links'],
            'broken_links': link_result['broken_count'],
            'duplicate_groups': duplicate_result['duplicate_count'],
            'structure_issues': structure_result['issue_count']
        }
    }
    
    # 保存报告
    output_path = Path(base_path) / "quick_quality_report.json"
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(report, f, ensure_ascii=False, indent=2)
        
    print(f"✅ 快速报告生成完成: {output_path}")
    print(f"📊 质量分数: {quality_score:.2f}")
    
    return report

def main():
    """主函数"""
    print("🚀 Rust语言形式化理论体系 - 快速维护脚本")
    print("=" * 50)
    
    # 生成快速报告
    report = generate_quick_report()
    
    print("\n📋 报告摘要:")
    print(f"  🔗 总链接数: {report['summary']['total_links']}")
    print(f"  ❌ 损坏链接: {report['summary']['broken_links']}")
    print(f"  📁 重复文件组: {report['summary']['duplicate_groups']}")
    print(f"  🏗️ 结构问题: {report['summary']['structure_issues']}")
    print(f"  📊 质量分数: {report['quality_score']}")
    
    if report['quality_score'] >= 90:
        print("🎉 质量优秀!")
    elif report['quality_score'] >= 80:
        print("✅ 质量良好")
    elif report['quality_score'] >= 70:
        print("⚠️ 质量一般，需要改进")
    else:
        print("❌ 质量较差，需要重点关注")

if __name__ == "__main__":
    main()
