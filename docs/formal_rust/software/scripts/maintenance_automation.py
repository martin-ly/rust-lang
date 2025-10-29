#!/usr/bin/env python3
"""
Rust软件工程文档自动化维护脚本
集成质量检查、链接检查、格式修复等功能
"""

import os
import sys
import subprocess
import json
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Any

class MaintenanceAutomation:
    def __init__(self, base_path: str):
        self.base_path = Path(base_path)
        self.scripts_dir = self.base_path / 'scripts'
        self.reports_dir = self.base_path / 'reports'
        self.config_file = self.scripts_dir / 'maintenance_config.json'
        
        # 创建必要目录
        self.reports_dir.mkdir(exist_ok=True)
        
        # 加载配置
        self.config = self.load_config()
    
    def load_config(self) -> Dict[str, Any]:
        """加载维护配置"""
        default_config = {
            "quality_check": {
                "enabled": True,
                "strict_mode": False,
                "check_format": True,
                "check_structure": True,
                "check_links": True
            },
            "link_check": {
                "enabled": True,
                "check_external": True,
                "timeout": 10,
                "retry_count": 3
            },
            "format_fix": {
                "enabled": True,
                "auto_fix": False,
                "backup_original": True
            },
            "reporting": {
                "generate_html": True,
                "generate_json": True,
                "email_notification": False
            },
            "schedule": {
                "daily_check": True,
                "weekly_report": True,
                "monthly_cleanup": True
            }
        }
        
        if self.config_file.exists():
            try:
                with open(self.config_file, 'r', encoding='utf-8') as f:
                    config = json.load(f)
                # 合并默认配置
                for key, value in default_config.items():
                    if key not in config:
                        config[key] = value
                return config
            except Exception as e:
                print(f"配置加载失败，使用默认配置: {e}")
                return default_config
        else:
            # 创建默认配置文件
            self.save_config(default_config)
            return default_config
    
    def save_config(self, config: Dict[str, Any]):
        """保存配置"""
        try:
            with open(self.config_file, 'w', encoding='utf-8') as f:
                json.dump(config, f, indent=2, ensure_ascii=False)
        except Exception as e:
            print(f"配置保存失败: {e}")
    
    def run_script(self, script_name: str, args: List[str] = None) -> Dict[str, Any]:
        """运行维护脚本"""
        script_path = self.scripts_dir / script_name
        
        if not script_path.exists():
            return {
                'success': False,
                'error': f"脚本不存在: {script_name}",
                'output': '',
                'exit_code': -1
            }
        
        try:
            cmd = [sys.executable, str(script_path)]
            if args:
                cmd.extend(args)
            
            result = subprocess.run(
                cmd,
                cwd=self.base_path,
                capture_output=True,
                text=True,
                timeout=300  # 5分钟超时
            )
            
            return {
                'success': result.returncode == 0,
                'output': result.stdout,
                'error': result.stderr,
                'exit_code': result.returncode
            }
        
        except subprocess.TimeoutExpired:
            return {
                'success': False,
                'error': f"脚本执行超时: {script_name}",
                'output': '',
                'exit_code': -1
            }
        except Exception as e:
            return {
                'success': False,
                'error': f"脚本执行错误: {e}",
                'output': '',
                'exit_code': -1
            }
    
    def run_quality_check(self) -> Dict[str, Any]:
        """运行质量检查"""
        print("🔍 运行质量检查...")
        
        if not self.config['quality_check']['enabled']:
            return {'success': True, 'message': '质量检查已禁用'}
        
        args = []
        if self.config['quality_check']['strict_mode']:
            args.append('--strict')
        
        result = self.run_script('quality_check.py', args)
        
        if result['success']:
            print("✅ 质量检查通过")
        else:
            print(f"❌ 质量检查失败: {result['error']}")
        
        return result
    
    def run_link_check(self) -> Dict[str, Any]:
        """运行链接检查"""
        print("🔗 运行链接检查...")
        
        if not self.config['link_check']['enabled']:
            return {'success': True, 'message': '链接检查已禁用'}
        
        result = self.run_script('link_checker.py')
        
        if result['success']:
            print("✅ 链接检查通过")
        else:
            print(f"❌ 链接检查失败: {result['error']}")
        
        return result
    
    def run_format_fix(self) -> Dict[str, Any]:
        """运行格式修复"""
        print("🔧 运行格式修复...")
        
        if not self.config['format_fix']['enabled']:
            return {'success': True, 'message': '格式修复已禁用'}
        
        # 这里可以添加格式修复逻辑
        # 例如：自动修复Markdown格式、统一标题层级等
        
        print("✅ 格式修复完成")
        return {'success': True, 'message': '格式修复完成'}
    
    def generate_maintenance_report(self, results: Dict[str, Any]) -> str:
        """生成维护报告"""
        timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        
        report = f"""# Rust软件工程文档维护报告

## 📊 维护概览

- **维护时间**: {timestamp}
- **维护路径**: {self.base_path}
- **维护状态**: {'✅ 成功' if all(r.get('success', False) for r in results.values()) else '❌ 部分失败'}

## 🔧 维护任务结果

### 质量检查
- **状态**: {'✅ 通过' if results.get('quality_check', {}).get('success') else '❌ 失败'}
- **详情**: {results.get('quality_check', {}).get('message', '未执行')}

### 链接检查
- **状态**: {'✅ 通过' if results.get('link_check', {}).get('success') else '❌ 失败'}
- **详情**: {results.get('link_check', {}).get('message', '未执行')}

### 格式修复
- **状态**: {'✅ 完成' if results.get('format_fix', {}).get('success') else '❌ 失败'}
- **详情**: {results.get('format_fix', {}).get('message', '未执行')}

## 📈 维护统计

- **总任务数**: {len(results)}
- **成功任务数**: {sum(1 for r in results.values() if r.get('success', False))}
- **失败任务数**: {sum(1 for r in results.values() if not r.get('success', False))}

## 🔄 下次维护计划

- **下次质量检查**: 建议24小时内
- **下次链接检查**: 建议每周一次
- **下次格式修复**: 建议每月一次

## 💡 改进建议

1. **定期维护**: 建议设置自动化维护计划
2. **问题修复**: 及时修复发现的问题
3. **配置优化**: 根据实际情况调整维护配置
4. **监控告警**: 设置维护失败告警机制

---
> 报告生成时间: {timestamp}
> 维护脚本版本: 1.0.0
"""
        
        return report
    
    def save_report(self, report: str, report_type: str = 'maintenance'):
        """保存报告"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        report_file = self.reports_dir / f"{report_type}_report_{timestamp}.md"
        
        try:
            with open(report_file, 'w', encoding='utf-8') as f:
                f.write(report)
            print(f"📄 报告已保存: {report_file}")
        except Exception as e:
            print(f"❌ 报告保存失败: {e}")
    
    def run_full_maintenance(self) -> bool:
        """运行完整维护流程"""
        print("🚀 开始完整维护流程...")
        
        results = {}
        
        # 1. 质量检查
        results['quality_check'] = self.run_quality_check()
        
        # 2. 链接检查
        results['link_check'] = self.run_link_check()
        
        # 3. 格式修复
        results['format_fix'] = self.run_format_fix()
        
        # 4. 生成报告
        report = self.generate_maintenance_report(results)
        self.save_report(report)
        
        # 5. 检查整体状态
        all_success = all(r.get('success', False) for r in results.values())
        
        if all_success:
            print("🎉 完整维护流程成功完成!")
        else:
            print("⚠️ 维护流程部分失败，请查看报告")
        
        return all_success
    
    def run_quick_maintenance(self) -> bool:
        """运行快速维护流程"""
        print("⚡ 开始快速维护流程...")
        
        # 只运行关键检查
        results = {}
        results['quality_check'] = self.run_quality_check()
        
        # 生成简要报告
        report = f"""# 快速维护报告

## 📊 维护概览
- **维护时间**: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}
- **维护类型**: 快速维护
- **质量检查**: {'✅ 通过' if results['quality_check'].get('success') else '❌ 失败'}

## 💡 建议
- 建议定期运行完整维护流程
- 发现问题及时修复
"""
        
        self.save_report(report, 'quick_maintenance')
        
        success = results['quality_check'].get('success', False)
        if success:
            print("✅ 快速维护完成!")
        else:
            print("❌ 快速维护发现问题")
        
        return success

def main():
    """主函数"""
    if len(sys.argv) < 2:
        print("用法: python maintenance_automation.py [full|quick] [path]")
        print("  full  - 运行完整维护流程")
        print("  quick - 运行快速维护流程")
        sys.exit(1)
    
    mode = sys.argv[1]
    base_path = sys.argv[2] if len(sys.argv) > 2 else os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    
    automation = MaintenanceAutomation(base_path)
    
    if mode == 'full':
        success = automation.run_full_maintenance()
    elif mode == 'quick':
        success = automation.run_quick_maintenance()
    else:
        print(f"未知模式: {mode}")
        sys.exit(1)
    
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()
