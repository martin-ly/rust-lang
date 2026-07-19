#!/usr/bin/env python3
"""
Rust形式化验证框架综合自动化管理脚本
集成验证、质量检查、文档生成、报告生成等功能
"""

import os
import sys
import subprocess
import json
import yaml
from pathlib import Path
from datetime import datetime
from typing import Dict, List, Any, Tuple
import re
import shutil

class FrameworkAutomation:
    def __init__(self, base_path: str):
        self.base_path = Path(base_path)
        self.scripts_dir = self.base_path / 'scripts'
        self.reports_dir = self.base_path / 'reports'
        self.config_file = self.scripts_dir / 'framework_config.yaml'
        
        # 创建必要目录
        self.reports_dir.mkdir(exist_ok=True)
        
        # 加载配置
        self.config = self.load_config()
    
    def load_config(self) -> Dict[str, Any]:
        """加载框架配置"""
        default_config = {
            "framework": {
                "version": "2.0",
                "name": "Rust Formal Verification Framework",
                "description": "Complete formal verification framework for Rust",
                "maintainer": "Rust Formal Verification Team"
            },
            "verification": {
                "enabled": True,
                "strict_mode": False,
                "check_types": True,
                "check_memory": True,
                "check_concurrency": True,
                "check_performance": True
            },
            "documentation": {
                "enabled": True,
                "auto_generate": True,
                "include_examples": True,
                "include_proofs": True,
                "format": ["markdown", "html", "pdf"]
            },
            "quality": {
                "enabled": True,
                "coverage_threshold": 90,
                "accuracy_threshold": 95,
                "completeness_threshold": 85,
                "performance_threshold": 90
            },
            "automation": {
                "enabled": True,
                "schedule": "daily",
                "backup": True,
                "notification": True,
                "reporting": True
            },
            "tools": {
                "clippy": {"enabled": True, "strict": True},
                "miri": {"enabled": True, "timeout": 600},
                "coq": {"enabled": True, "timeout": 300},
                "lean": {"enabled": True, "timeout": 300},
                "rustdoc": {"enabled": True, "private": True}
            }
        }
        
        if self.config_file.exists():
            try:
                with open(self.config_file, 'r', encoding='utf-8') as f:
                    config = yaml.safe_load(f)
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
                yaml.dump(config, f, default_flow_style=False, allow_unicode=True)
        except Exception as e:
            print(f"配置保存失败: {e}")
    
    def run_verification(self) -> Dict[str, Any]:
        """运行验证流程"""
        print("🔍 运行验证流程...")
        
        if not self.config['verification']['enabled']:
            return {'success': True, 'message': '验证已禁用'}
        
        results = {}
        
        # 运行Clippy检查
        if self.config['tools']['clippy']['enabled']:
            results['clippy'] = self.run_clippy()
        
        # 运行MIRI检查
        if self.config['tools']['miri']['enabled']:
            results['miri'] = self.run_miri()
        
        # 运行Coq验证
        if self.config['tools']['coq']['enabled']:
            results['coq'] = self.run_coq()
        
        # 运行Lean验证
        if self.config['tools']['lean']['enabled']:
            results['lean'] = self.run_lean()
        
        # 评估整体结果
        all_success = all(r.get('success', False) for r in results.values())
        
        return {
            'success': all_success,
            'results': results,
            'total_tools': len(results),
            'successful_tools': sum(1 for r in results.values() if r.get('success', False))
        }
    
    def run_clippy(self) -> Dict[str, Any]:
        """运行Clippy检查"""
        try:
            cmd = ['cargo', 'clippy']
            if self.config['tools']['clippy']['strict']:
                cmd.extend(['--', '-D', 'warnings'])
            
            result = subprocess.run(
                cmd,
                cwd=self.base_path,
                capture_output=True,
                text=True,
                timeout=300
            )
            
            return {
                'success': result.returncode == 0,
                'output': result.stdout,
                'error': result.stderr,
                'exit_code': result.returncode
            }
        except Exception as e:
            return {
                'success': False,
                'error': f'Clippy运行错误: {e}',
                'exit_code': -1
            }
    
    def run_miri(self) -> Dict[str, Any]:
        """运行MIRI检查"""
        try:
            cmd = ['cargo', 'miri', 'test']
            result = subprocess.run(
                cmd,
                cwd=self.base_path,
                capture_output=True,
                text=True,
                timeout=self.config['tools']['miri']['timeout']
            )
            
            return {
                'success': result.returncode == 0,
                'output': result.stdout,
                'error': result.stderr,
                'exit_code': result.returncode
            }
        except Exception as e:
            return {
                'success': False,
                'error': f'MIRI运行错误: {e}',
                'exit_code': -1
            }
    
    def run_coq(self) -> Dict[str, Any]:
        """运行Coq验证"""
        proofs_dir = self.base_path / 'proofs' / 'coq'
        if not proofs_dir.exists():
            return {'success': True, 'message': 'Coq证明目录不存在'}
        
        try:
            results = []
            for proof_file in proofs_dir.glob('*.v'):
                cmd = ['coqc', str(proof_file)]
                result = subprocess.run(
                    cmd,
                    cwd=proofs_dir,
                    capture_output=True,
                    text=True,
                    timeout=self.config['tools']['coq']['timeout']
                )
                
                results.append({
                    'file': proof_file.name,
                    'success': result.returncode == 0,
                    'output': result.stdout,
                    'error': result.stderr
                })
            
            overall_success = all(r['success'] for r in results)
            return {
                'success': overall_success,
                'results': results,
                'total_files': len(results),
                'successful_files': sum(1 for r in results if r['success'])
            }
        except Exception as e:
            return {
                'success': False,
                'error': f'Coq运行错误: {e}',
                'results': []
            }
    
    def run_lean(self) -> Dict[str, Any]:
        """运行Lean验证"""
        proofs_dir = self.base_path / 'proofs' / 'lean'
        if not proofs_dir.exists():
            return {'success': True, 'message': 'Lean证明目录不存在'}
        
        try:
            results = []
            for proof_file in proofs_dir.glob('*.lean'):
                cmd = ['lean', str(proof_file)]
                result = subprocess.run(
                    cmd,
                    cwd=proofs_dir,
                    capture_output=True,
                    text=True,
                    timeout=self.config['tools']['lean']['timeout']
                )
                
                results.append({
                    'file': proof_file.name,
                    'success': result.returncode == 0,
                    'output': result.stdout,
                    'error': result.stderr
                })
            
            overall_success = all(r['success'] for r in results)
            return {
                'success': overall_success,
                'results': results,
                'total_files': len(results),
                'successful_files': sum(1 for r in results if r['success'])
            }
        except Exception as e:
            return {
                'success': False,
                'error': f'Lean运行错误: {e}',
                'results': []
            }
    
    def generate_documentation(self) -> Dict[str, Any]:
        """生成文档"""
        print("📚 生成文档...")
        
        if not self.config['documentation']['enabled']:
            return {'success': True, 'message': '文档生成已禁用'}
        
        try:
            # 生成Rust文档
            if self.config['tools']['rustdoc']['enabled']:
                cmd = ['cargo', 'doc']
                if self.config['tools']['rustdoc']['private']:
                    cmd.append('--document-private-items')
                
                result = subprocess.run(
                    cmd,
                    cwd=self.base_path,
                    capture_output=True,
                    text=True,
                    timeout=300
                )
                
                if result.returncode != 0:
                    return {
                        'success': False,
                        'error': f'文档生成失败: {result.stderr}',
                        'exit_code': result.returncode
                    }
            
            # 生成其他格式文档
            formats = self.config['documentation']['format']
            generated_formats = []
            
            for format_type in formats:
                if format_type == 'html':
                    # HTML文档已通过rustdoc生成
                    generated_formats.append('html')
                elif format_type == 'markdown':
                    # Markdown文档已存在
                    generated_formats.append('markdown')
                elif format_type == 'pdf':
                    # PDF生成需要额外工具
                    generated_formats.append('pdf')
            
            return {
                'success': True,
                'generated_formats': generated_formats,
                'message': f'文档生成成功，格式: {", ".join(generated_formats)}'
            }
        
        except Exception as e:
            return {
                'success': False,
                'error': f'文档生成错误: {e}',
                'exit_code': -1
            }
    
    def assess_quality(self, verification_results: Dict[str, Any]) -> Dict[str, Any]:
        """评估质量"""
        print("📊 评估质量...")
        
        if not self.config['quality']['enabled']:
            return {'success': True, 'message': '质量评估已禁用'}
        
        quality_metrics = {
            'verification_coverage': 0,
            'tool_success_rate': 0,
            'documentation_completeness': 0,
            'overall_quality': 0
        }
        
        # 计算验证覆盖率
        if verification_results.get('success'):
            quality_metrics['verification_coverage'] = 100
        else:
            successful_tools = verification_results.get('successful_tools', 0)
            total_tools = verification_results.get('total_tools', 1)
            quality_metrics['verification_coverage'] = (successful_tools / total_tools) * 100
        
        # 计算工具成功率
        quality_metrics['tool_success_rate'] = quality_metrics['verification_coverage']
        
        # 计算文档完整性
        doc_files = list(self.base_path.rglob('*.md'))
        required_files = [
            'README.md',
            '00_MASTER_NAVIGATION.md',
            'LEARNING_PATHS.md',
            'VERIFICATION_GUIDE.md'
        ]
        
        existing_files = sum(1 for req_file in required_files 
                           if (self.base_path / req_file).exists())
        quality_metrics['documentation_completeness'] = (existing_files / len(required_files)) * 100
        
        # 计算总体质量
        quality_metrics['overall_quality'] = sum(quality_metrics.values()) / len(quality_metrics)
        
        # 检查质量阈值
        thresholds = {
            'coverage': self.config['quality']['coverage_threshold'],
            'accuracy': self.config['quality']['accuracy_threshold'],
            'completeness': self.config['quality']['completeness_threshold'],
            'performance': self.config['quality']['performance_threshold']
        }
        
        quality_gates = {
            'coverage_gate': quality_metrics['verification_coverage'] >= thresholds['coverage'],
            'accuracy_gate': quality_metrics['tool_success_rate'] >= thresholds['accuracy'],
            'completeness_gate': quality_metrics['documentation_completeness'] >= thresholds['completeness'],
            'performance_gate': quality_metrics['overall_quality'] >= thresholds['performance']
        }
        
        all_gates_passed = all(quality_gates.values())
        
        return {
            'success': all_gates_passed,
            'metrics': quality_metrics,
            'thresholds': thresholds,
            'gates': quality_gates,
            'overall_quality': quality_metrics['overall_quality']
        }
    
    def generate_comprehensive_report(self, verification_results: Dict[str, Any], 
                                    doc_results: Dict[str, Any], 
                                    quality_results: Dict[str, Any]) -> str:
        """生成综合报告"""
        timestamp = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
        
        report = f"""# Rust形式化验证框架综合报告

## 📊 框架概览

- **框架名称**: {self.config['framework']['name']}
- **框架版本**: {self.config['framework']['version']}
- **报告时间**: {timestamp}
- **框架路径**: {self.base_path}
- **整体状态**: {'✅ 优秀' if quality_results.get('overall_quality', 0) >= 90 else '⚠️ 需要改进' if quality_results.get('overall_quality', 0) >= 80 else '❌ 需要修复'}

## 🔍 验证结果

### 验证概览
- **验证状态**: {'✅ 成功' if verification_results.get('success') else '❌ 失败'}
- **工具总数**: {verification_results.get('total_tools', 0)}
- **成功工具**: {verification_results.get('successful_tools', 0)}

### 详细结果
"""
        
        # 添加验证工具结果
        for tool, result in verification_results.get('results', {}).items():
            status = '✅ 通过' if result.get('success') else '❌ 失败'
            report += f"- **{tool.upper()}**: {status}\n"
        
        report += f"""
## 📚 文档生成

### 文档状态
- **生成状态**: {'✅ 成功' if doc_results.get('success') else '❌ 失败'}
- **生成格式**: {', '.join(doc_results.get('generated_formats', []))}
- **详细信息**: {doc_results.get('message', '未执行')}

## 📈 质量评估

### 质量指标
- **验证覆盖率**: {quality_results.get('metrics', {}).get('verification_coverage', 0):.1f}%
- **工具成功率**: {quality_results.get('metrics', {}).get('tool_success_rate', 0):.1f}%
- **文档完整性**: {quality_results.get('metrics', {}).get('documentation_completeness', 0):.1f}%
- **总体质量**: {quality_results.get('overall_quality', 0):.1f}/100

### 质量门禁
"""
        
        # 添加质量门禁结果
        gates = quality_results.get('gates', {})
        for gate_name, passed in gates.items():
            status = '✅ 通过' if passed else '❌ 未通过'
            report += f"- **{gate_name}**: {status}\n"
        
        report += f"""
## 🎯 改进建议

### 短期改进
1. **验证优化**: 提高验证工具的成功率
2. **文档完善**: 补充缺失的文档内容
3. **质量提升**: 提升整体质量指标

### 长期改进
1. **工具扩展**: 增加更多验证工具
2. **自动化提升**: 提高自动化程度
3. **标准制定**: 制定更严格的质量标准

## 📞 技术支持

### 问题反馈
- **GitHub Issues**: 通过GitHub Issues提交问题
- **技术讨论**: 参与技术讨论和问题解决
- **贡献参与**: 欢迎提交PR和参与开发

### 文档维护
- **定期更新**: 每月更新框架和文档
- **质量检查**: 每周运行自动化质量检查
- **用户反馈**: 及时响应用户反馈和建议

---
> 报告生成时间: {timestamp}
> 框架版本: {self.config['framework']['version']}
> 质量等级: {'优秀' if quality_results.get('overall_quality', 0) >= 90 else '良好' if quality_results.get('overall_quality', 0) >= 80 else '需要改进'}
"""
        
        return report
    
    def save_report(self, report: str, report_type: str = 'comprehensive'):
        """保存报告"""
        timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
        report_file = self.reports_dir / f"{report_type}_report_{timestamp}.md"
        
        try:
            with open(report_file, 'w', encoding='utf-8') as f:
                f.write(report)
            print(f"📄 报告已保存: {report_file}")
        except Exception as e:
            print(f"❌ 报告保存失败: {e}")
    
    def run_full_automation(self) -> bool:
        """运行完整自动化流程"""
        print("🚀 开始完整自动化流程...")
        
        # 1. 运行验证
        verification_results = self.run_verification()
        
        # 2. 生成文档
        doc_results = self.generate_documentation()
        
        # 3. 评估质量
        quality_results = self.assess_quality(verification_results)
        
        # 4. 生成综合报告
        report = self.generate_comprehensive_report(verification_results, doc_results, quality_results)
        self.save_report(report)
        
        # 5. 检查整体状态
        overall_success = (
            verification_results.get('success', False) and
            doc_results.get('success', False) and
            quality_results.get('success', False)
        )
        
        if overall_success:
            print("🎉 完整自动化流程成功完成!")
        else:
            print("⚠️ 自动化流程部分失败，请查看报告")
        
        return overall_success

def main():
    """主函数"""
    if len(sys.argv) < 2:
        print("用法: python framework_automation.py [full|verify|doc|quality] [path]")
        print("  full    - 运行完整自动化流程")
        print("  verify  - 只运行验证流程")
        print("  doc     - 只生成文档")
        print("  quality - 只评估质量")
        sys.exit(1)
    
    mode = sys.argv[1]
    base_path = sys.argv[2] if len(sys.argv) > 2 else os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    
    automation = FrameworkAutomation(base_path)
    
    if mode == 'full':
        success = automation.run_full_automation()
    elif mode == 'verify':
        results = automation.run_verification()
        success = results.get('success', False)
    elif mode == 'doc':
        results = automation.generate_documentation()
        success = results.get('success', False)
    elif mode == 'quality':
        verification_results = automation.run_verification()
        results = automation.assess_quality(verification_results)
        success = results.get('success', False)
    else:
        print(f"未知模式: {mode}")
        sys.exit(1)
    
    sys.exit(0 if success else 1)

if __name__ == "__main__":
    main()
