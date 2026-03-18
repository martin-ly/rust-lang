#!/usr/bin/env python3
"""
Rust 版本跟踪器

自动跟踪 Rust 最新版本特性，生成更新报告。

用法:
    python scripts/rust_version_tracker.py [--check]

选项:
    --check    检查是否有新版本可用
"""

import argparse
import json
import subprocess
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional
import urllib.request
import urllib.error

# 项目根目录
PROJECT_ROOT = Path(__file__).parent.parent

# Rust 版本 API
RUST_RELEASES_URL = "https://releases.rs/api/v1/stable"
RUST_BLOG_URL = "https://blog.rust-lang.org/releases.json"


class RustVersionTracker:
    """Rust 版本跟踪器"""
    
    def __init__(self):
        self.current_version = self._get_current_version()
        self.latest_version = None
        
    def _get_current_version(self) -> str:
        """获取项目当前使用的 Rust 版本"""
        try:
            # 尝试从 Cargo.toml 读取
            cargo_toml = PROJECT_ROOT / "Cargo.toml"
            if cargo_toml.exists():
                content = cargo_toml.read_text()
                for line in content.split('\n'):
                    if 'rust-version' in line:
                        return line.split('=')[1].strip().strip('"')
        except Exception as e:
            print(f"警告: 无法读取当前版本: {e}")
        
        return "1.94.0"  # 默认值
    
    def fetch_latest_version(self) -> Optional[str]:
        """获取最新的 Rust 稳定版本"""
        try:
            # 使用 rustup 获取最新版本
            result = subprocess.run(
                ["rustup", "check"],
                capture_output=True,
                text=True,
                timeout=30
            )
            
            # 尝试从 releases.rs 获取
            try:
                with urllib.request.urlopen(RUST_RELEASES_URL, timeout=10) as response:
                    data = json.loads(response.read().decode())
                    return data.get('version', '1.94.0')
            except:
                pass
            
            # 尝试从 rustc 获取
            result = subprocess.run(
                ["rustc", "--version"],
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode == 0:
                version = result.stdout.strip().split()[1]
                return version
                
        except Exception as e:
            print(f"错误: 无法获取最新版本: {e}")
        
        return None
    
    def check_for_updates(self) -> bool:
        """检查是否有新版本可用"""
        self.latest_version = self.fetch_latest_version()
        
        if not self.latest_version:
            print("无法获取最新版本信息")
            return False
        
        current = tuple(map(int, self.current_version.split('.')))
        latest = tuple(map(int, self.latest_version.split('.')))
        
        if latest > current:
            print(f"🎉 发现新版本!")
            print(f"   当前版本: {self.current_version}")
            print(f"   最新版本: {self.latest_version}")
            return True
        else:
            print(f"✅ 已是最新版本 ({self.current_version})")
            return False
    
    def generate_report(self) -> str:
        """生成版本跟踪报告"""
        report = []
        report.append("# Rust 版本跟踪报告\n")
        report.append(f"**生成时间**: {datetime.now().isoformat()}\n")
        report.append(f"**当前项目版本**: {self.current_version}\n")
        report.append(f"**最新稳定版本**: {self.latest_version or '未知'}\n")
        
        if self.latest_version and self.latest_version != self.current_version:
            report.append(f"\n## ⚠️ 需要更新\n")
            report.append(f"从 {self.current_version} 升级到 {self.latest_version}\n")
            report.append(f"\n### 更新步骤\n")
            report.append(f"1. 更新 `Cargo.toml` 中的 `rust-version`\n")
            report.append(f"2. 运行 `cargo update`\n")
            report.append(f"3. 运行 `cargo test` 验证兼容性\n")
            report.append(f"4. 更新文档中的版本引用\n")
        
        report.append(f"\n## 特性跟踪\n")
        report.append(f"\n### 待跟踪特性\n")
        report.append(f"- [ ] Rust 1.95: Impl Trait in Associated Type\n")
        report.append(f"- [ ] Rust 1.96: Generic Const Expressions\n")
        report.append(f"- [ ] Rust 1.97: TAIT (Type Alias Impl Trait)\n")
        
        return ''.join(report)
    
    def save_report(self, report: str):
        """保存报告到文件"""
        report_dir = PROJECT_ROOT / "reports"
        report_dir.mkdir(exist_ok=True)
        
        timestamp = datetime.now().strftime("%Y%m%d")
        report_file = report_dir / f"version_tracking_{timestamp}.md"
        
        report_file.write_text(report, encoding='utf-8')
        print(f"\n报告已保存到: {report_file}")


def check_rust_features():
    """检查项目中 Rust 特性的使用情况"""
    print("\n🔍 检查项目特性使用情况...")
    
    features_found = {
        "array_windows": 0,
        "LazyCell": 0,
        "LazyLock": 0,
        "ControlFlow": 0,
        "math_consts": 0,
    }
    
    src_dir = PROJECT_ROOT / "crates"
    for rs_file in src_dir.rglob("*.rs"):
        content = rs_file.read_text(encoding='utf-8')
        
        if "array_windows" in content:
            features_found["array_windows"] += 1
        if "LazyCell" in content:
            features_found["LazyCell"] += 1
        if "LazyLock" in content:
            features_found["LazyLock"] += 1
        if "ControlFlow" in content:
            features_found["ControlFlow"] += 1
        if "EULER_GAMMA" in content or "GOLDEN_RATIO" in content:
            features_found["math_consts"] += 1
    
    print("\n📊 特性使用统计:")
    for feature, count in features_found.items():
        status = "✅" if count > 0 else "❌"
        print(f"   {status} {feature}: {count} 处使用")
    
    return features_found


def main():
    parser = argparse.ArgumentParser(description="Rust 版本跟踪器")
    parser.add_argument("--check", action="store_true", help="检查更新")
    parser.add_argument("--report", action="store_true", help="生成报告")
    args = parser.parse_args()
    
    tracker = RustVersionTracker()
    
    print("=" * 60)
    print("🦀 Rust 版本跟踪器")
    print("=" * 60)
    print(f"\n当前项目版本: {tracker.current_version}")
    
    # 检查更新
    if args.check or args.report:
        has_update = tracker.check_for_updates()
        
        if args.report or has_update:
            report = tracker.generate_report()
            tracker.save_report(report)
            print("\n" + report)
    
    # 检查特性使用情况
    check_rust_features()
    
    print("\n" + "=" * 60)
    print("完成!")
    print("=" * 60)


if __name__ == "__main__":
    main()
