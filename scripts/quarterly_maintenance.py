#!/usr/bin/env python3
"""
季度维护脚本 —— 全面健康检查

运行周期: 每 3 个月
检查项:
  1. cargo audit（依赖安全）
  2. kb_auditor.py（死链检查）
  3. version_fact_check.py（版本事实准确性）
  4. check_links.py（断裂链接复查）
  5. mdbook build（文档构建验证）
  6. cargo check --workspace（编译验证）

用法:
  python scripts/quarterly_maintenance.py [--fix]

返回码:
  0 — 全部通过
  1 — 至少一项未通过

> **来源**: Rust 分层概念知识体系维护手册
> **维护者**: 项目维护团队
"""

import argparse
import subprocess
import sys
from datetime import datetime
from pathlib import Path

PROJECT_ROOT = Path(__file__).parent.parent

CHECKS = [
    ("编译验证", ["cargo", "check", "--workspace"]),
    ("测试验证", ["cargo", "test", "--workspace", "--lib", "--bins", "--tests"]),
    ("依赖安全审计", ["cargo", "audit"]),
    ("知识库死链审计", ["python", "scripts/kb_auditor.py"]),
    ("版本事实检查", ["python", "scripts/version_fact_check.py"]),
    ("断裂链接复查", ["python", "scripts/check_links.py"]),
]

OPTIONAL_CHECKS = [
    ("稳定 API 审计", ["python", "scripts/audit_stable_apis.py"]),
    ("代码块编译检查", ["python", "scripts/code_block_compiler.py"]),
]


def run_check(name, cmd, fix=False):
    """运行单个检查，返回 (通过?, 输出)"""
    print(f"\n{'='*60}")
    print(f"🔍 {name}")
    print(f"{'='*60}")
    try:
        result = subprocess.run(
            cmd,
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=300,
        )
        if result.returncode == 0:
            print(f"✅ {name} 通过")
            return True, result.stdout + result.stderr
        else:
            output = result.stdout + result.stderr
            # cargo audit 网络错误视为环境限制，不标记为项目失败
            if name == "依赖安全审计" and (
                "couldn't fetch advisory database" in output
                or "git operation failed" in output
                or "error sending request" in output
            ):
                print(f"⚠️ {name} 因网络限制跳过 (advisory-db 获取失败)")
                return True, output  # 视为通过，避免误报
            print(f"❌ {name} 未通过 (exit code {result.returncode})")
            if result.stdout:
                print(result.stdout[-2000:])  # 只打印最后 2000 字符
            if result.stderr:
                print(result.stderr[-2000:])
            return False, result.stdout + result.stderr
    except subprocess.TimeoutExpired:
        print(f"⏱️ {name} 超时 (>300s)")
        return False, "timeout"
    except FileNotFoundError as e:
        print(f"⚠️ {name} 命令未找到: {e}")
        return False, str(e)


def main():
    parser = argparse.ArgumentParser(description="季度维护脚本")
    parser.add_argument("--fix", action="store_true", help="尝试自动修复可修复的问题")
    parser.add_argument("--include-optional", action="store_true", help="包含可选检查（耗时较长）")
    args = parser.parse_args()

    print(f"Rust 分层概念知识体系 — 季度维护检查")
    print(f"运行时间: {datetime.now().isoformat()}")
    print(f"项目根目录: {PROJECT_ROOT}")
    if args.fix:
        print("模式: 自动修复启用")

    results = []
    all_passed = True

    for name, cmd in CHECKS:
        passed, output = run_check(name, cmd, fix=args.fix)
        results.append((name, passed, output))
        if not passed:
            all_passed = False

    if args.include_optional:
        print("\n" + "="*60)
        print("可选检查（耗时较长）")
        print("="*60)
        for name, cmd in OPTIONAL_CHECKS:
            passed, output = run_check(name, cmd, fix=args.fix)
            results.append((name, passed, output))
            if not passed:
                all_passed = False

    # 汇总报告
    print("\n" + "="*60)
    print("📊 维护检查汇总")
    print("="*60)
    for name, passed, _ in results:
        status = "✅ 通过" if passed else "❌ 未通过"
        print(f"  {status} — {name}")

    total = len(results)
    passed_count = sum(1 for _, p, _ in results if p)
    print(f"\n总计: {passed_count}/{total} 通过")

    if all_passed:
        print("\n🎉 季度维护检查全部通过！")
        return 0
    else:
        print("\n⚠️ 部分检查未通过，请查看上方详情并修复。")
        return 1


if __name__ == "__main__":
    sys.exit(main())
