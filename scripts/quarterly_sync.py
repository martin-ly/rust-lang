#!/usr/bin/env python3
"""
归档迁移脚本：季度同步与 Rust 版本对齐检查清单生成器

读取 docs/00_meta/10_quarterly_sync_checklist.md 和
     docs/00_meta/13_rust_version_alignment_checklist.md 作为模板，
自动填充可客观获取的数据（日期、版本、编译状态、依赖状态、安全公告等），
生成填充后的检查清单到 archive/YYYY/QN/ 目录。

用法:
    python scripts/quarterly_sync.py
    python scripts/quarterly_sync.py --year 2026 --quarter 3 --executor "维护者"
    python scripts/quarterly_sync.py --skip-commands  # 仅生成空表头，不执行耗时命令

返回码:
    0 — 成功生成
    1 — 生成失败
"""

import argparse
import json
import re
import subprocess
import sys
import urllib.request
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Optional, Tuple

PROJECT_ROOT = Path(__file__).parent.parent
TEMPLATE_DIR = PROJECT_ROOT / "docs" / "00_meta"
OUTPUT_DIR = PROJECT_ROOT / "archive"

RUST_RELEASES_URL = "https://releases.rs/api/v1/stable"


def run_command(cmd: List[str], timeout: int = 120) -> Tuple[int, str, str]:
    """运行命令并返回 (returncode, stdout, stderr)"""
    try:
        result = subprocess.run(
            cmd,
            cwd=PROJECT_ROOT,
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        return result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired:
        return -1, "", f"timeout after {timeout}s"
    except FileNotFoundError as e:
        return -2, "", str(e)


def get_cargo_toml_field(field: str) -> Optional[str]:
    """从根 Cargo.toml 读取简单字段"""
    cargo_toml = PROJECT_ROOT / "Cargo.toml"
    if not cargo_toml.exists():
        return None
    content = cargo_toml.read_text(encoding="utf-8")
    # 匹配 [workspace.package] 下的字段（精确字段名，避免 version 匹配到 rust-version）
    match = re.search(
        rf"\[workspace\.package\][^\[]*\n{field}\s*=\s*\"([^\"]+)\"",
        content,
        re.DOTALL,
    )
    if match:
        return match.group(1)
    # 简单全局匹配
    match = re.search(rf"^{field}\s*=\s*\"([^\"]+)\"", content, re.MULTILINE)
    if match:
        return match.group(1)
    return None


def get_rust_latest_version() -> str:
    """获取最新 Rust 稳定版本"""
    # 优先解析 rustup check 输出
    # rustup check 在存在可用更新时返回码 100，但 stdout 仍包含版本信息
    rc, stdout, _ = run_command(["rustup", "check"], timeout=30)
    for line in stdout.splitlines():
        if line.startswith("stable") and "up to date:" in line:
            # 格式: stable-x86_64-pc-windows-msvc - up to date: 1.96.0 (hash YYYY-MM-DD)
            match = re.search(r"up to date:\s+([\d]+\.[\d]+\.[\d]+)", line)
            if match:
                return match.group(1)

    # 次选：尝试 releases.rs API
    try:
        with urllib.request.urlopen(RUST_RELEASES_URL, timeout=10) as response:
            data = json.loads(response.read().decode())
            version = data.get("version")
            if version:
                return version
    except Exception:
        pass

    return "未知"


def get_rustc_version() -> str:
    """获取当前 rustc 版本"""
    rc, stdout, _ = run_command(["rustc", "--version"], timeout=10)
    if rc == 0:
        return stdout.strip()
    return "未知"


def get_workspace_members() -> List[str]:
    """获取 workspace members 列表"""
    rc, stdout, _ = run_command(["cargo", "metadata", "--no-deps", "--format-version", "1"], timeout=30)
    if rc != 0:
        return []
    try:
        data = json.loads(stdout)
        return [pkg["name"] for pkg in data.get("packages", [])]
    except json.JSONDecodeError:
        return []


def check_workspace_compile() -> Tuple[bool, List[Tuple[str, bool, str]]]:
    """检查 workspace 编译状态，返回 (整体通过?, [(crate, 通过?, 输出), ...])"""
    members = get_workspace_members()
    if not members:
        # 如果 metadata 失败，直接整体编译
        rc, stdout, stderr = run_command(["cargo", "check", "--workspace", "--all-targets"], timeout=300)
        return rc == 0, [("workspace", rc == 0, (stdout + stderr)[-500:])]

    results = []
    all_passed = True
    for member in members:
        rc, stdout, stderr = run_command(
            ["cargo", "check", "--package", member, "--all-targets"],
            timeout=120,
        )
        passed = rc == 0
        results.append((member, passed, (stdout + stderr)[-300:] if not passed else ""))
        if not passed:
            all_passed = False
    return all_passed, results


def cargo_audit_summary() -> Tuple[int, List[Dict], str]:
    """运行 cargo audit --json，返回 (漏洞数, 详情列表, 原始输出)"""
    rc, stdout, stderr = run_command(["cargo", "audit", "--json"], timeout=60)
    if rc != 0 and not stdout:
        # 可能是网络问题或 cargo-audit 未安装
        return -1, [], stderr or stdout
    try:
        data = json.loads(stdout)
        vulnerabilities = data.get("vulnerabilities", {}).get("list", [])
        return len(vulnerabilities), vulnerabilities, stdout
    except json.JSONDecodeError:
        return -1, [], stdout


def cargo_outdated_summary() -> List[Dict]:
    """运行 cargo outdated -R --format json，返回根依赖更新列表"""
    rc, stdout, _ = run_command(["cargo", "outdated", "-R", "--format", "json"], timeout=60)
    if rc != 0:
        return []
    try:
        data = json.loads(stdout)
        return data if isinstance(data, list) else data.get("dependencies", [])
    except json.JSONDecodeError:
        return []


def count_todos() -> int:
    """统计 TODO/FIXME/XXX 数量"""
    patterns = ["TODO", "FIXME", "XXX"]
    dirs = ["crates", "examples", "docs", "concept", "knowledge"]
    total = 0
    for d in dirs:
        path = PROJECT_ROOT / d
        if not path.exists():
            continue
        for pattern in patterns:
            rc, stdout, _ = run_command(
                ["grep", "-R", "-E", f"(^|[ \t]){pattern}([ \t]|$)", str(path)],
                timeout=30,
            )
            if rc == 0:
                total += len(stdout.strip().split("\n"))
    return total


def count_open_issues_prs() -> Tuple[int, int]:
    """使用 gh CLI 统计开放 Issues/PRs"""
    issues = 0
    prs = 0
    rc, stdout, _ = run_command(["gh", "issue", "list", "--state", "open", "--json", "number", "--limit", "1000"], timeout=30)
    if rc == 0:
        try:
            issues = len(json.loads(stdout))
        except json.JSONDecodeError:
            pass
    rc, stdout, _ = run_command(["gh", "pr", "list", "--state", "open", "--json", "number", "--limit", "1000"], timeout=30)
    if rc == 0:
        try:
            prs = len(json.loads(stdout))
        except json.JSONDecodeError:
            pass
    return issues, prs


def generate_quarterly_checklist(
    year: int,
    quarter: int,
    executor: str,
    skip_commands: bool,
) -> str:
    """生成本季度同步检查清单"""
    template = TEMPLATE_DIR / "00_quarterly_sync_checklist.md"
    content = template.read_text(encoding="utf-8") if template.exists() else ""

    now = datetime.now()
    date_str = now.strftime("%Y-%m-%d")

    # 填充表头
    content = re.sub(
        r"> \*\*本季度:\*\* .+?\n",
        f"> **本季度:** {year} 年 第 {quarter} 季度\n",
        content,
    )
    content = re.sub(
        r"> \*\*执行人:\*\* .+?\n",
        f"> **执行人:** {executor or '________________'}\n",
        content,
    )
    content = re.sub(
        r"> \*\*执行日期:\*\* .+?\n",
        f"> **执行日期:** {date_str}\n",
        content,
    )

    if skip_commands:
        return content

    # 获取数据
    rustc_ver = get_rustc_version()
    latest_ver = get_rust_latest_version()
    msrv = get_cargo_toml_field("rust-version") or "未知"
    edition = get_cargo_toml_field("edition") or "未知"
    workspace_version = get_cargo_toml_field("version") or "未知"

    # 依赖状态
    outdated = cargo_outdated_summary()

    # 安全审计
    vuln_count, vulnerabilities, _ = cargo_audit_summary()

    # 编译状态
    compile_ok, compile_results = check_workspace_compile()

    # 其他指标
    todo_count = count_todos()
    try:
        issues, prs = count_open_issues_prs()
    except Exception:
        issues, prs = 0, 0

    # 构建摘要块
    summary = f"""
<!-- 以下由 scripts/quarterly_sync.py 于 {date_str} 自动生成 -->

### 自动采集摘要

| 指标 | 值 |
|:---|:---|
| 当前 rustc | {rustc_ver} |
| 最新稳定版 | {latest_ver} |
| 项目 MSRV | {msrv} |
| 项目 Edition | {edition} |
| Workspace 版本 | {workspace_version} |
| 编译状态 | {'✅ 通过' if compile_ok else '❌ 存在失败'} |
| 安全漏洞 | {'✅ 0 个' if vuln_count == 0 else f'❌ {vuln_count} 个'} |
| 过期根依赖 | {len(outdated)} 个 |
| TODO/FIXME/XXX | {todo_count} 个 |
| 开放 Issues | {issues} 个 |
| 开放 PRs | {prs} 个 |

"""

    # 编译状态表
    compile_table = "### Crate 编译状态\n\n| Crate | 状态 | 备注 |\n|:---|:---:|:---|\n"
    for crate, passed, output in compile_results:
        status = "✅ 通过" if passed else "❌ 失败"
        note = output[:100].replace("\n", " ") if output else ""
        compile_table += f"| {crate} | {status} | {note} |\n"
    compile_table += "\n"

    # 依赖状态表
    dep_table = "### 根依赖更新状态\n\n| Crate | 当前版本 | 最新版本 | 更新类型 | 决策 |\n|:---|:---|:---|:---:|:---|\n"
    if outdated:
        for dep in outdated:
            name = dep.get("name", "?")
            current = dep.get("version", "?")
            latest = dep.get("latest", "?")
            update_type = "major" if latest.split('.')[0] != current.split('.')[0] else "minor/patch"
            dep_table += f"| {name} | {current} | {latest} | {update_type} | 待评估 |\n"
    else:
        dep_table += "| - | - | - | - | 所有根依赖均为最新或 cargo-outdated 未安装 |\n"
    dep_table += "\n"

    # 安全公告表
    vuln_table = "### 安全公告\n\n| RUSTSEC | 严重程度 | 受影响 Crate | 修复版本 | 状态 |\n|:---|:---|:---|:---|:---|\n"
    if vuln_count > 0:
        for vuln in vulnerabilities:
            adv = vuln.get("advisory", {})
            vuln_table += (
                f"| {adv.get('id', '?')} | {adv.get('severity', '?')} | "
                f"{', '.join(p.get('name', '?') for p in vuln.get('packages', []))} | "
                f"{adv.get('patched_versions', ['?'])[0] if adv.get('patched_versions') else '?'} | 待处理 |\n"
            )
    elif vuln_count == 0:
        vuln_table += "| - | - | - | - | ✅ 无已知安全漏洞 |\n"
    else:
        vuln_table += "| - | - | - | - | ⚠️ cargo audit 运行失败或未安装 |\n"
    vuln_table += "\n"

    # 在文档开头插入摘要（在第一个主章节之前）
    insert_marker = "## 1️⃣ Rust 官方生态更新"
    if insert_marker in content:
        content = content.replace(insert_marker, summary + compile_table + dep_table + vuln_table + "\n---\n\n" + insert_marker)
    else:
        content += "\n" + summary + compile_table + dep_table + vuln_table

    return content


def generate_rust_version_checklist(
    year: int,
    quarter: int,
    executor: str,
    skip_commands: bool,
) -> str:
    """生成 Rust 版本对齐检查清单"""
    template = TEMPLATE_DIR / "00_rust_version_alignment_checklist.md"
    content = template.read_text(encoding="utf-8") if template.exists() else ""

    now = datetime.now()
    date_str = now.strftime("%Y-%m-%d")
    month = now.month

    content = re.sub(
        r"> \*\*本次检查周期:\*\* .+?\n",
        f"> **本次检查周期:** {year} 年 {month} 月\n",
        content,
    )
    content = re.sub(
        r"> \*\*执行人:\*\* .+?\n",
        f"> **执行人:** {executor or '________________'}\n",
        content,
    )

    if skip_commands:
        # 即使跳过命令，也填充静态字段
        msrv = get_cargo_toml_field("rust-version") or "未知"
        content = re.sub(
            r"> \*\*Rust 最新稳定版:\*\* .+?\n",
            f"> **Rust 最新稳定版:** 未知（--skip-commands 模式）\n",
            content,
        )
        content = re.sub(
            r"> \*\*项目当前 MSRV:\*\* .+?\n",
            f"> **项目当前 MSRV:** {msrv}\n",
            content,
        )
        return content

    latest_ver = get_rust_latest_version()
    rustc_ver = get_rustc_version()
    msrv = get_cargo_toml_field("rust-version") or "未知"
    edition = get_cargo_toml_field("edition") or "未知"

    content = re.sub(
        r"> \*\*Rust 最新稳定版:\*\* .+?\n",
        f"> **Rust 最新稳定版:** {latest_ver}\n",
        content,
    )
    content = re.sub(
        r"> \*\*项目当前 MSRV:\*\* .+?\n",
        f"> **项目当前 MSRV:** {msrv}\n",
        content,
    )

    # Beta / Nightly 版本
    beta_ver = "未知"
    nightly_ver = "未知"
    rc, stdout, _ = run_command(["rustc", "+beta", "--version"], timeout=10)
    if rc == 0:
        parts = stdout.strip().split()
        if len(parts) >= 2:
            beta_ver = parts[1]
    rc, stdout, _ = run_command(["rustc", "+nightly", "--version"], timeout=10)
    if rc == 0:
        parts = stdout.strip().split()
        if len(parts) >= 2:
            nightly_ver = parts[1]

    summary = f"""
<!-- 以下由 scripts/quarterly_sync.py 于 {date_str} 自动生成 -->

### 自动采集摘要

| 版本类型 | 版本号 | 项目当前使用 | 状态 |
|:---|:---|:---:|:---|
| 当前 rustc | {rustc_ver} | - | - |
| 最新稳定版 (Stable) | {latest_ver} | {'✅' if latest_ver == msrv else '⚠️'} | {'已同步' if latest_ver == msrv else f'项目 MSRV 为 {msrv}'} |
| Beta | {beta_ver} | - | 跟踪中 |
| Nightly | {nightly_ver} | - | 跟踪中 |
| 项目 MSRV | {msrv} | - | - |
| 项目 Edition | {edition} | - | - |

"""

    insert_marker = "## 1️⃣ Rust 新版本发布跟踪"
    if insert_marker in content:
        content = content.replace(insert_marker, summary + "\n---\n\n" + insert_marker)
    else:
        content += "\n" + summary

    return content


def main():
    parser = argparse.ArgumentParser(description="季度同步与 Rust 版本对齐检查清单生成器")
    parser.add_argument("--year", type=int, default=datetime.now().year, help="年份（默认当前年份）")
    parser.add_argument("--quarter", type=int, default=(datetime.now().month - 1) // 3 + 1, help="季度 1-4（默认当前季度）")
    parser.add_argument("--executor", default="", help="执行人姓名")
    parser.add_argument("--output-dir", type=Path, default=OUTPUT_DIR, help="输出目录")
    parser.add_argument(
        "--skip-commands",
        action="store_true",
        help="跳过 cargo 等耗时命令，仅填充表头和静态字段",
    )
    parser.add_argument(
        "--quarterly-only",
        action="store_true",
        help="仅生成季度同步检查清单",
    )
    parser.add_argument(
        "--rust-version-only",
        action="store_true",
        help="仅生成 Rust 版本对齐检查清单",
    )
    args = parser.parse_args()

    year = args.year
    quarter = max(1, min(4, args.quarter))
    output_dir = args.output_dir

    # 创建输出目录
    quarterly_dir = output_dir / str(year) / f"Q{quarter}"
    rust_version_dir = output_dir / str(year) / f"H{(quarter - 1) // 2 + 1}"
    quarterly_dir.mkdir(parents=True, exist_ok=True)
    rust_version_dir.mkdir(parents=True, exist_ok=True)

    generated_files = []

    if not args.rust_version_only:
        content = generate_quarterly_checklist(year, quarter, args.executor, args.skip_commands)
        out_path = quarterly_dir / f"quarterly-sync-checklist-{year}-Q{quarter}.md"
        out_path.write_text(content, encoding="utf-8")
        generated_files.append(out_path)
        print(f"✅ 已生成: {out_path.relative_to(PROJECT_ROOT)}")

    if not args.quarterly_only:
        content = generate_rust_version_checklist(year, quarter, args.executor, args.skip_commands)
        out_path = rust_version_dir / f"rust-version-alignment-{year}-H{(quarter - 1) // 2 + 1}.md"
        out_path.write_text(content, encoding="utf-8")
        generated_files.append(out_path)
        print(f"✅ 已生成: {out_path.relative_to(PROJECT_ROOT)}")

    print(f"\n生成完成。共 {len(generated_files)} 个文件。")
    return 0


if __name__ == "__main__":
    sys.exit(main())
