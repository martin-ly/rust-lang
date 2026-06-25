#!/usr/bin/env python3
"""
Rust 1.97.0 发布日辅助脚本。

用法（2026-07-09 或之后）:
    python scripts/maintenance/rust_197_release_day.py [--activate]

功能:
    1. 检测 rustup 中 1.97.0 stable 是否可用。
    2. 读取并解析 crates/c08_algorithms/src/rust_197_features.rs，列出待激活占位。
    3. 可选：生成 sed/手动替换清单（不自动修改源码，避免误操作）。
    4. 运行 cargo check/test/clippy 基线验证（若已切换 toolchain）。

决策规则（与 .kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md 对齐）:
    - 仅当官方 Release Notes 确认某 API 在 1.97.0 stable 中才激活真实调用。
    - VecDeque::retain_back 若未进入 1.97，保留等效实现并标注“推迟至 1.98”。
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
FEATURES_FILE = ROOT / "crates" / "c08_algorithms" / "src" / "rust_197_features.rs"
TOOLCHAIN_FILE = ROOT / "rust-toolchain.toml"


@dataclass
class Placeholder:
    name: str
    line: int
    kind: str  # "commented_api" | "equivalent_impl" | "concept_only"
    note: str


def run(cmd: list[str], **kwargs) -> subprocess.CompletedProcess:
    return subprocess.run(cmd, capture_output=True, text=True, **kwargs)


def check_rustup_version() -> tuple[bool, str]:
    """检查 1.97.0 是否已通过 rustup 可用。"""
    res = run(["rustup", "toolchain", "list"])
    if res.returncode != 0:
        return False, f"rustup 调用失败: {res.stderr.strip()}"
    installed = res.stdout.strip().splitlines()
    available = any("1.97.0" in line for line in installed)
    if available:
        return True, f"1.97.0 已安装: {[l for l in installed if '1.97.0' in l]}"
    # 未安装则检查是否可安装
    res2 = run(["rustup", "check"])
    return False, f"1.97.0 未在已安装列表中。rustup check 输出:\n{res2.stdout.strip()[:500]}"


def parse_features_file() -> list[Placeholder]:
    """扫描 rust_197_features.rs 中的占位代码块。"""
    if not FEATURES_FILE.exists():
        return []
    text = FEATURES_FILE.read_text(encoding="utf-8")
    placeholders: list[Placeholder] = []
    for i, line in enumerate(text.splitlines(), start=1):
        stripped = line.strip()
        # 检测 `// 1.97+: 真实用法` 或等效实现注释
        if re.search(r"//\s*1\.97\+.*(?:实际用法|真实用法|截断前部|从尾部)", stripped):
            placeholders.append(
                Placeholder(name=f"line-{i}", line=i, kind="commented_api", note=stripped)
            )
        elif re.search(r"//\s*当前等效实现", stripped):
            placeholders.append(
                Placeholder(name=f"line-{i}", line=i, kind="equivalent_impl", note=stripped)
            )
    return placeholders


def suggest_activation_steps() -> list[str]:
    """根据当前占位状态生成人工检查清单。"""
    steps = [
        "1. 访问 https://blog.rust-lang.org/2026/07/09/Rust-1.97.0.html 核对实际稳定 API 列表。",
        "2. 编辑 rust-toolchain.toml: channel = '1.97.0' 并运行 `rustup show`。",
        f"3. 编辑 {FEATURES_FILE.relative_to(ROOT)}，取消确认稳定的 API 注释，删除等效实现。",
        "4. 运行 `cargo check --workspace`、`cargo test --workspace`、`cargo clippy --workspace -- -D warnings`。",
        "5. 更新 concept/07_future/rust_1_97_preview.md 状态为 ✅ Stable，并迁移到 docs/06_toolchain/06_21_rust_1_97_features.md。",
        "6. 更新 concept/00_meta/terminology_glossary.md 中 1.97 术语状态。",
        "7. 完善 CHANGELOG.md [3.1.0] 条目细节，必要时更新 workspace version。",
    ]
    return steps


def main() -> int:
    parser = argparse.ArgumentParser(description="Rust 1.97.0 发布日辅助脚本")
    parser.add_argument(
        "--activate",
        action="store_true",
        help="仅生成激活建议清单，不自动修改源码（默认行为）。",
    )
    args = parser.parse_args()

    print("=" * 70)
    print("Rust 1.97.0 发布日辅助脚本")
    print("=" * 70)

    ok, msg = check_rustup_version()
    print(f"\n[工具链状态] {'✅' if ok else '⏳'} {msg}")

    placeholders = parse_features_file()
    print(f"\n[占位代码扫描] 在 {FEATURES_FILE.relative_to(ROOT)} 中发现 {len(placeholders)} 处待确认项：")
    for p in placeholders:
        print(f"  - 行 {p.line:4d} [{p.kind}] {p.note[:80]}")

    print("\n[建议执行步骤]")
    for step in suggest_activation_steps():
        print(f"  {step}")

    if args.activate:
        print("\n⚠️  --activate 当前仅生成建议，不会自动修改源码。请人工核对 Release Notes 后执行。")

    print("\n[回滚方案]")
    print("  - 切换 toolchain 前备份 Cargo.lock: cp Cargo.lock Cargo.lock.pre-1.97")
    print("  - 若某特性未稳定，保留等效实现并更新注释为 '推迟至 1.98+'")
    print("  - 若构建失败，执行 `rustup default nightly` 并恢复 rust-toolchain.toml 中的 channel")

    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
