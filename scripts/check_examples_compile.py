#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""检查根 examples/ 游离示例文件的编译健康（P3-5 编译保护门）。

背景：
    根 `examples/` 下的 .rs 文件不是 Cargo workspace 成员，不被任何标准
    质量门编译，存在腐烂风险。本脚本提供轻量编译保护：

    1. STDLIB_EXAMPLES — 无外部依赖，直接用 `rustc --edition 2024` 试编译；
    2. DEPENDENT_EXAMPLES — 需要 tokio/axum 等依赖，通过
       `examples/examples_check/` 轻量 bin crate（独立 workspace，
       `cargo check --offline`）编译；
    3. EXEMPT_EXAMPLES — Cargo Script 格式（frontmatter/shebang），
       需 `cargo +nightly -Zscript`，本门豁免并记录原因。

用法：
    python scripts/check_examples_compile.py            # 观察模式：失败仅告警，exit 0
    python scripts/check_examples_compile.py --strict   # 阻断模式：任何失败 exit 1

新增游离 .rs 文件时，必须将其登记到上述三个列表之一，否则本门失败。
"""

import argparse
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXAMPLES_DIR = ROOT / "examples"
EXAMPLES_CHECK_CRATE = EXAMPLES_DIR / "examples_check"

# 无外部依赖：rustc 直接编译
STDLIB_EXAMPLES = [
    "advanced_usage_examples.rs",
    "comprehensive_integration_example.rs",
    "concurrent_data_structures.rs",
    "module_complete_examples.rs",
    "real_world_applications.rs",
    "rust_194_array_windows_demo.rs",
    "rust_194_control_flow_demo.rs",
    "rust_194_lazy_lock_demo.rs",
    "rust_194_lazylock_patterns.rs",
]

# 需要外部依赖：由 examples/examples_check/ crate 的 [[bin]] 目标编译
DEPENDENT_EXAMPLES = [
    "comprehensive_web_server.rs",
    "microservice_template.rs",
    "rust_194_controlflow_patterns.rs",
]

# 豁免：Cargo Script 格式（含 frontmatter/shebang），rustc 无法直接解析
EXEMPT_EXAMPLES = {
    "cargo_script_demo.rs": "Cargo Script 格式（```cargo frontmatter），需 `cargo +nightly -Zscript` 运行",
    "module_system_patterns.rs": "Cargo Script 格式（--- frontmatter），需 `cargo +nightly -Zscript` 运行",
}


def run(cmd, **kwargs):
    return subprocess.run(cmd, capture_output=True, text=True, **kwargs)


def crate_type_for(path: Path) -> str:
    text = path.read_text(encoding="utf-8", errors="replace")
    return "bin" if re.search(r"fn\s+main\s*\(", text) else "lib"


def check_stdlib_examples() -> list[str]:
    failures = []
    with tempfile.TemporaryDirectory(prefix="examples_check_") as tmp:
        out_path = Path(tmp) / "out.bin"
        for name in STDLIB_EXAMPLES:
            src = EXAMPLES_DIR / name
            result = run([
                "rustc", "--edition", "2024",
                "--crate-type", crate_type_for(src),
                str(src), "-o", str(out_path),
            ])
            if result.returncode != 0:
                first_error = next(
                    (line for line in result.stderr.splitlines() if line.startswith("error")),
                    result.stderr.splitlines()[0] if result.stderr else "unknown error",
                )
                failures.append(f"{name}: {first_error}")
                print(f"❌ [stdlib] {name}\n   {first_error}")
            else:
                print(f"✅ [stdlib] {name}")
    return failures


def check_dependent_examples() -> list[str]:
    if not EXAMPLES_CHECK_CRATE.is_dir():
        return [f"缺失编译保护 crate: {EXAMPLES_CHECK_CRATE}"]
    print(f"--- cargo check ({EXAMPLES_CHECK_CRATE.relative_to(ROOT)}) ---")
    result = run(["cargo", "check", "--offline", "--locked"], cwd=EXAMPLES_CHECK_CRATE)
    if result.returncode != 0:
        # --locked 失败（锁文件漂移）时重试一次，避免本地环境差异误报
        result = run(["cargo", "check", "--offline"], cwd=EXAMPLES_CHECK_CRATE)
    if result.returncode != 0:
        errors = [line for line in result.stderr.splitlines() if line.startswith("error")]
        for line in errors[:10]:
            print(f"   {line}")
        return [f"examples_check crate 编译失败（{len(errors)} 个错误）: " + (errors[0] if errors else "unknown")]
    print(f"✅ [deps] {', '.join(DEPENDENT_EXAMPLES)}")
    return []


def check_registry() -> list[str]:
    """确保每个游离 .rs 文件都被登记，防止新增文件绕过编译保护。"""
    registered = set(STDLIB_EXAMPLES) | set(DEPENDENT_EXAMPLES) | set(EXEMPT_EXAMPLES)
    actual = {p.name for p in EXAMPLES_DIR.glob("*.rs")}
    failures = []
    for name in sorted(actual - registered):
        failures.append(f"未登记的游离示例: examples/{name}（请登记到 STDLIB/DEPENDENT/EXEMPT 之一）")
        print(f"❌ [registry] {name} 未登记")
    for name in sorted(registered - actual):
        failures.append(f"登记了不存在的示例: {name}（请从列表移除）")
        print(f"❌ [registry] {name} 已登记但文件不存在")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--strict", action="store_true", help="失败时 exit 1（默认仅告警）")
    args = parser.parse_args()

    failures = []
    failures += check_registry()
    failures += check_stdlib_examples()
    failures += check_dependent_examples()

    print("\n--- 豁免清单（Cargo Script 格式，不参与本门编译）---")
    for name, reason in EXEMPT_EXAMPLES.items():
        print(f"⚠️  [exempt] {name}: {reason}")

    print(f"\n总计: {len(STDLIB_EXAMPLES)} stdlib + {len(DEPENDENT_EXAMPLES)} deps "
          f"+ {len(EXEMPT_EXAMPLES)} exempt，失败 {len(failures)} 项")
    if failures:
        for f in failures:
            print(f"FAIL: {f}", file=sys.stderr)
        if args.strict:
            return 1
        print("（观察模式：未启用 --strict，exit 0）")
    return 0


if __name__ == "__main__":
    sys.exit(main())
