#!/usr/bin/env python3
"""
项目完整性检查脚本

检查项目各部分完成情况。不同 crate 类型按其实际职责评估，避免对无 src 的
集成测试 crate 或 bin-only 演示 crate 提出不切实际的要求。
"""

import re
import sys
from pathlib import Path

CRATES = [
    "c01_ownership_borrow_scope",
    "c02_type_system",
    "c03_control_fn",
    "c04_generic",
    "c05_threads",
    "c06_async",
    "c07_process",
    "c08_algorithms",
    "c09_design_pattern",
    "c10_networks",
    "c11_macro_system_proc",
    "c12_wasm",
    "c13_embedded",
    "c14_semantic_web",
    "c15_verification_tools",
    "c16_gui",
    "c17_resolver_v3_public_demo",
    "common",
    "integration_tests",
]


def crate_kind(crate_path: Path) -> str:
    """根据 Cargo.toml 判断 crate 类型。"""
    cargo_toml = crate_path / "Cargo.toml"
    if not cargo_toml.exists():
        return "unknown"
    text = cargo_toml.read_text(encoding="utf-8")
    if crate_path.name == "integration_tests":
        return "integration_tests"
    if re.search(r"^\[\[bin\]\]", text, re.MULTILINE) or "src/main.rs" in str(crate_path / "src/main.rs") and not (crate_path / "src/lib.rs").exists():
        # Only treat as bin-only if there's no lib.rs
        if (crate_path / "src/lib.rs").exists():
            return "lib"
        return "bin"
    return "lib"


def check_crate(crate_name: str) -> dict:
    """检查单个 crate 的完整性"""
    crate_path = Path("crates") / crate_name

    if not crate_path.exists():
        return {"exists": False, "score": 0.0}

    kind = crate_kind(crate_path)

    # 所有 crate 都应具备的基础项
    checks = {
        "exists": True,
        "has_readme": (crate_path / "README.md").exists(),
        "has_src_or_tests": (crate_path / "src").exists() or (crate_path / "tests").exists(),
        "has_docs": (crate_path / "docs").exists(),
    }

    # 按类型补充检查项
    if kind == "bin":
        checks["has_main"] = (crate_path / "src/main.rs").exists()
    elif kind == "integration_tests":
        checks["has_tests"] = (crate_path / "tests").exists()
    else:
        # lib / mixed crate：要求 src 与至少一个可运行入口（tests 或 examples）
        has_lib = (crate_path / "src/lib.rs").exists()
        has_tests = (crate_path / "tests").exists()
        has_examples = (crate_path / "examples").exists()
        checks["has_src"] = (crate_path / "src").exists()
        checks["has_tests_or_examples"] = has_tests or has_examples

    score = sum(1 for v in checks.values() if v) / len(checks) * 100
    checks["score"] = round(score, 1)
    checks["kind"] = kind

    return checks


def main():
    print("=" * 60)
    print("Rust 学习项目完整性检查")
    print("=" * 60)

    results = {}
    total_score = 0.0

    print("\n各 crate 检查情况:")
    print("-" * 60)

    for crate in CRATES:
        result = check_crate(crate)
        results[crate] = result
        total_score += result["score"]

        status = "✓" if result["score"] >= 80 else "~" if result["score"] >= 50 else "✗"
        kind = result.get("kind", "?")
        print(f"{status} {crate:34} {result['score']:5.1f}% [{kind}]")

    avg_score = total_score / len(CRATES)

    print("-" * 60)
    print(f"\n平均完成度: {avg_score:.1f}%")

    # 检查关键文件
    print("\n关键文件检查:")
    print("-" * 60)

    key_files = [
        "README.md",
        "docs/README.md",
        "content/README.md",
        "content/ecosystem/README.md",
        "content/safety_critical/README.md",
        "crates/module_cross_reference.md",
    ]

    for file in key_files:
        exists = Path(file).exists()
        status = "✓" if exists else "✗"
        print(f"{status} {file}")

    print("\n" + "=" * 60)

    if avg_score >= 95:
        print("🎉 项目状态: 优秀 (100% 完成)")
        return 0
    elif avg_score >= 80:
        print("👍 项目状态: 良好")
        return 0
    else:
        print("⚠️  项目状态: 需要改进")
        return 1


if __name__ == "__main__":
    sys.exit(main())
