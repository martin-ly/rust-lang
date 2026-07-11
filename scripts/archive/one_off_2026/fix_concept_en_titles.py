#!/usr/bin/env python3
"""修复 concept/ 中英文标题占位问题。

策略：
1. 为缺失 H1 的文件补充中文 H1。
2. 将英文 H1 替换为中文 H1（EN 字段保留或改进为更描述性）。
3. 更新 EN 字段为更具体、国际化的标题。
"""

import re
from pathlib import Path

CONCEPT_DIR = Path("concept")

# 路径 -> (中文 H1, 新 EN 标题或 None 表示保留原 EN)
TITLE_UPDATES: dict[str, tuple[str, str | None]] = {
    # 非归档：补充/替换 H1 并润色 EN
    "02_intermediate/22_api_naming_conventions.md": (
        "Rust API 命名约定",
        "Idiomatic Rust API Naming Conventions",
    ),
    "03_advanced/03_unsafe.md": (
        "Unsafe Rust 安全编程",
        "Safe and Effective Unsafe Rust",
    ),
    "04_formal/23_borrow_sanitizer.md": (
        "BorrowSanitizer 运行时别名模型检测",
        "BorrowSanitizer: Runtime Tree Borrows Violation Detection",
    ),
    "04_formal/24_autoverus.md": (
        "AutoVerus / Verus 自动证明生态",
        "AutoVerus and Verus Automated Verification Ecosystem",
    ),
    "05_comparative/14_rust_vs_elixir.md": (
        "Rust vs Elixir 对比分析",
        "Rust vs Elixir: Concurrency and Fault Tolerance Comparison",
    ),
    "06_ecosystem/09_cargo_script.md": (
        "Cargo Script 脚本化 Rust",
        "Cargo Script: Writing and Running Rust Scripts",
    ),
    "06_ecosystem/10_public_private_deps.md": (
        "Cargo 公共与私有依赖",
        "Public and Private Dependencies in Cargo",
    ),
    "06_ecosystem/39_os_kernel.md": (
        "Rust 操作系统内核开发",
        "Rust for Operating System Kernel Development",
    ),
    "06_ecosystem/45_compiler_internals.md": (
        "Rust 编译器内部原理",
        "Rust Compiler Internals and Driver Architecture",
    ),
    "06_ecosystem/48_industrial_case_studies.md": (
        "Rust 工业应用案例研究",
        "Industrial Rust Adoption Case Studies",
    ),
    "06_ecosystem/51_quantum_computing_rust.md": (
        "Rust 量子计算生态",
        "Rust in Quantum Computing Ecosystems",
    ),
    "06_ecosystem/53_embedded_graphics.md": (
        "Rust 嵌入式图形开发",
        "Embedded Graphics Development with Rust",
    ),
    "06_ecosystem/54_webassembly_advanced.md": (
        "Rust WebAssembly 高级开发",
        "Advanced WebAssembly Development with Rust",
    ),
    "06_ecosystem/55_rust_for_data_science.md": (
        "Rust 数据科学与科学计算",
        "Rust for Data Science and Scientific Computing",
    ),
    "06_ecosystem/58_platform_rust_integration.md": (
        "将 Rust 集成到现有平台",
        "Integrating Rust into Existing Platforms and Codebases",
    ),
    "07_future/12_inline_const_pattern_preview.md": (
        "Inline Const Pattern 预览（Rust 1.98+ Nightly）",
        "Inline Const Pattern Preview (Rust 1.98+ Nightly)",
    ),
    "07_future/15_rpitit_preview.md": (
        "特质中返回位置 impl Trait（RPITIT）预览",
        "Return Position Impl Trait In Traits (RPITIT) Preview",
    ),
    "07_future/17_const_trait_preview.md": (
        "Const Trait 实现预览",
        "Const Trait Implementation Preview",
    ),
    "07_future/22_gen_blocks_preview.md": (
        "Generator Blocks（gen）预览",
        "Generator Blocks (gen) Preview",
    ),
    "SUMMARY.md": (
        "目录",
        "Table of Contents",
    ),
    # 归档文件：补充中文 H1，EN 保持 "... Archived" 不变
    "archive/01.md": ("归档条目", None),
    "archive/01_foundation_19_numerics_archived.md": ("归档：数值类型基础", None),
    "archive/02_intermediate_22_iterator_patterns_archived.md": ("归档：迭代器模式", None),
    "archive/03_advanced_02_async_programming_archived.md": ("归档：异步编程", None),
    "archive/03_advanced_03_unsafe_rust_archived.md": ("归档：Unsafe Rust", None),
    "archive/03_advanced_05_macros_archived.md": ("归档：宏系统", None),
    "archive/03_advanced_08_zero_cost_abstractions_archived.md": ("归档：零成本抽象", None),
    "archive/03_advanced_13_async_patterns_archived.md": ("归档：异步模式", None),
    "archive/04_formal_07_separation_logic_archived.md": ("归档：分离逻辑", None),
    "archive/04_formal_09_operational_semantics_archived.md": ("归档：操作语义", None),
    "archive/05_comparative_16_rust_vs_ruby_archived.md": ("归档：Rust vs Ruby", None),
    "archive/06_ecosystem_33_idioms_spectrum_archived.md": ("归档：惯用法谱系", None),
    "archive/06_ecosystem_34_formal_ecosystem_tower_archived.md": ("归档：形式化生态塔", None),
}


def process_file(path: Path, h1: str, new_en: str | None) -> str:
    text = path.read_text(encoding="utf-8")

    # 更新 EN 字段（支持 `> **EN**: ...` 引用块前缀）
    if new_en is not None:
        text = re.sub(r"^(>\s*\*\*EN\*\*:\s*).+$", rf"\g<1>{new_en}", text, flags=re.MULTILINE)

    # 替换已有的 H1
    if re.search(r"^#\s+(.+)$", text, re.MULTILINE):
        text = re.sub(r"^#\s+(.+)$", f"# {h1}", text, count=1, flags=re.MULTILINE)
    else:
        # 没有 H1 时，在文件开头插入
        text = f"# {h1}\n\n{text}"
    return text


def main():
    for rel, (h1, new_en) in TITLE_UPDATES.items():
        path = CONCEPT_DIR / rel
        if not path.exists():
            print(f"skip (missing): {path}")
            continue
        new_text = process_file(path, h1, new_en)
        path.write_text(new_text, encoding="utf-8")
        print(f"updated: {path}")


if __name__ == "__main__":
    main()
