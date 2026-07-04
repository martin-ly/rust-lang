#!/usr/bin/env python3
"""
concept/ 目录统一配置。

集中维护：
- L0-L7 层级映射
- 各层级推荐的主题子目录
- 权威来源 URL 模板
- 文件命名与路径约定

所有操作 concept/ 的脚本都应从此模块读取配置，避免硬编码路径。
"""

from __future__ import annotations

from pathlib import Path
from typing import Final

# project root relative to this file
PROJECT_ROOT: Final[Path] = Path(__file__).resolve().parent.parent
CONCEPT_DIR: Final[Path] = PROJECT_ROOT / "concept"

# L0-L7 层级映射（目录名 -> 层级标签）
LAYER_DIRS: Final[dict[str, str]] = {
    "00_meta": "L0",
    "01_foundation": "L1",
    "02_intermediate": "L2",
    "03_advanced": "L3",
    "04_formal": "L4",
    "05_comparative": "L5",
    "06_ecosystem": "L6",
    "07_future": "L7",
}

# 各层级推荐的主题子目录（顺序即建议的排序）
# 用于 validate_summary.py、文件创建建议、目录重构指导。
THEME_SUBDIRS: Final[dict[str, list[str]]] = {
    "00_meta": [
        "00_framework",       # 认知框架、方法论、学习路径
        "01_terminology",     # 术语表、双语模板、i18n
        "02_sources",         # 权威来源、RFC 索引、来源地图
        "03_audit",           # 审计清单、质量指南、Bloom 规范
        "04_navigation",      # 索引、SUMMARY、知识图谱入口
        "knowledge_topology", # 已有子目录，保留
    ],
    "01_foundation": [
        "00_start",
        "01_ownership_borrow_lifetime",
        "02_type_system",
        "03_values_and_references",
        "04_control_flow",
        "05_collections",
        "06_strings_and_text",
        "07_modules_and_items",
        "08_error_handling",
        "09_macros_basics",
        "10_testing_basics",
        "11_quizzes",
    ],
    "02_intermediate": [
        "00_traits",
        "01_generics",
        "02_memory_management",
        "03_error_handling",
        "04_types_and_conversions",
        "05_modules_and_visibility",
        "06_macros_and_metaprogramming",
        "07_iterators_and_closures",
        "08_concurrency_basics",
        "09_quizzes",
    ],
    "03_advanced": [
        "00_concurrency",
        "01_async",
        "02_unsafe",
        "03_proc_macros",
        "04_ffi",
        "05_inline_assembly",
        "06_low_level_patterns",
        "07_unsafe_internals",
    ],
    "04_formal": [
        "00_type_theory",
        "01_ownership_logic",
        "02_separation_logic",
        "03_operational_semantics",
        "04_model_checking",
        "05_rustc_internals",
        "06_notation",
    ],
    "05_comparative": [
        "00_paradigms",
        "01_systems_languages",
        "02_managed_languages",
        "03_domain_comparisons",
    ],
    "06_ecosystem": [
        "00_toolchain",
        "01_cargo",
        "02_core_crates",
        "03_design_patterns",
        "04_web_and_networking",
        "05_systems_and_embedded",
        "06_data_and_distributed",
        "07_security_and_cryptography",
        "08_formal_verification",
        "09_testing_and_quality",
        "10_performance",
        "11_domain_applications",
    ],
    "07_future": [
        "00_version_tracking",
        "01_edition_roadmap",
        "02_stabilized_features",
        "03_preview_features",
        "04_research_and_experimental",
        "05_roadmaps",
    ],
}

# 权威来源 URL 模板（用于新文件模板和校验）
AUTHORITY_SOURCES: Final[dict[str, str]] = {
    "trpl": "https://doc.rust-lang.org/book/",
    "reference": "https://doc.rust-lang.org/reference/",
    "nomicon": "https://doc.rust-lang.org/nomicon/",
    "rbe": "https://doc.rust-lang.org/rust-by-example/",
    "edition_guide": "https://doc.rust-lang.org/edition-guide/",
    "unsafe_guidelines": "https://rust-lang.github.io/unsafe-code-guidelines/",
    "rfcs": "https://rust-lang.github.io/rfcs/",
    "std": "https://doc.rust-lang.org/std/",
    "blog": "https://blog.rust-lang.org/",
    "inside_rust": "https://blog.rust-lang.org/inside-rust/",
}

# 稳定 Rust 版本（用于版本对齐）
RUST_VERSION: Final[str] = "1.96.1"
RUST_EDITION: Final[str] = "2024"


def detect_layer(filepath: Path) -> str | None:
    """从路径检测层级 L0-L7。兼容主题子目录。"""
    parts = filepath.parts
    for p in parts:
        if p in LAYER_DIRS:
            return LAYER_DIRS[p]
    return None


def iter_concept_files() -> list[Path]:
    """返回 concept/ 下所有 Markdown 文件（排除 archive/）。"""
    files: list[Path] = []
    if not CONCEPT_DIR.exists():
        return files
    for path in CONCEPT_DIR.rglob("*.md"):
        rel = path.relative_to(CONCEPT_DIR)
        # 排除 archive/ 与 sources/ 中的文件
        if str(rel).startswith("archive/") or str(rel).startswith("sources/"):
            continue
        files.append(path)
    files.sort()
    return files


def is_concept_path(path: Path) -> bool:
    """判断路径是否属于 concept/ 下的有效概念文件。"""
    try:
        rel = path.relative_to(PROJECT_ROOT)
    except ValueError:
        return False
    parts = rel.parts
    if len(parts) < 2 or parts[0] != "concept":
        return False
    return parts[1] in LAYER_DIRS


def get_layer_dir(layer_label: str) -> str | None:
    """由 L0-L7 标签反查目录名。"""
    for d, label in LAYER_DIRS.items():
        if label == layer_label:
            return d
    return None
