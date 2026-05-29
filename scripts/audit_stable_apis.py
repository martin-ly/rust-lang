#!/usr/bin/env python3
"""
Rust 稳定版 API 审计脚本

扫描 crates/ 目录中的 rust_*_features.rs 文件，
与已知的新稳定 API 列表进行对比，生成缺失报告。

用法:
    python scripts/audit_stable_apis.py [--version 1.96.0]
"""

import argparse
import os
import re
import sys
from pathlib import Path
from typing import Dict, List, Set, Tuple

# 已知的新稳定 API 清单（按版本分类）
# 格式: (API 名称, 模块, 建议位置)
KNOWN_APIS: Dict[str, List[Tuple[str, str, str]]] = {
    "1.95.0": [
        ("MaybeUninit<[T; N]>: From<[MaybeUninit<T>; N]>", "core::mem", "c01_ownership"),
        ("MaybeUninit<[T; N]>: AsRef<[MaybeUninit<T>; N]>", "core::mem", "c01_ownership"),
        ("MaybeUninit<[T; N]>: AsMut<[MaybeUninit<T>; N]>", "core::mem", "c01_ownership"),
        ("[MaybeUninit<T>; N]: From<MaybeUninit<[T; N]>>", "core::mem", "c01_ownership"),
        ("Cell<[T; N]>: AsRef<[Cell<T>; N]>", "core::cell", "c01_ownership"),
        ("bool: TryFrom<{integer}>", "core::convert", "c02_type_system"),
        ("AtomicPtr::update", "core::sync::atomic", "c05_threads"),
        ("AtomicPtr::try_update", "core::sync::atomic", "c05_threads"),
        ("AtomicBool::update", "core::sync::atomic", "c05_threads"),
        ("AtomicBool::try_update", "core::sync::atomic", "c05_threads"),
        ("cfg_select!", "core::macros", "c11_macro_system"),
        ("core::range::RangeInclusive", "core::range", "c02_type_system"),
        ("core::range::RangeInclusiveIter", "core::range", "c02_type_system"),
        ("core::hint::cold_path", "core::hint", "c05_threads"),
        ("<*const T>::as_ref_unchecked", "core::ptr", "c13_embedded"),
        ("<*mut T>::as_mut_unchecked", "core::ptr", "c13_embedded"),
        ("Vec::push_mut", "alloc::vec", "c08_algorithms"),
        ("Vec::insert_mut", "alloc::vec", "c08_algorithms"),
        ("VecDeque::push_front_mut", "alloc::collections", "c08_algorithms"),
        ("VecDeque::push_back_mut", "alloc::collections", "c08_algorithms"),
        ("VecDeque::insert_mut", "alloc::collections", "c08_algorithms"),
        ("LinkedList::push_front_mut", "alloc::collections", "c08_algorithms"),
        ("LinkedList::push_back_mut", "alloc::collections", "c08_algorithms"),
        ("Layout::dangling_ptr", "core::alloc", "c01_ownership"),
        ("Layout::repeat", "core::alloc", "c01_ownership"),
        ("Layout::repeat_packed", "core::alloc", "c01_ownership"),
        ("Layout::extend_packed", "core::alloc", "c01_ownership"),
        ("fmt::from_fn (const)", "core::fmt", "c02_type_system"),
        ("ControlFlow::is_break (const)", "core::ops", "c03_control_fn"),
        ("ControlFlow::is_continue (const)", "core::ops", "c03_control_fn"),
    ],
    "1.96.0": [
        ("assert_matches!", "std::assert_matches", "c02_type_system"),
        ("core::range::Range", "core::range", "c02_type_system"),
        ("core::range::RangeFrom", "core::range", "c02_type_system"),
        ("core::range::RangeToInclusive", "core::range", "c02_type_system"),
        ("NonZero range iteration (Step)", "core::num", "c02_type_system"),
        ("From<T> for LazyCell", "std::cell", "c02_type_system"),
        ("From<T> for LazyLock", "std::sync", "c02_type_system"),
        ("From<T> for AssertUnwindSafe", "std::panic", "c02_type_system"),
        ("ManuallyDrop const pattern", "core::mem", "c02_type_system"),
        ("expr metavariable to cfg", "macro", "c11_macro_system"),
    ],
}


def scan_crate_features(crate_dir: Path) -> Set[str]:
    """扫描单个 crate 中已实现的特性关键词。"""
    features: Set[str] = set()
    
    for rs_file in crate_dir.rglob("rust_*_features.rs"):
        content = rs_file.read_text(encoding="utf-8")
        # 提取文档注释和函数名中的关键词
        # 简单启发式：查找已知 API 名称的片段
        features.update(extract_feature_keywords(content))
    
    return features


def extract_feature_keywords(content: str) -> Set[str]:
    """从文件内容中提取已实现的特性关键词。"""
    keywords: Set[str] = set()
    
    # 匹配常见的特性标识模式
    patterns = [
        r"push_mut",
        r"insert_mut",
        r"try_update",
        r"cfg_select",
        r"RangeInclusive",
        r"cold_path",
        r"as_ref_unchecked",
        r"as_mut_unchecked",
        r"MaybeUninit.*数组",
        r"dangling_ptr",
        r"repeat_packed",
        r"extend_packed",
        r"bool::try_from",
        r"fmt::from_fn",
        r"ControlFlow::is_break",
        r"ControlFlow::is_continue",
    ]
    
    for pattern in patterns:
        if re.search(pattern, content, re.IGNORECASE):
            keywords.add(pattern)
    
    return keywords


def check_api_coverage(crate_dir: Path, known_apis: List[Tuple[str, str, str]]) -> List[Tuple[str, str, str]]:
    """检查已知 API 是否在 crate 中已有实现。"""
    implemented = scan_crate_features(crate_dir)
    missing: List[Tuple[str, str, str]] = []
    
    for api_name, module, suggested_crate in known_apis:
        # 简单启发式：检查 API 名称的关键词是否在已实现的特性中
        api_keywords = api_name.lower().replace("::", " ").replace("<", " ").replace(">", " ").split()
        found = False
        
        for keyword in implemented:
            if any(kw in api_name.lower() for kw in keyword.lower().split("_")):
                found = True
                break
        
        if not found:
            # 额外检查：直接搜索 API 名称片段
            for rs_file in crate_dir.rglob("*.rs"):
                content = rs_file.read_text(encoding="utf-8")
                # 提取 API 的核心标识符
                core_idents = re.findall(r"[a-z_]+[a-z0-9_]*", api_name.lower())
                if any(ident in content.lower() for ident in core_idents if len(ident) > 3):
                    found = True
                    break
        
        if not found:
            missing.append((api_name, module, suggested_crate))
    
    return missing


def main():
    parser = argparse.ArgumentParser(description="Audit Rust stable APIs in project crates")
    parser.add_argument("--version", default="1.96.0", help="Rust version to audit (default: 1.96.0)")
    parser.add_argument("--crates-dir", default="crates", help="Path to crates directory")
    args = parser.parse_args()
    
    crates_dir = Path(args.crates_dir)
    if not crates_dir.exists():
        print(f"Error: {crates_dir} does not exist", file=sys.stderr)
        sys.exit(1)
    
    version = args.version
    known_apis = KNOWN_APIS.get(version, [])
    
    if not known_apis:
        print(f"No known API list for version {version}")
        sys.exit(0)
    
    print(f"=== Rust {version} API 审计报告 ===")
    print(f"扫描目录: {crates_dir.absolute()}")
    print()
    
    total_missing = 0
    
    # 按建议 crate 分组
    by_crate: Dict[str, List[Tuple[str, str]]] = {}
    for api_name, module, suggested_crate in known_apis:
        crate_dir = crates_dir / suggested_crate
        if crate_dir.exists():
            missing = check_api_coverage(crate_dir, [(api_name, module, suggested_crate)])
            if missing:
                by_crate.setdefault(suggested_crate, []).append((api_name, module))
                total_missing += 1
        else:
            by_crate.setdefault(suggested_crate, []).append((api_name, module))
            total_missing += 1
    
    if total_missing == 0:
        print("✅ 所有已知 API 均已覆盖！")
        return
    
    print(f"发现 {total_missing} 个可能缺失的 API:\n")
    
    for crate_name, apis in sorted(by_crate.items()):
        print(f"### {crate_name}")
        for api_name, module in apis:
            print(f"  - [{module}] {api_name}")
        print()
    
    print("=" * 50)
    print("注意: 本脚本使用启发式扫描，可能存在误报或漏报。")
    print("建议人工复核后再决定补充。")


if __name__ == "__main__":
    main()
