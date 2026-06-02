#!/usr/bin/env python3
"""
修复 Cargo.toml 元数据不完整的问题
"""

import os
import re
from pathlib import Path

# 项目根目录
ROOT_DIR = Path("E:/_src/rust-lang")
CRATES_DIR = ROOT_DIR / "crates"

# 标准化的元数据模板
METADATA_TEMPLATE = '''authors = ["Rust Learning Community"]
description = "{description}"
license = "MIT OR Apache-2.0"
repository = "https://github.com/rust-lang/rust-lang-learning"
'''

# 每个 crate 的描述
CRATE_DESCRIPTIONS = {
    "c01_ownership_borrow_scope": "Rust ownership, borrowing, and scope system learning module",
    "c02_type_system": "Rust type system comprehensive learning module",
    "c03_control_fn": "Rust control flow and functions learning module",
    "c04_generic": "Rust generics and trait system learning module",
    "c05_threads": "Rust concurrency and threading learning module",
    "c06_async": "Rust asynchronous programming learning module",
    "c07_process": "Rust process management and IPC learning module",
    "c08_algorithms": "Rust algorithms and data structures learning module",
    "c09_design_pattern": "Rust design patterns learning module",
    "c10_networks": "Rust network programming learning module",
    "c11_macro_system": "Rust macro system and metaprogramming learning module",
    "c12_wasm": "Rust WebAssembly learning module",
}

def fix_cargo_toml(crate_name: str):
    """修复单个 Cargo.toml 文件"""
    cargo_path = CRATES_DIR / crate_name / "Cargo.toml"
    
    if not cargo_path.exists():
        print(f"❌ {crate_name}/Cargo.toml 不存在")
        return
    
    content = cargo_path.read_text(encoding='utf-8')
    
    # 检查是否已有元数据
    has_authors = 'authors' in content
    has_description = 'description' in content
    has_license = 'license' in content
    has_repository = 'repository' in content
    
    if all([has_authors, has_description, has_license, has_repository]):
        print(f"✅ {crate_name} 已有完整元数据")
        return
    
    # 准备要添加的元数据
    description = CRATE_DESCRIPTIONS.get(crate_name, f"Rust learning module - {crate_name}")
    metadata_to_add = []
    
    if not has_authors:
        metadata_to_add.append('authors = ["Rust Learning Community"]')
    if not has_description:
        metadata_to_add.append(f'description = "{description}"')
    if not has_license:
        metadata_to_add.append('license = "MIT OR Apache-2.0"')
    if not has_repository:
        metadata_to_add.append('repository = "https://github.com/rust-lang/rust-lang-learning"')
    
    # 在 [package] 部分后插入元数据
    new_metadata = '\n'.join(metadata_to_add)
    
    # 找到 [package] 部分的结束位置
    lines = content.split('\n')
    package_end_idx = 0
    in_package = False
    
    for i, line in enumerate(lines):
        if line.strip() == '[package]':
            in_package = True
        elif in_package and line.startswith('[') and line.strip() != '[package]':
            package_end_idx = i
            break
        elif in_package and i == len(lines) - 1:
            package_end_idx = i + 1
    
    if package_end_idx > 0:
        new_lines = lines[:package_end_idx] + [''] + new_metadata.split('\n') + [''] + lines[package_end_idx:]
        new_content = '\n'.join(new_lines)
        cargo_path.write_text(new_content, encoding='utf-8')
        print(f"✅ 已修复 {crate_name}/Cargo.toml")
    else:
        print(f"⚠️ 无法确定 {crate_name} 的 [package] 部分结束位置")

def main():
    print("🔧 开始修复 Cargo.toml 元数据...\n")
    
    for crate_name in CRATE_DESCRIPTIONS.keys():
        fix_cargo_toml(crate_name)
    
    print("\n✅ Cargo.toml 修复完成")

if __name__ == "__main__":
    main()
