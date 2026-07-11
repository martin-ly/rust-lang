#!/usr/bin/env python3
"""
批量修复跨层引用问题。
为每个缺少向下引用的文件添加一个指向直接低一层级的链接。
"""

import json
import re
from pathlib import Path

with open("concept_kb.json", encoding="utf-8") as f:
    KB = json.load(f)

LAYER_ORDER = {"L0": 0, "L1": 1, "L2": 2, "L3": 3, "L4": 4, "L5": 5, "L6": 6, "L7": 7}

# 每个层级到直接低一层级的默认引用（使用 ../ 相对路径）
LAYER_LOWER_REF = {
    "L1": "[概念索引](../00_meta/concept_index.md)",
    "L2": "[Ownership](../01_foundation/01_ownership.md)",
    "L3": "[Traits](../02_intermediate/01_traits.md)",
    "L4": "[Concurrency](../03_advanced/01_concurrency.md)",
    "L5": "[Type Theory](../04_formal/02_type_theory.md)",
    "L6": "[Rust vs C++](../05_comparative/01_rust_vs_cpp.md)",
    "L7": "[Toolchain](../06_ecosystem/01_toolchain.md)",
}


def get_layer_from_path(ref: str) -> str:
    for part in Path(ref).parts:
        if part.startswith("0") and len(part) >= 2 and part[1].isdigit():
            return f"L{part[1]}"
    return None


def find_insertion_point(content: str) -> int:
    """在第一个 ## 标题之前插入"""
    match = re.search(r"\n## ", content)
    if match:
        return match.start() + 1
    return len(content)


def fix_file(file_info: dict) -> bool:
    filepath = Path(file_info["path"])
    layer = file_info["layer"]
    current_num = LAYER_ORDER.get(layer, -1)
    if current_num <= 0:
        return False
    
    expected_lower = f"L{current_num - 1}"
    
    # 检查是否已有向下引用
    for ref in file_info.get("cross_references", []):
        if get_layer_from_path(ref) == expected_lower:
            return False
    
    # 添加向下引用
    if layer not in LAYER_LOWER_REF:
        return False
    
    content = filepath.read_text(encoding="utf-8")
    insert_pos = find_insertion_point(content)
    section = f"> **前置依赖**: {LAYER_LOWER_REF[layer]}\n\n"
    new_content = content[:insert_pos] + section + content[insert_pos:]
    filepath.write_text(new_content, encoding="utf-8")
    return True


def main():
    fixed = 0
    for file_info in KB["files"]:
        if fix_file(file_info):
            print(f"  ✅ 已添加跨层引用: {file_info['path']}")
            fixed += 1
    print(f"\n总计: 为 {fixed} 个文件添加了跨层引用")


if __name__ == "__main__":
    main()
