#!/usr/bin/env python3
"""
批量修复：
1. 缺少后置概念的文件 → 添加 > **后置概念** 标注
2. 缺少跨层引用的文件 → 添加指向低一层级的链接
"""

import json
import re
from pathlib import Path

with open("concept_kb.json", encoding="utf-8") as f:
    KB = json.load(f)

# 层级顺序
LAYER_ORDER = {"L0": 0, "L1": 1, "L2": 2, "L3": 3, "L4": 4, "L5": 5, "L6": 6, "L7": 7}

# 每个层级的默认后置概念目标（指向更高层级或同层级核心文件）
LAYER_DEFAULT_POST = {
    "L1": "[Traits](../../02_intermediate/01_traits.md) · [Generics](../../02_intermediate/02_generics.md)",
    "L2": "[Concurrency](../../03_advanced/01_concurrency.md) · [Async](../../03_advanced/02_async.md)",
    "L3": "[Formal Verification](../../04_formal/03_ownership_formal.md)",
    "L4": "[Comparative Studies](../../05_comparative/01_rust_vs_cpp.md)",
    "L5": "[Ecosystem](../../06_ecosystem/01_toolchain.md)",
    "L6": "[Future Roadmap](../../07_future/24_roadmap.md)",
    "L7": "[Rust Specification](https://www.rust-lang.org/) · [官方路线图](https://github.com/rust-lang/rust/labels/F-roadmap)",
}

# 每个层级的默认向下引用目标（指向低一层级核心文件）
LAYER_DEFAULT_LOWER = {
    "L1": "[概念索引](../../00_meta/concept_index.md)",
    "L2": "[Ownership](../../01_foundation/01_ownership.md) · [Borrowing](../../01_foundation/02_borrowing.md)",
    "L3": "[Traits](../../02_intermediate/01_traits.md) · [Generics](../../02_intermediate/02_generics.md)",
    "L4": "[Concurrency](../../03_advanced/01_concurrency.md) · [Unsafe](../../03_advanced/03_unsafe.md)",
    "L5": "[Type Theory](../../04_formal/02_type_theory.md)",
    "L6": "[Rust vs C++](../../05_comparative/01_rust_vs_cpp.md)",
    "L7": "[Toolchain](../../06_ecosystem/01_toolchain.md)",
}


def find_insertion_point(content: str) -> int:
    """在定位段落之后、正文之前插入"""
    # 尝试在第一个 ## 标题之前插入
    match = re.search(r"\n## ", content)
    if match:
        return match.start() + 1
    # 否则在文件末尾插入
    return len(content)


def has_post_concept(content: str) -> bool:
    return bool(re.search(r"> \*\*后置概念\*\*", content))


def has_cross_ref_to_layer(content: str, target_layer: str) -> bool:
    """检查内容中是否有指向目标层级的链接"""
    # 从路径推断层级
    for match in re.finditer(r"\[([^\]]+)\]\(([^)]+\.md)\)", content):
        ref = match.group(2)
        for part in Path(ref).parts:
            if part.startswith("0") and len(part) >= 2 and part[1].isdigit():
                ref_layer = f"L{part[1]}"
                if ref_layer == target_layer:
                    return True
    return False


def fix_file(file_info: dict) -> tuple:
    """修复单个文件，返回 (添加了后置概念, 添加了跨层引用)"""
    filepath = Path(file_info["path"])
    content = filepath.read_text(encoding="utf-8")
    layer = file_info["layer"]
    changed = False
    added_post = False
    added_ref = False

    # 1. 添加后置概念
    if not has_post_concept(content) and layer in LAYER_DEFAULT_POST:
        insert_pos = find_insertion_point(content)
        section = f"> **后置概念**: {LAYER_DEFAULT_POST[layer]}\n\n"
        content = content[:insert_pos] + section + content[insert_pos:]
        added_post = True
        changed = True

    # 2. 添加跨层引用（向下引用）
    current_num = LAYER_ORDER.get(layer, -1)
    if current_num > 0:
        expected_lower = f"L{current_num - 1}"
        if not has_cross_ref_to_layer(content, expected_lower):
            insert_pos = find_insertion_point(content)
            if expected_lower in LAYER_DEFAULT_LOWER:
                section = f"> **前置依赖**: {LAYER_DEFAULT_LOWER[expected_lower]}\n\n"
                content = content[:insert_pos] + section + content[insert_pos:]
                added_ref = True
                changed = True

    if changed:
        filepath.write_text(content, encoding="utf-8")

    return added_post, added_ref


def main():
    total_post = 0
    total_ref = 0
    total_files = 0

    for file_info in KB["files"]:
        layer = file_info["layer"]
        if layer not in LAYER_ORDER:
            continue
        # 只处理 L1-L7
        if layer == "L0":
            continue

        added_post, added_ref = fix_file(file_info)
        if added_post or added_ref:
            total_files += 1
            if added_post:
                total_post += 1
            if added_ref:
                total_ref += 1
            print(f"  {'✅' if added_post else '  '} {'✅' if added_ref else '  '} {file_info['path']}")

    print(f"\n总计: 修复了 {total_files} 个文件")
    print(f"  - 添加后置概念: {total_post}")
    print(f"  - 添加跨层引用: {total_ref}")


if __name__ == "__main__":
    main()
