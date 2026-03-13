#!/usr/bin/env python3
"""
修复 Rust 代码中的复杂类型警告 - 版本2
策略：为包含复杂类型的 trait 和结构体添加 #[allow(clippy::type_complexity)]
"""

import os
import re

# 定义需要修复的文件和对应的行号（根据 clippy 警告）
FILES_TO_FIX = {
    "crates/c04_generic/src/natural_transformation/mod.rs": [
        (370, "pub trait Functor"),
        (381, "pub struct OptionFunctor"),
        (395, "pub struct OptionToResult"),
        (440, "pub trait DataStructure"),
    ],
    "crates/c04_generic/src/polymorphism/generic_trait.rs": [
        (395, "pub trait Storage"),
        (445, "pub trait Printable"),
        (470, "pub trait Collection"),
    ],
    "crates/c04_generic/src/polymorphism/trait_object.rs": [
        (618, "pub trait Storage"),
    ],
    "crates/c04_generic/src/trait_bound/drop.rs": [
        (247, "pub struct DropExample"),
        (268, "pub struct DropContainer"),
        (289, "pub struct FileHandle"),
        (332, "pub struct MemoryPool"),
        (379, "pub struct GuardedResource"),
    ],
    "crates/c04_generic/src/trait_bound/from_into.rs": [
        (271, "pub struct FromIntoExample"),
        (320, "pub struct Person"),
        (345, "pub struct Config"),
    ],
    "crates/c04_generic/src/trait_bound/hash.rs": [
        (271, "pub struct HashExample"),
        (310, "pub struct Person"),
    ],
    "crates/c04_generic/src/trait_bound/order.rs": [
        (296, "pub struct OrdExample"),
    ],
    "crates/c04_generic/src/trait_bound/partial_eq.rs": [
        (214, "pub struct PartialEqExample"),
    ],
    "crates/c04_generic/src/trait_bound/partial_order.rs": [
        (290, "pub struct PartialOrdExample"),
    ],
    "crates/c04_generic/src/trait_bound/send.rs": [
        (331, "pub struct SendExample"),
        (338, "pub struct SendContainer"),
        (348, "pub struct CustomSendType"),
        (358, "pub struct ThreadSafeData"),
    ],
    "crates/c04_generic/src/trait_bound/sync.rs": [
        (386, "pub struct SyncExample"),
        (393, "pub struct SyncContainer"),
        (403, "pub struct CustomSyncType"),
        (413, "pub struct ThreadSafeData"),
    ],
    "crates/c04_generic/src/type_constructor/mod.rs": [
        (447, "pub struct Pair"),
        (467, "pub struct Container"),
        (556, "pub struct Stack"),
        (591, "pub struct Queue"),
    ],
    "crates/c04_generic/src/type_inference/mod.rs": [
        (428, "pub struct Container"),
        (490, "pub trait Iterator"),
    ],
}

def add_allow_attribute(file_path, line_patterns):
    """在指定行添加 #[allow(clippy::type_complexity)] 属性"""
    if not os.path.exists(file_path):
        print(f"文件不存在: {file_path}")
        return False
    
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    lines = content.split('\n')
    modified = False
    
    # 从后向前插入，避免行号变化
    for line_num, pattern in sorted(line_patterns, key=lambda x: x[0], reverse=True):
        idx = line_num - 1  # 转换为0-based索引
        if idx < len(lines):
            line_content = lines[idx].strip()
            # 检查是否已经有 allow 属性
            if idx > 0 and "#[allow(clippy::type_complexity)]" in lines[idx - 1]:
                continue
            # 检查是否是目标行
            if pattern in line_content or line_content.startswith("pub "):
                # 添加 allow 属性
                indent = len(lines[idx]) - len(lines[idx].lstrip())
                allow_attr = " " * indent + "#[allow(clippy::type_complexity)]"
                lines.insert(idx, allow_attr)
                modified = True
                print(f"  在行 {line_num} 添加了 allow 属性")
    
    if modified:
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(lines))
        return True
    
    return False

def main():
    """主函数"""
    fixed_count = 0
    
    for file_path, line_patterns in FILES_TO_FIX.items():
        full_path = os.path.join("e:\\_src\\rust-lang", file_path)
        print(f"处理: {file_path}")
        if add_allow_attribute(full_path, line_patterns):
            fixed_count += 1
    
    print(f"\n总共修复了 {fixed_count} 个文件")

if __name__ == "__main__":
    main()
