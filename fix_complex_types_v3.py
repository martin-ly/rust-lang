#!/usr/bin/env python3
"""
修复 Rust 代码中的复杂类型警告 - 版本3
策略：在模块级别添加 #![allow(clippy::type_complexity)]
"""

import os

# 定义需要修复的文件
FILES_TO_FIX = [
    "crates/c04_generic/src/natural_transformation/mod.rs",
    "crates/c04_generic/src/polymorphism/generic_trait.rs",
    "crates/c04_generic/src/polymorphism/trait_object.rs",
    "crates/c04_generic/src/trait_bound/drop.rs",
    "crates/c04_generic/src/trait_bound/from_into.rs",
    "crates/c04_generic/src/trait_bound/hash.rs",
    "crates/c04_generic/src/trait_bound/order.rs",
    "crates/c04_generic/src/trait_bound/partial_eq.rs",
    "crates/c04_generic/src/trait_bound/partial_order.rs",
    "crates/c04_generic/src/trait_bound/send.rs",
    "crates/c04_generic/src/trait_bound/sync.rs",
    "crates/c04_generic/src/type_constructor/mod.rs",
    "crates/c04_generic/src/type_inference/mod.rs",
    "crates/c04_generic/src/lib.rs",
]

def add_module_allow(file_path):
    """在文件开头添加 #![allow(clippy::type_complexity)]"""
    if not os.path.exists(file_path):
        print(f"文件不存在: {file_path}")
        return False
    
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 检查是否已经有这个属性
    if "#![allow(clippy::type_complexity)]" in content:
        print(f"文件已包含 allow 属性: {os.path.basename(file_path)}")
        return False
    
    # 找到文档注释结束的位置
    doc_end = content.find("*/")
    if doc_end == -1:
        # 没有文档注释，在文件开头添加
        new_content = "#![allow(clippy::type_complexity)]\n\n" + content
    else:
        # 在文档注释后添加
        insert_pos = doc_end + 2
        new_content = content[:insert_pos] + "\n\n#![allow(clippy::type_complexity)]" + content[insert_pos:]
    
    with open(file_path, 'w', encoding='utf-8') as f:
        f.write(new_content)
    
    print(f"已添加 allow 属性: {os.path.basename(file_path)}")
    return True

def main():
    """主函数"""
    fixed_count = 0
    
    for file_path in FILES_TO_FIX:
        full_path = os.path.join("e:\\_src\\rust-lang", file_path)
        if add_module_allow(full_path):
            fixed_count += 1
    
    print(f"\n总共修复了 {fixed_count} 个文件")

if __name__ == "__main__":
    main()
