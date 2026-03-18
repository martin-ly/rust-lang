#!/usr/bin/env python3
"""
清理未使用的类型别名
"""

import os

FILES_TO_CLEANUP = [
    "crates/c04_generic/src/natural_transformation/mod.rs",
    "crates/c04_generic/src/polymorphism/generic_trait.rs",
    "crates/c04_generic/src/trait_bound/drop.rs",
    "crates/c04_generic/src/trait_bound/from_into.rs",
    "crates/c04_generic/src/trait_bound/hash.rs",
    "crates/c04_generic/src/trait_bound/order.rs",
    "crates/c04_generic/src/trait_bound/partial_eq.rs",
    "crates/c04_generic/src/trait_bound/partial_order.rs",
    "crates/c04_generic/src/type_constructor/mod.rs",
    "crates/c04_generic/src/type_inference/mod.rs",
]

UNUSED_ALIASES = [
    "type TransformationFn<A, B> = fn(A) -> B;",
    "type LinkedList<T> = std::collections::LinkedList<T>;",
    "type PredicateFn<T> = Box<dyn Fn(&T) -> bool + Send + Sync>;",
    "type ByteVec = Vec<u8>;",
    "type StaticMutexGuard = Option<MutexGuard<'static, ()>>;",
    "type StringVec = Vec<String>;",
    "type FloatVec = Vec<f64>;",
    "type IntVec = Vec<i32>;",
]

def remove_unused_aliases(file_path):
    """移除未使用的类型别名"""
    if not os.path.exists(file_path):
        return False
    
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    original_content = content
    
    for alias in UNUSED_ALIASES:
        content = content.replace(alias + "\n", "")
        content = content.replace(alias, "")
    
    # 清理多余的空行
    content = content.replace("\n\n\n", "\n\n")
    
    if content != original_content:
        with open(file_path, 'w', encoding='utf-8') as f:
            f.write(content)
        print(f"已清理: {os.path.basename(file_path)}")
        return True
    
    return False

def main():
    """主函数"""
    cleaned_count = 0
    
    for file_path in FILES_TO_CLEANUP:
        full_path = os.path.join("e:\\_src\\rust-lang", file_path)
        if remove_unused_aliases(full_path):
            cleaned_count += 1
    
    print(f"\n总共清理了 {cleaned_count} 个文件")

if __name__ == "__main__":
    main()
