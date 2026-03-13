#!/usr/bin/env python3
"""
修复 Rust 代码中的复杂类型警告
"""

import os
import re
import subprocess

# 定义需要修复的文件和对应的类型别名
FILES_TO_FIX = {
    "crates/c04_generic/src/natural_transformation/mod.rs": {
        "aliases": [
            "type TransformationFn<A, B> = fn(A) -> B;",
            "type LinkedList<T> = std::collections::LinkedList<T>;",
        ],
        "replacements": [
            ("std::collections::LinkedList", "LinkedList"),
        ]
    },
    "crates/c04_generic/src/polymorphism/generic_trait.rs": {
        "aliases": [
            "type PredicateFn<T> = Box<dyn Fn(&T) -> bool + Send + Sync>;",
        ],
        "replacements": []
    },
    "crates/c04_generic/src/polymorphism/trait_object.rs": {
        "aliases": [
            "type SharedHashMap<K, V> = Arc<Mutex<HashMap<K, V>>>;",
            "type PluginVec = Vec<Box<dyn Plugin>>;",
            "type DrawableVec = Vec<Box<dyn Drawable>>;",
            "type ProcessorVec = Vec<Box<dyn Processor>>;",
        ],
        "replacements": [
            ("Arc<Mutex<HashMap<String, String>>>", "SharedHashMap<String, String>"),
        ]
    },
    "crates/c04_generic/src/trait_bound/drop.rs": {
        "aliases": [
            "type ByteVec = Vec<u8>;",
            "type StaticMutexGuard = Option<MutexGuard<'static, ()>>;",
        ],
        "replacements": [
            ("Option<MutexGuard<'static, ()>>", "StaticMutexGuard"),
        ]
    },
    "crates/c04_generic/src/trait_bound/send.rs": {
        "aliases": [
            "type AtomicUsize = std::sync::atomic::AtomicUsize;",
            "type AtomicBool = std::sync::atomic::AtomicBool;",
            "type ByteVec = Vec<u8>;",
        ],
        "replacements": []
    },
    "crates/c04_generic/src/trait_bound/sync.rs": {
        "aliases": [
            "type AtomicUsize = std::sync::atomic::AtomicUsize;",
            "type AtomicBool = std::sync::atomic::AtomicBool;",
            "type ByteVec = Vec<u8>;",
        ],
        "replacements": []
    },
    "crates/c04_generic/src/trait_bound/from_into.rs": {
        "aliases": [
            "type StringVec = Vec<String>;",
            "type ByteVec = Vec<u8>;",
        ],
        "replacements": []
    },
    "crates/c04_generic/src/trait_bound/hash.rs": {
        "aliases": [
            "type StringVec = Vec<String>;",
        ],
        "replacements": []
    },
    "crates/c04_generic/src/trait_bound/order.rs": {
        "aliases": [
            "type StringVec = Vec<String>;",
            "type PersonVec = Vec<Person>;",
        ],
        "replacements": []
    },
    "crates/c04_generic/src/trait_bound/partial_eq.rs": {
        "aliases": [
            "type FloatVec = Vec<f64>;",
        ],
        "replacements": []
    },
    "crates/c04_generic/src/trait_bound/partial_order.rs": {
        "aliases": [
            "type FloatVec = Vec<f64>;",
        ],
        "replacements": []
    },
    "crates/c04_generic/src/type_constructor/mod.rs": {
        "aliases": [
            "type LinkedList<T> = std::collections::LinkedList<T>;",
        ],
        "replacements": []
    },
    "crates/c04_generic/src/type_inference/mod.rs": {
        "aliases": [
            "type IntVec = Vec<i32>;",
            "type StringVec = Vec<String>;",
        ],
        "replacements": []
    },
}

def add_type_aliases(file_path, config):
    """为文件添加类型别名"""
    if not os.path.exists(file_path):
        print(f"文件不存在: {file_path}")
        return False
    
    with open(file_path, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 检查是否已经有类型别名
    if "type " in content and any(alias in content for alias in config["aliases"]):
        print(f"文件已包含类型别名: {file_path}")
        return False
    
    # 找到文档注释结束的位置
    doc_end = content.find("*/")
    if doc_end == -1:
        # 没有文档注释，在文件开头添加 use 语句之后
        lines = content.split('\n')
        use_idx = 0
        for i, line in enumerate(lines):
            if line.startswith('use '):
                use_idx = i + 1
        
        # 在 use 语句后添加类型别名
        aliases_text = '\n'.join([''] + config["aliases"] + [''])
        lines.insert(use_idx, aliases_text)
        new_content = '\n'.join(lines)
    else:
        # 在文档注释后添加类型别名
        insert_pos = doc_end + 2
        aliases_text = '\n\n' + '\n'.join(config["aliases"]) + '\n'
        new_content = content[:insert_pos] + aliases_text + content[insert_pos:]
    
    with open(file_path, 'w', encoding='utf-8') as f:
        f.write(new_content)
    
    print(f"已添加类型别名: {file_path}")
    return True

def main():
    """主函数"""
    fixed_count = 0
    
    for file_path, config in FILES_TO_FIX.items():
        full_path = os.path.join("e:\\_src\\rust-lang", file_path)
        if add_type_aliases(full_path, config):
            fixed_count += 1
    
    print(f"\n总共修复了 {fixed_count} 个文件")

if __name__ == "__main__":
    main()
