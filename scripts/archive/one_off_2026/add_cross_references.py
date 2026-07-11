#!/usr/bin/env python3
"""在 concept ↔ knowledge 重叠主题文件顶部添加交叉引用导航块"""
import os
from pathlib import Path

# 核心重叠主题映射: (concept_path, knowledge_path, display_name)
CROSS_REFS = [
    # L1 基础层
    ("concept/01_foundation/01_ownership.md", "knowledge/01_fundamentals/04_ownership.md", "所有权"),
    ("concept/01_foundation/02_borrowing.md", "knowledge/01_fundamentals/01_borrowing.md", "借用"),
    ("concept/01_foundation/03_lifetimes.md", "knowledge/01_fundamentals/03_lifetimes.md", "生命周期"),
    ("concept/01_foundation/04_type_system.md", "knowledge/02_intermediate/type_system/", "类型系统"),
    ("concept/01_foundation/08_collections.md", "knowledge/02_intermediate/01_collections.md", "集合"),
    ("concept/01_foundation/09_strings_and_text.md", "knowledge/02_intermediate/05_strings.md", "字符串与文本"),
    ("concept/01_foundation/10_error_handling_basics.md", "knowledge/02_intermediate/02_error_handling.md", "错误处理基础"),
    ("concept/01_foundation/11_modules_and_paths.md", "knowledge/02_intermediate/10_module_system.md", "模块系统"),
    ("concept/01_foundation/12_attributes_and_macros.md", "knowledge/03_advanced/macros/", "属性与宏"),
    ("concept/01_foundation/15_closure_basics.md", "knowledge/02_intermediate/", "闭包"),  # 无精确对应
    # L2 进阶层
    ("concept/02_intermediate/01_traits.md", "knowledge/02_intermediate/06_traits.md", "Trait"),
    ("concept/02_intermediate/02_generics.md", "knowledge/02_intermediate/03_generics.md", "泛型"),
    ("concept/02_intermediate/04_error_handling.md", "knowledge/02_intermediate/02_error_handling.md", "错误处理"),
    ("concept/02_intermediate/12_smart_pointers.md", "knowledge/02_intermediate/04_smart_pointers.md", "智能指针"),
    ("concept/02_intermediate/17_macro_patterns.md", "knowledge/03_advanced/macros/", "宏模式"),
    ("concept/02_intermediate/15_iterator_patterns.md", "knowledge/01_fundamentals/02_iterators.md", "迭代器"),
    # L3 高级层
    ("concept/03_advanced/01_concurrency.md", "knowledge/03_advanced/concurrency/", "并发"),
    ("concept/03_advanced/02_async.md", "knowledge/03_advanced/async/", "异步编程"),
    ("concept/03_advanced/02_async_programming.md", "knowledge/03_advanced/async/", "异步编程"),
    ("concept/03_advanced/03_unsafe.md", "knowledge/03_advanced/unsafe/", "Unsafe Rust"),
    ("concept/03_advanced/03_unsafe_rust.md", "knowledge/03_advanced/unsafe/", "Unsafe Rust"),
    ("concept/03_advanced/04_macros.md", "knowledge/03_advanced/macros/", "宏系统"),
    ("concept/03_advanced/05_macros.md", "knowledge/03_advanced/macros/", "宏系统"),
    ("concept/03_advanced/05_rust_ffi.md", "knowledge/03_advanced/02_ffi.md", "FFI"),
    ("concept/03_advanced/07_proc_macro.md", "knowledge/03_advanced/macros/02_procedural.md", "过程宏"),
    ("concept/03_advanced/11_atomics_and_memory_ordering.md", "knowledge/03_advanced/concurrency/01_atomics.md", "原子操作"),
    ("concept/03_advanced/06_pin_unpin.md", "knowledge/03_advanced/async/", "Pin/Unpin"),  # 无精确对应
    # 性能与优化
    ("concept/06_ecosystem/15_performance_optimization.md", "knowledge/03_advanced/05_performance_optimization.md", "性能优化"),
    # 生态
    ("concept/06_ecosystem/23_database_systems.md", "knowledge/06_ecosystem/databases/", "数据库"),
    ("concept/06_ecosystem/27_web_frameworks.md", "content/ecosystem/deep_dives/01_axum_deep_dive.md", "Web 框架"),
]

def rel_path(from_file, to_file):
    """计算从 from_file 到 to_file 的相对路径"""
    from_dir = Path(from_file).parent
    to = Path(to_file)
    try:
        return os.path.relpath(to, from_dir).replace("\\", "/")
    except ValueError:
        # Windows 不同盘符的情况
        return to_file

def add_cross_ref_to_file(filepath, ref_path, ref_label, direction):
    """在文件顶部添加交叉引用块"""
    if not os.path.exists(filepath):
        return False
    
    content = Path(filepath).read_text(encoding='utf-8')
    
    # 检查是否已有交叉引用块
    if '**📎 交叉引用**' in content or '**交叉引用**' in content:
        return False
    
    # 找到第一个标题之后的位置，或文件开头
    lines = content.split('\n')
    
    # 查找第一个非空行/标题后的位置
    insert_idx = 0
    for i, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith('#'):
            # 找到第一个标题，在其后插入（如果下一行是空行则再后一行）
            insert_idx = i + 1
            if insert_idx < len(lines) and lines[insert_idx].strip() == '':
                insert_idx += 1
            break
        elif stripped == '---':
            # front matter，跳过
            insert_idx = i + 1
    
    if direction == 'concept_to_knowledge':
        block = f"> **📎 交叉引用**\n>\n> 本主题在 knowledge 中有系统化的知识索引：[{ref_label}]({ref_path})\n"
    else:
        block = f"> **📎 交叉引用**\n>\n> 本主题在 concept 中有深度的概念分析：[{ref_label}]({ref_path})\n"
    
    lines.insert(insert_idx, block)
    new_content = '\n'.join(lines)
    
    if new_content != content:
        Path(filepath).write_text(new_content, encoding='utf-8')
        return True
    return False

def resolve_dir(path):
    """如果 path 是目录，尝试找到其中的入口文件"""
    if os.path.isdir(path):
        for entry in ['README.md', 'INDEX.md', '01.md']:
            p = os.path.join(path, entry)
            if os.path.isfile(p):
                return p
        # 找到第一个 .md 文件
        for f in sorted(os.listdir(path)):
            if f.endswith('.md'):
                return os.path.join(path, f)
        return None
    return path

def main():
    modified = []
    
    for concept_path, knowledge_path, label in CROSS_REFS:
        concept_file = resolve_dir(concept_path)
        knowledge_file = resolve_dir(knowledge_path)
        
        # concept → knowledge
        if concept_file and os.path.exists(concept_file):
            ref = rel_path(concept_file, knowledge_path)
            if add_cross_ref_to_file(concept_file, ref, label, 'concept_to_knowledge'):
                modified.append(concept_file)
        
        # knowledge → concept
        if knowledge_file and os.path.exists(knowledge_file):
            ref = rel_path(knowledge_file, concept_path)
            if add_cross_ref_to_file(knowledge_file, ref, label, 'knowledge_to_concept'):
                modified.append(knowledge_file)
    
    print(f"Added cross-references to {len(modified)} files:")
    for f in modified:
        print(f"  {f}")

if __name__ == '__main__':
    main()
