#!/usr/bin/env python3
"""
自动为缺少前置/后置概念的文件补充关联链接。
基于文件名关键词和层级推断前置/后置概念。
"""

import re
from pathlib import Path
from collections import defaultdict

CONCEPT_DIR = Path('concept')
LEVEL_DIRS = {
    '00_meta': 'L0', '01_foundation': 'L1', '02_intermediate': 'L2',
    '03_advanced': 'L3', '04_formal': 'L4', '05_comparative': 'L5',
    '06_ecosystem': 'L6', '07_future': 'L7'
}

# 层级内主题簇映射（用于推断同层关联）
TOPIC_CLUSTERS = {
    'L1': {
        'ownership': ['01_ownership.md'],
        'borrowing': ['02_borrowing.md'],
        'lifetime': ['03_lifetimes.md', '03_lifetimes_advanced.md'],
        'type': ['04_type_system.md', '04_type_system_advanced.md', '05_never_type.md', '05_reference_semantics.md'],
        'control': ['07_control_flow.md'],
        'collection': ['08_collections.md'],
        'string': ['09_strings_and_text.md'],
        'error': ['10_error_handling_basics.md'],
        'module': ['11_modules_and_paths.md'],
        'macro': ['12_attributes_and_macros.md'],
        'panic': ['13_panic_and_abort.md'],
        'closure': ['15_closure_basics.md'],
    },
    'L2': {
        'trait': ['01_traits.md'],
        'generic': ['02_generics.md'],
        'memory': ['03_memory_management.md', '12_smart_pointers.md', '08_interior_mutability.md'],
        'error': ['04_error_handling.md', '05_assert_matches.md'],
        'pattern': ['06_pattern_matching.md', '07_closure_types.md'],
        'serde': ['09_serde_patterns.md'],
        'cow': ['11_cow_and_borrowed.md'],
        'dsl': ['13_dsl_and_embedding.md'],
    },
    'L3': {
        'concurrency': ['01_concurrency.md', '11_atomics_and_memory_ordering.md'],
        'async': ['02_async.md', '02_async_advanced.md', '02_async_programming.md', '13_async_patterns.md'],
        'unsafe': ['03_unsafe_rust.md'],
        'macro': ['05_macros.md'],
        'pin': ['06_pin_unpin.md'],
        'ffi': ['05_rust_ffi.md'],
    },
    'L4': {
        'linear': ['01_linear_logic.md', '09_linear_logic_applications.md'],
        'type': ['02_type_theory.md', '06_subtype_variance.md', '08_type_inference.md', '21_type_semantics.md'],
        'ownership': ['03_ownership_formal.md'],
        'rustbelt': ['04_rustbelt.md'],
        'verification': ['05_verification_toolchain.md', '22_modern_verification_tools.md'],
        'separation': ['07_separation_logic.md', '11_separation_logic.md'],
        'semantics': ['09_operational_semantics.md', '17_operational_semantics.md', '18_evaluation_strategies.md', '20_axiomatic_semantics.md', '23_programming_language_foundations.md'],
        'category': ['10_category_theory.md'],
        'lambda': ['14_lambda_calculus.md'],
        'hoare': ['15_hoare_logic.md'],
        'aerospace': ['16_aerospace_certification_formal_methods.md'],
    },
}

# 层级间前置映射：每个层级的默认前置来源
LEVEL_PRECEDENTS = {
    'L1': ['[PL Prerequisites](./00_pl_prerequisites.md)'],
    'L2': ['[Ownership](../01_foundation/01_ownership.md)', '[Type System](../01_foundation/04_type_system.md)'],
    'L3': ['[Traits](../02_intermediate/01_traits.md)', '[Generics](../02_intermediate/02_generics.md)', '[Error Handling](../02_intermediate/04_error_handling.md)'],
    'L4': ['[Type System](../../01_foundation/04_type_system.md)', '[Unsafe](../../03_advanced/03_unsafe_rust.md)'],
    'L5': ['[Type System](../../01_foundation/04_type_system.md)', '[Concurrency](../../03_advanced/01_concurrency.md)'],
    'L6': ['[Traits](../../02_intermediate/01_traits.md)', '[Async](../../03_advanced/02_async.md)'],
    'L7': ['[Type System](../../01_foundation/04_type_system.md)', '[Effects System](./04_effects_system.md)'],
}

# 层级间后置映射：每个层级的默认后置目标
LEVEL_SUCCESSORS = {
    'L1': ['[Traits](../../02_intermediate/01_traits.md)', '[Generics](../../02_intermediate/02_generics.md)'],
    'L2': ['[Concurrency](../../03_advanced/01_concurrency.md)', '[Async](../../03_advanced/02_async.md)'],
    'L3': ['[Linear Logic](../../04_formal/01_linear_logic.md)', '[RustBelt](../../04_formal/04_rustbelt.md)'],
    'L4': ['[Comparative Analysis](../../05_comparative/)'],
    'L5': ['[Ecosystem](../../06_ecosystem/)'],
    'L6': ['[Future Trends](../../07_future/)'],
    'L7': [],
}


def get_level(filepath: Path) -> str:
    rel = filepath.relative_to(CONCEPT_DIR)
    top = rel.parts[0] if rel.parts else ''
    return LEVEL_DIRS.get(top, 'Other')


def extract_keywords(filename: str) -> list:
    """从文件名提取关键词"""
    name = filename.lower().replace('.md', '').replace('_', ' ')
    # 提取有意义的词
    words = re.findall(r'[a-z]+', name)
    # 过滤常见词
    stopwords = {'and', 'the', 'in', 'of', 'to', 'a', 'an', 'for', 'with', 'on', 'at', 'from'}
    return [w for w in words if w not in stopwords and len(w) > 2]


def infer_pre_concepts(filepath: Path, level: str) -> str:
    """推断前置概念"""
    fname = filepath.name
    keywords = extract_keywords(fname)
    
    # L0 不需要前置概念
    if level == 'L0':
        return ''
    
    # 尝试基于关键词匹配同层主题簇
    if level in TOPIC_CLUSTERS:
        for topic, files in TOPIC_CLUSTERS[level].items():
            if any(topic in kw for kw in keywords):
                # 找到相关主题，前置为同主题的更早文件
                try:
                    idx = files.index(fname)
                    if idx > 0:
                        pre_file = files[idx - 1]
                        return f'[{pre_file.replace(".md", "").replace("_", " ").title()}](./{pre_file})'
                except ValueError:
                    pass
    
    # 默认使用层级前置
    precedents = LEVEL_PRECEDENTS.get(level, [])
    if precedents:
        return ' · '.join(precedents[:2])  # 最多 2 个
    return ''


def infer_post_concepts(filepath: Path, level: str) -> str:
    """推断后置概念"""
    fname = filepath.name
    keywords = extract_keywords(fname)
    
    # L7 不需要后置概念
    if level == 'L7' or level == 'L0':
        return ''
    
    # 尝试基于关键词匹配同层主题簇
    if level in TOPIC_CLUSTERS:
        for topic, files in TOPIC_CLUSTERS[level].items():
            if any(topic in kw for kw in keywords):
                try:
                    idx = files.index(fname)
                    if idx < len(files) - 1:
                        post_file = files[idx + 1]
                        return f'[{post_file.replace(".md", "").replace("_", " ").title()}](./{post_file})'
                except ValueError:
                    pass
    
    # 默认使用层级后置
    successors = LEVEL_SUCCESSORS.get(level, [])
    if successors:
        return ' · '.join(successors[:2])
    return ''


def add_concept_links(filepath: Path, level: str) -> bool:
    """为文件添加前置/后置概念链接"""
    with open(filepath, 'r', encoding='utf-8') as f:
        content = f.read()
    
    # 检查前 500 字符是否已有前置/后置
    header = content[:500]
    has_pre = '前置概念' in header
    has_post = '后置概念' in header
    
    if has_pre and has_post:
        return False  # 无需修改
    
    # 推断前置/后置
    pre = infer_pre_concepts(filepath, level) if not has_pre else ''
    post = infer_post_concepts(filepath, level) if not has_post else ''
    
    if not pre and not post:
        return False
    
    # 构建插入文本
    links = []
    if pre and not has_pre:
        links.append(f'> **前置概念**: {pre}')
    if post and not has_post:
        links.append(f'> **后置概念**: {post}')
    
    insert_text = '\n'.join(links) + '\n'
    
    # 找到插入位置：在标题之后、第一个 ## 之前
    lines = content.split('\n')
    insert_idx = 0
    for i, line in enumerate(lines):
        if line.startswith('# ') and i > 0:
            insert_idx = i + 1
            break
    
    # 在插入位置后添加
    new_lines = lines[:insert_idx] + [''] + insert_text.split('\n') + lines[insert_idx:]
    new_content = '\n'.join(new_lines)
    
    with open(filepath, 'w', encoding='utf-8') as f:
        f.write(new_content)
    
    return True


def main():
    modified = 0
    skipped = 0
    
    for filepath in sorted(CONCEPT_DIR.rglob('*.md')):
        level = get_level(filepath)
        if level == 'L0':
            skipped += 1
            continue
        
        if add_concept_links(filepath, level):
            modified += 1
            print(f'  + {filepath.relative_to(CONCEPT_DIR)}')
        else:
            skipped += 1
    
    print(f'\n总计: {modified + skipped} 个文件')
    print(f'  新增关联链接: {modified}')
    print(f'  跳过 (已有或无需): {skipped}')


if __name__ == '__main__':
    main()
