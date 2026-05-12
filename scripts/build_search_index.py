#!/usr/bin/env python3
"""基于 concept_kb.json 构建概念搜索索引"""

import json, re, os
from collections import defaultdict

def load_kb():
    with open('concept_kb.json', 'r', encoding='utf-8') as f:
        return json.load(f)

def extract_concepts(text):
    """从文本中提取潜在概念（Rust 关键字、类型、trait 等）"""
    # Rust 关键字和常见概念
    concepts = set()
    
    # 匹配 `Type` 或 `trait_name`
    for m in re.finditer(r'`([^`]+)`', text):
        concept = m.group(1).strip()
        if len(concept) > 2 and not concept.startswith('http'):
            concepts.add(concept)
    
    # 匹配 CamelCase（类型/Trait）
    for m in re.finditer(r'\b([A-Z][a-zA-Z0-9_]{2,})\b', text):
        concepts.add(m.group(1))
    
    # 匹配 snake_case（函数/变量）中的常见模式
    rust_concepts = {
        'ownership', 'borrowing', 'lifetime', 'trait', 'generic', 'macro',
        'async', 'await', 'future', 'pin', 'unsafe', 'ffi', 'drop', 'clone',
        'copy', 'send', 'sync', 'mutex', 'rwlock', 'arc', 'rc', 'box',
        'refcell', 'cell', 'option', 'result', 'panic', 'enum', 'struct',
        'impl', 'dyn', 'static', 'const', 'mut', 'let', 'match', 'if let',
        'while let', 'for', 'loop', 'break', 'continue', 'return', 'move',
        'where', 'self', 'super', 'crate', 'mod', 'use', 'pub', 'priv',
        'type', 'fn', 'struct', 'union', 'impl', 'trait', 'auto trait',
        'negative impl', 'specialization', 'gat', 'hrtb', 'const generics',
        'type alias impl trait', 'never type', 'impl trait', 'dyn trait',
        'mermaid', 'polonius', 'tree borrows', 'stacked borrows',
        'rustbelt', 'iris', 'oxide', 'miri', 'kani', 'aeneas', 'creusot',
        'verus', 'prusti', 'refinedrust', 'linear logic', 'separation logic',
        'affine logic', 'system f', 'hindley-milner', 'parametricity',
        'region types', 'non-lexical lifetimes', 'edition',
    }
    
    text_lower = text.lower()
    for concept in rust_concepts:
        if concept in text_lower:
            concepts.add(concept)
    
    return concepts

def build_index():
    kb = load_kb()
    index = defaultdict(lambda: defaultdict(float))
    
    for file_info in kb['files']:
        path = file_info['path']
        layer = file_info['layer']
        title = file_info.get('title', '')
        positioning = file_info.get('positioning', '')
        
        # 从标题提取概念（高权重）
        for concept in extract_concepts(title):
            index[concept][path] += 10.0
        
        # 从定位提取概念（高权重）
        for concept in extract_concepts(positioning):
            index[concept][path] += 8.0
        
        # 从定理链提取概念（中权重）
        for chain in file_info.get('theorem_chains', []):
            text = chain.get('text', '')
            for concept in extract_concepts(text):
                index[concept][path] += 5.0
        
        # 从反命题提取概念（中权重）
        for anti in file_info.get('anti_propositions', []):
            text = anti.get('title', '')
            for concept in extract_concepts(text):
                index[concept][path] += 4.0
        
        # 从代码块提取概念（低权重）
        for block in file_info.get('code_blocks', []):
            text = block.get('code', '')
            for concept in extract_concepts(text):
                index[concept][path] += 2.0
        
        # 层级加权
        layer_boost = {'L1': 1.2, 'L2': 1.1, 'L3': 1.0, 'L4': 1.0, 'L5': 0.9, 'L6': 0.8, 'L7': 0.8, 'L0': 0.5}
        boost = layer_boost.get(layer, 1.0)
        for concept in list(index.keys()):
            if path in index[concept]:
                index[concept][path] *= boost
    
    # 转换为可序列化的格式
    result = {}
    for concept, files in index.items():
        sorted_files = sorted(files.items(), key=lambda x: -x[1])
        result[concept] = [{'path': p, 'score': round(s, 1)} for p, s in sorted_files[:10]]
    
    return result

def main():
    index = build_index()
    output = {
        'meta': {
            'total_concepts': len(index),
            'generated_from': 'concept_kb.json',
            'version': '1.0'
        },
        'index': index
    }
    
    with open('concept_search_index.json', 'w', encoding='utf-8') as f:
        json.dump(output, f, ensure_ascii=False, indent=2)
    
    print(f'Generated concept_search_index.json with {len(index)} concepts')
    
    # 打印 top 20 概念
    top_concepts = sorted(index.keys(), key=lambda c: sum(f['score'] for f in index[c]), reverse=True)[:20]
    print('\nTop 20 concepts:')
    for concept in top_concepts:
        files = index[concept]
        print(f'  {concept}: {len(files)} files, top={files[0]["path"]} ({files[0]["score"]})')

if __name__ == '__main__':
    main()
