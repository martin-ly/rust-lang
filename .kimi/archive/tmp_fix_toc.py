#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""修复 9 个目标文件的目录（TOC）中因批量替换产生的混乱条目。"""

from pathlib import Path

BASE = Path('e:/_src/rust-lang/docs/research_notes')

FILES = {
    '10_rust_193_feature_matrix.md': {
        'old_block': '''  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)
    - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#本文档的rust-194更新要点)''',
        'new_block': '''  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)''',
    },
    '10_rust_193_language_features_comprehensive_analysis.md': {
        'old_block': '''  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)
    - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#本文档的rust-194更新要点)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#最后更新-2026-03-14-rust-194-深度整合)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)
    - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#本文档的rust-194更新要点)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#最后更新-2026-03-14-rust-194-深度整合)''',
        'new_block': '''  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)''',
    },
    '10_rust_194_195_feature_matrix.md': {
        'old_block': '''- [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#rust-194195-特性矩阵与形式化追踪)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)
    - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#本文档的rust-194更新要点)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#最后更新-2026-03-14-rust-194-深度整合)''',
        'new_block': '''- [Rust 1.94/1.95 特性矩阵与形式化追踪](#rust-194195-特性矩阵与形式化追踪)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)''',
    },
    '10_rust_194_comprehensive_analysis.md': {
        'old_block': '''  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)
    - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#本文档的rust-194更新要点)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#最后更新-2026-03-14-rust-194-深度整合)''',
        'new_block': '''  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)''',
    },
    '10_rust_194_deep_semantic_analysis.md': {
        'old_block': '''- [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#rust-194-深度语义分析)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)
    - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#本文档的rust-194更新要点)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#最后更新-2026-03-14-rust-194-深度整合)''',
        'new_block': '''- [Rust 1.94 深度语义分析](#rust-194-深度语义分析)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)''',
    },
    '10_rust_194_mind_representations.md': {
        'old_block': '''- [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#rust-194-思维表征资产库)
    - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#11-rust-194-核心语义思维导图)
    - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#24-rust-194-新特性影响矩阵)
    - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#35-rust-194-迭代器选择决策树)
    - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#44-rust-194-array_windows-正确性证明)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)
    - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#本文档的rust-194更新要点)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#最后更新-2026-03-14-rust-194-深度整合)''',
        'new_block': '''- [Rust 1.94 思维表征资产库](#rust-194-思维表征资产库)
    - [1.1 Rust 1.94 核心语义思维导图](#11-rust-194-核心语义思维导图)
    - [2.4 Rust 1.94 新特性影响矩阵](#24-rust-194-新特性影响矩阵)
    - [3.5 Rust 1.94 迭代器选择决策树](#35-rust-194-迭代器选择决策树)
    - [4.4 Rust 1.94 array_windows 正确性证明](#44-rust-194-array_windows-正确性证明)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)''',
    },
    '10_rust_194_core_notes_index.md': {
        'old_block': '''- [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#rust-194-核心研究笔记索引)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)
    - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#本文档的rust-194更新要点)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#最后更新-2026-03-14-rust-194-深度整合)''',
        'new_block': '''- [Rust 1.94 核心研究笔记索引](#rust-194-核心研究笔记索引)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)''',
    },
    '10_rust_194_research_update.md': {
        'old_block': '''  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)
    - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#本文档的rust-194更新要点)
  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#最后更新-2026-03-14-rust-194-深度整合)''',
        'new_block': '''  - [✅ 权威国际化来源对齐升级摘要（Rust 1.96.0+ / Edition 2024）](#-权威国际化来源对齐升级摘要-rust-1960-edition-2024)''',
    },
}


def main():
    for name, cfg in FILES.items():
        p = BASE / name
        text = p.read_text(encoding='utf-8')
        old = cfg['old_block']
        new = cfg['new_block']
        if old not in text:
            print(f'[WARN] old block not found in {name}')
            continue
        text = text.replace(old, new, 1)
        p.write_text(text, encoding='utf-8')
        print(f'[FIXED] {name}')


if __name__ == '__main__':
    main()
