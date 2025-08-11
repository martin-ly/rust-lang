#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
概念词汇表聚合脚本：扫描Markdown标题与“定义”段，汇总概念并输出词汇表。
- 输入：目录(默认 formal_rust/refactor)
- 输出：formal_rust/refactor/CONCEPT_GLOSSARY.md
"""
import os
import re
import sys
from pathlib import Path
from collections import defaultdict
import argparse

HEADING_PATTERN = re.compile(r'^(#{1,6})\s+(.+)$', re.MULTILINE)
DEFINITION_PATTERN = re.compile(r'^[>\s]*[\*\- ]*\*\*?定义\*\*?[:：]\s*(.+)$', re.MULTILINE)
LINK_ANCHOR_PATTERN = re.compile(r'\s+')


def slugify(text: str) -> str:
    t = text.strip().lower()
    t = re.sub(r'[~`!@#$%^&*()\-_=+\[\]{}\\|;:\'",.<>/?]+', '', t)
    t = LINK_ANCHOR_PATTERN.sub('-', t)
    return t


def extract_terms(root: Path, file_path: Path, text: str):
    terms = []
    rel = file_path.relative_to(root).as_posix()
    # 1) 标题中的术语
    for m in HEADING_PATTERN.finditer(text):
        level = len(m.group(1))
        title = m.group(2).strip()
        if level <= 3 and len(title) <= 60:
            terms.append((title, f'{rel}#{slugify(title)}', 'heading'))
    # 2) 定义段落
    for m in DEFINITION_PATTERN.finditer(text):
        term = m.group(1).strip()
        if term:
            terms.append((term, rel, 'definition'))
    return terms


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('path', nargs='?', default='formal_rust/refactor', help='扫描目录')
    args = ap.parse_args()

    root = Path(args.path).resolve()
    all_terms = []

    for p in root.rglob('*.md'):
        try:
            content = p.read_text(encoding='utf-8', errors='ignore')
        except Exception:
            continue
        all_terms.extend(extract_terms(root, p, content))

    # 归一化与计数
    norm_map = defaultdict(list)  # 规范化术语 -> [(原始, 链接, 来源)]
    for t, link, src in all_terms:
        key = t.strip().lower()
        norm_map[key].append((t, link, src))

    # 频次排序
    items = []
    for key, vals in norm_map.items():
        freq = len(vals)
        # 选择一个代表形式（最短的原文）
        repr_term = min((v[0] for v in vals), key=len)
        # 选择一个代表链接（优先 heading）
        heading_links = [v[1] for v in vals if v[2] == 'heading']
        link = heading_links[0] if heading_links else vals[0][1]
        items.append((freq, repr_term, link))

    items.sort(key=lambda x: (-x[0], x[1]))

    # 输出
    out_path = root / 'CONCEPT_GLOSSARY.md'
    lines = []
    lines.append('# 概念词汇表 (自动聚合)')
    lines.append('')
    lines.append('> 说明：以下术语基于标题与“定义”段自动聚合，按出现频次排序。建议人工二次校对与去重合并。')
    lines.append('')
    lines.append('| 术语 | 频次 | 参考链接 |')
    lines.append('|---|:---:|---|')
    for freq, term, link in items[:1000]:
        lines.append(f'| {term} | {freq} | [{link}]({link}) |')
    out_path.write_text('\n'.join(lines), encoding='utf-8')
    print(f'已生成词汇表: {out_path.as_posix()} (共{len(items)}项，展示前1000)')

if __name__ == '__main__':
    main() 