#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Markdown 链接有效性检查脚本
- 检查 [text](path#anchor) 的文件是否存在，若为同文件锚点则检查标题是否存在
- 输出 markdown 报告
"""
import os
import re
import sys
from pathlib import Path
import argparse

LINK_PATTERN = re.compile(r"\[([^\]]+)\]\(([^)]+)\)")
HEADING_PATTERN = re.compile(r'^(#{1,6})\s+(.+)$', re.MULTILINE)

# 仅保留：字母数字、空格、连字符、下划线、以及中日韩统一表意文字
ALLOW_CHARS_PATTERN = re.compile(r"[^0-9A-Za-z\u4e00-\u9fff\- _]+")
MULTI_HYPHENS_PATTERN = re.compile(r"\-+")
MULTI_SPACES_PATTERN = re.compile(r"\s+")


def slugify(text: str) -> str:
    t = text.strip().lower()
    # 先将连续空白统一为单空格
    t = MULTI_SPACES_PATTERN.sub(' ', t)
    # 去除emoji及其他符号，仅保留允许字符
    t = ALLOW_CHARS_PATTERN.sub('', t)
    # 将空格替换为连字符
    t = t.replace(' ', '-')
    # 合并多连字符
    t = MULTI_HYPHENS_PATTERN.sub('-', t)
    # 去除首尾连字符
    t = t.strip('-')
    return t


def extract_anchors(text: str):
    anchors = set()
    for m in HEADING_PATTERN.finditer(text):
        title = m.group(2).strip()
        anchors.add(slugify(title))
    return anchors


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('path', nargs='?', default='formal_rust/refactor', help='扫描目录')
    ap.add_argument('--out', default='link_check_report.md')
    args = ap.parse_args()

    root = Path(args.path)
    problems = []

    for p in root.rglob('*.md'):
        try:
            content = p.read_text(encoding='utf-8', errors='ignore')
        except Exception:
            continue
        anchors = extract_anchors(content)
        for m in LINK_PATTERN.finditer(content):
            url = m.group(2)
            if url.startswith('http://') or url.startswith('https://') or url.startswith('mailto:'):
                continue
            # 拆分 path#anchor
            if '#' in url:
                path_part, anchor = url.split('#', 1)
            else:
                path_part, anchor = url, None
            if not path_part or path_part.startswith('#'):
                # 同文件锚点
                a = anchor or path_part.lstrip('#')
                if a and slugify(a) not in anchors:
                    problems.append((p.as_posix(), url, 'missing_anchor'))
                continue
            target = (p.parent / path_part).resolve()
            if not target.exists():
                problems.append((p.as_posix(), url, 'missing_file'))
                continue
            if anchor:
                try:
                    tcontent = target.read_text(encoding='utf-8', errors='ignore')
                    tanchors = extract_anchors(tcontent)
                    if slugify(anchor) not in tanchors:
                        problems.append((p.as_posix(), url, 'missing_anchor'))
                except Exception:
                    problems.append((p.as_posix(), url, 'unreadable_target'))

    lines = []
    lines.append('# 链接检查报告')
    lines.append('')
    lines.append(f'- 根目录: `{root.as_posix()}`')
    lines.append(f'- 问题数量: {len(problems)}`')
    lines.append('')
    if problems:
        lines.append('| 源文件 | 链接 | 问题 |')
        lines.append('|---|---|---|')
        for src, link, kind in problems[:2000]:
            desc = {'missing_file':'目标文件不存在','missing_anchor':'目标锚点缺失','unreadable_target':'无法读取目标文件'}.get(kind, kind)
            lines.append(f'| `{src}` | `{link}` | {desc} |')
    Path(args.out).write_text('\n'.join(lines), encoding='utf-8')
    print(f'已生成报告: {args.out} (问题 {len(problems)})')

if __name__ == '__main__':
    main() 