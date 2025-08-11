#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Markdown 重复/相似内容检测工具（基于shingle + Jaccard相似度）
- 输入：目录路径（默认 formal_rust/refactor）
- 输出：duplicates_report.md（相似对、聚类、合并建议）

不依赖第三方库，适合CI环境。
"""
import os
import re
import sys
from pathlib import Path
from collections import defaultdict
from itertools import combinations
import argparse

SHINGLE_SIZE = 5
SIMILARITY_THRESHOLD = 0.5
MAX_PAIRS = 500

CODE_BLOCK_PATTERN = re.compile(r"```[\s\S]*?```", re.MULTILINE)
INLINE_CODE_PATTERN = re.compile(r"`[^`]*`")
MD_LINK_PATTERN = re.compile(r"\[[^\]]*\]\([^\)]*\)")
HTML_TAG_PATTERN = re.compile(r"<[^>]+>")

STOPWORDS = set("""
的 了 和 与 在 是 为 于 对 及 并 或 而 又 这 那 一个 一种 一类 以及 等 等等 上 下 中 内 外 前 后 后续 已经 进行 通过 
如果 因此 但是 但是 然而 所以 并且 需要 可以 应该 可能 主要 其次 同时 总之 例如 比如 等等 其中 
the a an and or of to in on for with as by from at that this these those be have has are is was were will would can could should may might must not
""".split())


def read_markdown_files(root: Path):
    for p in root.rglob('*.md'):
        yield p


def normalize_text(text: str) -> str:
    # 去掉代码块/行内代码/链接/HTML标签
    text = CODE_BLOCK_PATTERN.sub(' ', text)
    text = INLINE_CODE_PATTERN.sub(' ', text)
    text = MD_LINK_PATTERN.sub(' ', text)
    text = HTML_TAG_PATTERN.sub(' ', text)
    # 转小写
    text = text.lower()
    # 非字母数字和中文转空格
    text = re.sub(r"[^0-9a-z\u4e00-\u9fff]+", " ", text)
    # 合并空格
    text = re.sub(r"\s+", " ", text).strip()
    return text


def tokenize(text: str):
    # 简单分词：中文按字符，英文按空格
    tokens = []
    buf = []
    for ch in text:
        if '\u4e00' <= ch <= '\u9fff':
            if buf:
                tokens.extend(''.join(buf).split())
                buf = []
            tokens.append(ch)
        else:
            buf.append(ch)
    if buf:
        tokens.extend(''.join(buf).split())
    # 去停用词与短token
    tokens = [t for t in tokens if t and (len(t) > 1 or ('\u4e00' <= t <= '\u9fff')) and t not in STOPWORDS]
    return tokens


def shingles(tokens, k=SHINGLE_SIZE):
    if len(tokens) < k:
        return set([' '.join(tokens)]) if tokens else set()
    return set(' '.join(tokens[i:i+k]) for i in range(len(tokens)-k+1))


def jaccard(a: set, b: set) -> float:
    if not a or not b:
        return 0.0
    inter = len(a & b)
    if inter == 0:
        return 0.0
    union = len(a | b)
    return inter / union


def union_find(n):
    parent = list(range(n))
    rank = [0]*n
    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    def union(x,y):
        rx, ry = find(x), find(y)
        if rx == ry:
            return
        if rank[rx] < rank[ry]:
            parent[rx] = ry
        elif rank[rx] > rank[ry]:
            parent[ry] = rx
        else:
            parent[ry] = rx
            rank[rx] += 1
    return find, union


def analyze(root: Path, threshold=SIMILARITY_THRESHOLD, k=SHINGLE_SIZE, max_pairs=MAX_PAIRS):
    files = list(read_markdown_files(root))
    texts = []
    tokens_list = []
    shingle_sets = []

    for p in files:
        try:
            text = p.read_text(encoding='utf-8', errors='ignore')
        except Exception:
            text = ''
        texts.append(text)
        norm = normalize_text(text)
        tokens = tokenize(norm)
        tokens_list.append(tokens)
        shingle_sets.append(shingles(tokens, k))

    pairs = []
    for (i, j) in combinations(range(len(files)), 2):
        sim = jaccard(shingle_sets[i], shingle_sets[j])
        if sim >= threshold:
            pairs.append((sim, i, j))
    pairs.sort(reverse=True)
    if len(pairs) > max_pairs:
        pairs = pairs[:max_pairs]

    # 聚类
    find, union = union_find(len(files))
    for sim, i, j in pairs:
        union(i, j)
    clusters = defaultdict(list)
    for idx in range(len(files)):
        clusters[find(idx)].append(idx)
    # 过滤掉单节点
    clusters = {k: v for k, v in clusters.items() if len(v) > 1}

    return files, pairs, clusters


def render_report(root: Path, files, pairs, clusters, out_path: Path):
    lines = []
    lines.append('# 重复/相似内容检测报告')
    lines.append('')
    lines.append('## 总览')
    lines.append(f'- 扫描根目录: `{root.as_posix()}`')
    lines.append(f'- 文件数量: {len(files)}')
    lines.append(f'- 相似对数量(阈值≥{SIMILARITY_THRESHOLD}): {len(pairs)}')
    lines.append(f'- 聚类数量(>1个文件): {len(clusters)}')
    lines.append('')

    if pairs:
        lines.append('## 最高相似度前20对')
        lines.append('')
        header = '| 相似度 | 文件A | 文件B | 合并建议 |'
        sep = '|:---:|---|---|---|'
        lines.extend([header, sep])
        for sim, i, j in pairs[:20]:
            fa = files[i].as_posix(); fb = files[j].as_posix()
            suggestion = '同主题、内容高度重合，建议合并或抽取公共段落' if sim >= 0.7 else '部分重合，建议交叉引用并去重'
            lines.append(f'| {sim:.2f} | `{fa}` | `{fb}` | {suggestion} |')
        lines.append('')

    if clusters:
        lines.append('## 相似簇(建议合并/抽取公共模块)')
        lines.append('')
        for cid, idxs in sorted(clusters.items(), key=lambda kv: -len(kv[1])):
            lines.append(f'### 簇 {cid} (共 {len(idxs)} 个文件)')
            for i in idxs:
                lines.append(f'- `{files[i].as_posix()}`')
            lines.append('')

    # 生成合并计划草案
    lines.append('## 合并计划草案')
    lines.append('')
    lines.append('合并策略建议：')
    lines.append('- 同一目录下的相似文件优先合并')
    lines.append('- 将公共定义与背景提炼为独立小节，被不同文档引用')
    lines.append('- 保留每个文档的独特内容，避免信息丢失')
    lines.append('- 为每次合并建立变更记录与交叉引用映射')

    out_path.write_text('\n'.join(lines), encoding='utf-8')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('path', nargs='?', default='formal_rust/refactor', help='扫描目录')
    ap.add_argument('--threshold', type=float, default=SIMILARITY_THRESHOLD, help='Jaccard相似度阈值')
    ap.add_argument('--k', type=int, default=SHINGLE_SIZE, help='shingle大小')
    ap.add_argument('--out', default='duplicates_report.md', help='报告输出文件')
    args = ap.parse_args()

    root = Path(args.path)
    files, pairs, clusters = analyze(root, args.threshold, args.k)
    render_report(root, files, pairs, clusters, Path(args.out))
    print(f'已生成报告: {args.out}')

if __name__ == '__main__':
    main() 