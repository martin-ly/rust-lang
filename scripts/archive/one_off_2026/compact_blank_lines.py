#!/usr/bin/env python3
"""
压缩 Markdown 文件中的多余空白行，降低 blank-line ratio，同时保留语义结构。

处理范围：
- 代码块外部：最多保留 MAX_OUTSIDE 个连续空行；删除表格行之间、简单列表项之间、
  引用块行之间的空行；删除文件首尾的多余空行。
- 代码块内部：删除 fence 前后的连续空行；块内最多保留 MAX_INSIDE 个连续空行。
- Frontmatter 保持不变。

用法：
    python scripts/compact_blank_lines.py <file_or_dir>...
    python scripts/compact_blank_lines.py --all  # 处理仓库中所有 *.md
"""
from pathlib import Path
import re
import sys

MAX_OUTSIDE = 1       # 代码块外部最多保留 1 个连续空行
MAX_INSIDE = 2        # 代码块内部最多保留 2 个连续空行


def is_table_row(line):
    return line.strip().startswith('|') and line.strip().endswith('|')


def is_list_item(line):
    return bool(re.match(r'^(\s*)([-*]|\d+\.)\s', line))


def is_blockquote(line):
    return line.strip().startswith('>')


def is_heading(line):
    return bool(re.match(r'^#{1,6}\s', line.strip()))


def is_fence(line):
    s = line.strip()
    return s.startswith('```') or s.startswith('~~~')


def compact_outside(lines):
    """压缩代码块/Frontmatter 之外的空行。"""
    result = []
    blank_streak = 0
    prev_line = ''

    for i, line in enumerate(lines):
        stripped = line.strip()

        if stripped == '':
            blank_streak += 1

            if not result:
                continue  # 删除文件开头的空行
            if blank_streak > MAX_OUTSIDE:
                continue

            # 删除表格行之间的空行
            if is_table_row(prev_line):
                j = i + 1
                while j < len(lines) and lines[j].strip() == '':
                    j += 1
                if j < len(lines) and is_table_row(lines[j]):
                    continue

            # 删除简单列表项之间的空行
            if is_list_item(prev_line):
                j = i + 1
                while j < len(lines) and lines[j].strip() == '':
                    j += 1
                if j < len(lines) and is_list_item(lines[j]):
                    continue

            # 删除引用块行之间的空行
            if is_blockquote(prev_line):
                j = i + 1
                while j < len(lines) and lines[j].strip() == '':
                    j += 1
                if j < len(lines) and is_blockquote(lines[j]):
                    continue

            result.append(line)
            continue

        # 非空行
        blank_streak = 0
        result.append(line)
        prev_line = line

    return result


def compact_inside(lines):
    """压缩单个代码块内部的空行；lines 以 fence 开头、以 fence 结尾。"""
    if len(lines) < 2:
        return lines

    fence_open = lines[0]
    fence_close = lines[-1]
    body = lines[1:-1]

    # 删除 body 开头和结尾的连续空行
    while body and body[0].strip() == '':
        body.pop(0)
    while body and body[-1].strip() == '':
        body.pop()

    # 块内最多保留 MAX_INSIDE 个连续空行
    compressed = []
    blank_streak = 0
    for line in body:
        if line.strip() == '':
            blank_streak += 1
            if blank_streak > MAX_INSIDE:
                continue
        else:
            blank_streak = 0
        compressed.append(line)

    return [fence_open] + compressed + [fence_close]


def compact_text(text):
    lines = text.splitlines()
    result = []
    i = 0
    n = len(lines)

    # 先整体处理代码块/Frontmatter 之外
    # 但为了保留代码块，我们标记出特殊区域，先处理外部，再分别处理内部

    # 收集 (start, end, kind) 区间，kind 为 'code' 或 'frontmatter'
    regions = []
    in_code = False
    in_fm = False
    fence = ''
    code_start = 0
    fm_start = 0

    for idx, line in enumerate(lines):
        stripped = line.strip()
        if not in_code and not in_fm and is_fence(stripped):
            in_code = True
            fence = stripped[:3]
            code_start = idx
            continue
        if in_code and stripped.startswith(fence):
            regions.append((code_start, idx, 'code'))
            in_code = False
            fence = ''
            continue
        if idx == 0 and stripped == '---':
            in_fm = True
            fm_start = idx
            continue
        if in_fm and stripped == '---':
            regions.append((fm_start, idx, 'frontmatter'))
            in_fm = False
            continue

    # 如果没有特殊区域，直接处理全部
    if not regions:
        result = compact_outside(lines)
    else:
        last = 0
        for start, end, kind in regions:
            # 处理外部区间 [last, start)
            result.extend(compact_outside(lines[last:start]))

            if kind == 'frontmatter':
                result.extend(lines[start:end + 1])
            elif kind == 'code':
                result.extend(compact_inside(lines[start:end + 1]))

            last = end + 1

        # 处理尾部
        result.extend(compact_outside(lines[last:]))

    # 删除文件尾部空行
    while result and result[-1].strip() == '':
        result.pop()

    return '\n'.join(result) + ('\n' if result else '')


def stats(text):
    lines = text.splitlines()
    total = len(lines)
    blank = sum(1 for l in lines if l.strip() == '')
    ratio = blank / total if total else 0
    max_c = cur = 0
    for l in lines:
        if l.strip() == '':
            cur += 1
            max_c = max(max_c, cur)
        else:
            cur = 0
    return total, blank, ratio, max_c


def main():
    args = sys.argv[1:]
    dry_run = '--dry-run' in args
    if dry_run:
        args.remove('--dry-run')

    all_files = False
    if '--all' in args:
        all_files = True
        args.remove('--all')

    paths = [Path(a) for a in args]

    if all_files:
        paths = [Path('.')]

    if not paths:
        print("Usage: python compact_blank_lines.py [--dry-run] [--all] <file_or_dir>...")
        sys.exit(1)

    files = []
    for p in paths:
        if p.is_file():
            files.append(p)
        else:
            files.extend(p.rglob('*.md'))

    changed = 0
    total_files = 0
    for f in files:
        if any(part in f.parts for part in ['.git', '.venv', 'node_modules', 'target', '__pycache__', '.pytest_cache']):
            continue
        if 'archive' in f.parts:
            continue
        total_files += 1
        try:
            text = f.read_text(encoding='utf-8')
        except Exception as e:
            print(f"Skip {f}: {e}")
            continue

        new_text = compact_text(text)
        if new_text == text:
            continue

        total_before, blank_before, ratio_before, max_before = stats(text)
        total_after, blank_after, ratio_after, max_after = stats(new_text)
        changed += 1

        if dry_run:
            print(f"[dry-run] {f}: blank {blank_before}->{blank_after} "
                  f"ratio {ratio_before:.2f}->{ratio_after:.2f} "
                  f"max {max_before}->{max_after}")
            continue

        f.write_text(new_text, encoding='utf-8', newline='\n')
        print(f"Compacted {f}: blank {blank_before}->{blank_after} "
              f"ratio {ratio_before:.2f}->{ratio_after:.2f} "
              f"max {max_before}->{max_after}")

    print(f"\nProcessed {total_files} files, changed {changed}.")


if __name__ == '__main__':
    main()
