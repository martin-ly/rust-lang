#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
从源Markdown文件(如 00_master_index.md)提取相对链接，
对不存在的目标 Markdown 创建占位 00_index.md 或目标文件本身。

用法：
  python scripts/create_missing_index_stubs.py formal_rust/refactor/00_master_index.md --root formal_rust/refactor
"""
import re
import sys
from pathlib import Path
import argparse
from datetime import datetime

LINK_PATTERN = re.compile(r"\[[^\]]*\]\(([^)]+)\)")

HEADER_TMPL = """# 占位文档

## 📅 文档信息

**文档版本**: v0.1  
**创建日期**: {date}  
**最后更新**: {date}  
**状态**: 待补充  
**质量等级**: 青铜级 ⭐

---

## 1.0 概述

此文档由自动化脚本生成用于修复链接缺失，后续将补充真实内容。
"""

def ensure_stub(root: Path, target_rel: str) -> bool:
    # 忽略外链和锚点
    if target_rel.startswith('http://') or target_rel.startswith('https://') or target_rel.startswith('mailto:'):
        return False
    # 分离#锚点
    path_part = target_rel.split('#', 1)[0]
    if not path_part:
        return False
    target_path = (root / path_part).resolve()
    if target_path.exists():
        return False
    # 确保目录存在
    target_path.parent.mkdir(parents=True, exist_ok=True)
    # 如果不是以.md结尾，忽略
    if target_path.suffix != '.md':
        return False
    # 写入占位内容
    content = HEADER_TMPL.format(date=datetime.now().strftime('%Y-%m-%d'))
    target_path.write_text(content, encoding='utf-8')
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('source', help='源Markdown文件，例如 formal_rust/refactor/00_master_index.md')
    ap.add_argument('--root', default=None, help='根目录，默认为源文件所在根(其父目录)')
    args = ap.parse_args()

    source = Path(args.source)
    if not source.exists():
        print(f'源文件不存在: {source}')
        sys.exit(1)
    root = Path(args.root) if args.root else source.parent

    text = source.read_text(encoding='utf-8', errors='ignore')
    links = LINK_PATTERN.findall(text)
    created = 0
    for url in links:
        # 仅处理相对路径
        if url.startswith(('http://','https://','mailto:')):
            continue
        # 同文件锚点跳过
        if url.startswith('#'):
            continue
        if ensure_stub(root, url):
            created += 1
            print(f'创建占位: {url}')

    print(f'完成。新建占位文件: {created} 个')

if __name__ == '__main__':
    main() 