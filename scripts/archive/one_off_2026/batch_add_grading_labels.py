#!/usr/bin/env python3
"""
批量为 knowledge/ 和 docs/ 文件添加双标签（受众 + 内容分级）。
基于现有头部元数据自动推断，不破坏原有内容。
"""

import re
from pathlib import Path

# 推断规则
def infer_labels(text: str, filepath: Path) -> tuple[str, str]:
    """根据文件头部内容推断受众和内容分级。"""
    
    # 已有双标签则跳过
    if "**受众**:" in text and "**内容分级**:" in text:
        return None, None
    
    text_lower = text.lower()
    
    # 关键词检测
    has_unsafe = "unsafe" in text_lower or "unsafe rust" in text_lower
    has_formal = "形式化" in text or "formal" in text_lower or "语义" in text
    has_nightly = "nightly" in text_lower or "preview" in text_lower or "experimental" in text_lower or "🧪" in text
    has_rfc = "rfc" in text_lower
    has_async = "async" in text_lower
    has_macro = "macro" in text_lower or "宏" in text
    
    # 难度星级检测 — 统计 ⭐/★ 字符数量
    star_chars = re.findall(r'[⭐★]', text)
    stars = len(star_chars) if star_chars else 0
    
    # Bloom 层级检测 — 支持数字格式 L1-L7 或文字格式
    bloom_match = re.search(r'Bloom.*?L(\d)', text, re.I)
    if bloom_match:
        bloom = int(bloom_match.group(1))
    else:
        # 文字格式映射
        bloom_text = re.search(r'Bloom[^\n]*?(记忆|理解|应用|分析|评价|创造)', text, re.I)
        bloom_map = {'记忆': 1, '理解': 2, '应用': 3, '分析': 4, '评价': 5, '创造': 6}
        bloom = bloom_map.get(bloom_text.group(1).lower(), 2) if bloom_text else 2
    
    # 推断受众
    if stars >= 5 or bloom >= 5 or has_formal:
        audience = "[专家] / [研究者]"
    elif stars >= 4 or bloom >= 4 or has_unsafe or has_macro:
        audience = "[进阶] / [专家]"
    elif bloom <= 2:
        audience = "[初学者] / [进阶]"
    else:
        audience = "[进阶]"
    
    # 推断内容分级
    if has_nightly or has_rfc:
        level = "[实验级]"
    elif stars >= 5 or bloom >= 5 or has_formal:
        level = "[研究者级]"
    elif stars >= 3 or bloom >= 3 or has_unsafe or has_async or has_macro:
        level = "[专家级]"
    else:
        level = "[综述级]"
    
    # 特殊路径覆盖
    path_str = str(filepath).lower()
    if "future" in path_str or "preview" in path_str or "nightly" in path_str:
        level = "[实验级]"
        if "专家" not in audience and "研究者" not in audience:
            audience = "[进阶] / [专家]"
    # 仅当文件位于 fundamentals/foundation/01_ 目录下时才降级
    dir_path = str(filepath.parent).lower()
    if "fundamentals" in dir_path or "/01_" in dir_path or "foundation" in dir_path:
        if bloom <= 2:
            level = "[综述级]"
            audience = "[初学者] / [进阶]"
    
    # 00_start 目录强制为初学者级别
    if "00_start" in dir_path:
        level = "[综述级]"
        audience = "[初学者] / [进阶]"
    
    return audience, level


def process_file(filepath: Path, dry_run: bool = True) -> bool:
    """处理单个文件，返回是否修改。"""
    content = filepath.read_text(encoding="utf-8")
    
    # 只处理已有头部元数据的文件（以 # 开头）
    if not content.strip().startswith("#"):
        return False
    
    # 检查是否已有双标签
    if "**受众**:" in content and "**内容分级**:" in content:
        return False
    
    # 取前 30 行用于推断
    header = "\n".join(content.splitlines()[:30])
    audience, level = infer_labels(header, filepath)
    
    if audience is None:
        return False
    
    # 查找插入位置：在标题行后的 > 块中，或标题后第一行
    lines = content.splitlines()
    
    # 策略：如果文件有 > 开头的引用块（元数据块），在块内插入
    # 否则在标题后创建元数据块
    insert_idx = 1  # 默认在标题后
    in_quote_block = False
    quote_block_end = 0
    
    for i, line in enumerate(lines[1:], start=1):
        if line.strip().startswith(">"):
            in_quote_block = True
            quote_block_end = i
        elif in_quote_block and not line.strip():
            # 空行结束引用块
            insert_idx = quote_block_end + 1
            break
        elif in_quote_block and not line.strip().startswith(">"):
            insert_idx = i
            break
    else:
        if in_quote_block:
            insert_idx = quote_block_end + 1
    
    # 构建插入文本
    labels_text = f"> **受众**: {audience}\n> **内容分级**: {level}\n"
    
    # 如果插入位置在引用块内，保持 > 前缀
    if in_quote_block and insert_idx <= quote_block_end + 1:
        # 在引用块末尾追加
        new_lines = lines[:insert_idx] + [">", f"> **受众**: {audience}", f"> **内容分级**: {level}"] + lines[insert_idx:]
    else:
        # 在标题后创建新块
        new_lines = lines[:insert_idx] + [">", f"> **受众**: {audience}", f"> **内容分级**: {level}", ">"] + lines[insert_idx:]
    
    new_content = "\n".join(new_lines)
    
    if not dry_run:
        filepath.write_text(new_content, encoding="utf-8")
    
    return True


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--run", action="store_true", help="实际执行修改（默认 dry-run）")
    parser.add_argument("--dir", default="knowledge", help="目标目录")
    args = parser.parse_args()
    
    target_dir = Path(args.dir)
    if not target_dir.exists():
        print(f"目录不存在: {target_dir}")
        return
    
    modified = 0
    skipped = 0
    
    for md_file in sorted(target_dir.rglob("*.md")):
        # 跳过 archive 目录
        if "archive" in str(md_file).lower():
            skipped += 1
            continue
        
        if process_file(md_file, dry_run=not args.run):
            print(f"{'[DRY-RUN] ' if not args.run else ''}{md_file}")
            modified += 1
        else:
            skipped += 1
    
    print(f"\n{'[DRY-RUN] ' if not args.run else ''}完成: 修改 {modified} 个文件, 跳过 {skipped} 个文件")


if __name__ == "__main__":
    main()
