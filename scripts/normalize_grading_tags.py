#!/usr/bin/env python3
"""
规范化 concept/ 文件中的双标签（受众 + 内容分级）。
"""

import re
from pathlib import Path

CONCEPT_DIR = Path("concept")

VALID_AUDIENCES = {"[初学者]", "[进阶]", "[专家]", "[研究者]"}
VALID_GRADINGS = {"[综述级]", "[实验级]", "[专家级]", "[研究者级]"}

# 映射非标准标签到标准标签
GRADING_MAP = {
    "[指南级]": "[综述级]",
    "[参考级]": "[综述级]",
    "[研究级]": "[研究者级]",
    "[操作级]": "[专家级]",
}

AUDIENCE_MAP = {
    "[初学者 / 进阶]": "[进阶]",
    "[进阶 / 专家]": "[专家]",
    "[研究者 / 专家]": "[研究者]",
    "[专家 / 研究者]": "[专家]",
}

# 目录默认映射
DIR_DEFAULTS = {
    "00_meta": ("[初学者]", "[综述级]"),
    "01_foundation": ("[初学者]", "[综述级]"),
    "02_intermediate": ("[进阶]", "[专家级]"),
    "03_advanced": ("[进阶]", "[专家级]"),
    "04_formal": ("[研究者]", "[研究者级]"),
    "05_comparative": ("[进阶]", "[综述级]"),
    "06_ecosystem": ("[进阶]", "[综述级]"),
    "07_future": ("[专家]", "[实验级]"),
}


def get_defaults(rel_path: str) -> tuple:
    for dir_name, defaults in DIR_DEFAULTS.items():
        if dir_name in rel_path:
            return defaults
    return ("[进阶]", "[综述级]")


def normalize_line(line: str, tag_name: str, valid_set: set, mapping: dict) -> str:
    """规范化单行标签"""
    if tag_name not in line:
        return line
    
    # 检查是否包含多个值或映射
    for old_val, new_val in mapping.items():
        if old_val in line:
            return f"> **{tag_name}**: {new_val}\n"
    
    # 检查是否包含多个斜杠分隔的值
    if " / " in line:
        # 取第一个有效值
        for val in valid_set:
            if val in line:
                return f"> **{tag_name}**: {val}\n"
    
    # 检查是否有效
    if not any(v in line for v in valid_set):
        # 无效值，用默认值替换
        return None  # 需要外部处理
    
    return line


def process_file(md_path: Path) -> list:
    rel = str(md_path.relative_to(CONCEPT_DIR)).replace("\\", "/")
    content = md_path.read_text(encoding="utf-8")
    lines = content.splitlines(keepends=True)
    
    has_audience = False
    has_grading = False
    audience_default, grading_default = get_defaults(rel)
    
    fixed = []
    for i, line in enumerate(lines):
        if "**受众**:" in line:
            has_audience = True
            new_line = normalize_line(line, "受众", VALID_AUDIENCES, AUDIENCE_MAP)
            if new_line is None:
                new_line = f"> **受众**: {audience_default}\n"
            lines[i] = new_line
            fixed.append(f"受众: {line.strip()} -> {new_line.strip()}")
        elif "**内容分级**:" in line:
            has_grading = True
            new_line = normalize_line(line, "内容分级", VALID_GRADINGS, GRADING_MAP)
            if new_line is None:
                new_line = f"> **内容分级**: {grading_default}\n"
            lines[i] = new_line
            fixed.append(f"内容分级: {line.strip()} -> {new_line.strip()}")
    
    # 如果缺少标签，在第一个元数据行后插入
    if not has_audience or not has_grading:
        insert_idx = 0
        for i, line in enumerate(lines):
            if line.startswith("> "):
                insert_idx = i + 1
        
        inserts = []
        if not has_audience:
            inserts.append(f"> **受众**: {audience_default}\n")
            fixed.append(f"缺少受众 -> {audience_default}")
        if not has_grading:
            inserts.append(f"> **内容分级**: {grading_default}\n")
            fixed.append(f"缺少内容分级 -> {grading_default}")
        
        for ins in reversed(inserts):
            lines.insert(insert_idx, ins)
    
    md_path.write_text("".join(lines), encoding="utf-8")
    return fixed


def main():
    files = sorted(CONCEPT_DIR.rglob("*.md"))
    files = [f for f in files if "archive" not in str(f) and "sources" not in str(f)]
    
    total_fixed = 0
    for md_path in files:
        fixed = process_file(md_path)
        if fixed:
            total_fixed += len(fixed)
            print(f"{md_path.relative_to(CONCEPT_DIR)}:")
            for f in fixed:
                print(f"  - {f}")
    
    print(f"\n规范化完成: 处理了 {len(files)} 个文件，修复 {total_fixed} 处问题")


if __name__ == "__main__":
    main()
