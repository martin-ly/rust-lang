#!/usr/bin/env python3
"""
批量为 concept/ 文件注入双标签（受众 + 内容分级）。
策略：
  1. 已有标签的文件跳过
  2. 根据目录推断默认分级
  3. 统一标签格式
"""

import os
import re
from pathlib import Path

CONCEPT_DIR = Path("concept")

# 目录 -> (默认受众, 默认分级)
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

# 特殊文件覆盖
FILE_OVERRIDES = {
    "01_foundation/00_pl_prerequisites.md": ("[初学者]", "[综述级]"),
    "01_foundation/03_lifetimes_advanced.md": ("[进阶]", "[专家级]"),
    "01_foundation/10_error_handling_basics.md": ("[初学者]", "[综述级]"),
    "01_foundation/10_numerics.md": ("[初学者]", "[综述级]"),
    "01_foundation/11_numeric_types.md": ("[初学者]", "[综述级]"),
    "01_foundation/16_testing_basics.md": ("[初学者]", "[综述级]"),
    "01_foundation/17_collections_advanced.md": ("[进阶]", "[专家级]"),
    "01_foundation/19_numerics.md": ("[进阶]", "[专家级]"),
    "01_foundation/20_variable_model.md": ("[进阶]", "[专家级]"),
    "01_foundation/21_effects_and_purity.md": ("[研究者]", "[研究者级]"),
    "01_foundation/22_data_abstraction_spectrum.md": ("[研究者]", "[研究者级]"),
    "02_intermediate/05_assert_matches.md": ("[进阶]", "[综述级]"),
    "02_intermediate/06_range_types.md": ("[进阶]", "[综述级]"),
    "02_intermediate/07_closure_types.md": ("[进阶]", "[综述级]"),
    "02_intermediate/11_cow_and_borrowed.md": ("[进阶]", "[综述级]"),
    "02_intermediate/15_error_handling_deep_dive.md": ("[进阶]", "[专家级]"),
    "02_intermediate/16_iterator_patterns.md": ("[进阶]", "[专家级]"),
    "02_intermediate/22_iterator_patterns.md": ("[进阶]", "[专家级]"),
    "03_advanced/18_network_programming.md": ("[进阶]", "[综述级]"),
    "04_formal/22_modern_verification_tools.md": ("[专家]", "[实验级]"),
    "07_future/rust_1_97_preview.md": ("[专家]", "[实验级]"),
    "07_future/README.md": ("[专家]", "[综述级]"),
}

RE_GRADING = re.compile(r"\*\*内容分级\*\*:\s*(\[[^\]]+\])")
RE_AUDIENCE = re.compile(r"\*\*受众\*\*:\s*(\[[^\]]+\])")

def get_defaults(rel_path: str) -> tuple:
    if rel_path in FILE_OVERRIDES:
        return FILE_OVERRIDES[rel_path]
    for dir_name, defaults in DIR_DEFAULTS.items():
        if dir_name in rel_path:
            return defaults
    return ("[进阶]", "[综述级]")

def process_file(md_path: Path) -> dict:
    rel = str(md_path.relative_to(CONCEPT_DIR)).replace("\\", "/")
    content = md_path.read_text(encoding="utf-8")
    
    has_grading = RE_GRADING.search(content)
    has_audience = RE_AUDIENCE.search(content)
    
    result = {
        "path": rel,
        "has_grading": bool(has_grading),
        "has_audience": bool(has_audience),
        "action": "skip",
    }
    
    if has_grading and has_audience:
        result["action"] = "skip"
        return result
    
    audience, grading = get_defaults(rel)
    
    # 如果已有分级但没有受众，或反之，尝试智能补充
    lines = content.splitlines(keepends=True)
    
    # 找到第一个以 "> " 开头的元数据行，在其后插入
    insert_idx = 0
    for i, line in enumerate(lines):
        if line.startswith("> **") or line.startswith("> **内容分级") or line.startswith("> **受众"):
            insert_idx = i + 1
    
    # 如果没有找到元数据行，在第一行后插入
    if insert_idx == 0:
        insert_idx = 1
    
    new_lines = lines.copy()
    inserts = []
    if not has_grading:
        inserts.append(f"> **内容分级**: {grading}\n")
    if not has_audience:
        inserts.append(f"> **受众**: {audience}\n")
    
    for ins in reversed(inserts):
        new_lines.insert(insert_idx, ins)
    
    md_path.write_text("".join(new_lines), encoding="utf-8")
    result["action"] = "updated"
    result["added"] = inserts
    return result

def main():
    files = sorted(CONCEPT_DIR.rglob("*.md"))
    # 排除 archive/ 和 sources/
    files = [f for f in files if "archive" not in str(f) and "sources" not in str(f)]
    
    stats = {"total": 0, "skip": 0, "updated": 0}
    updated_files = []
    
    for md_path in files:
        rel = str(md_path.relative_to(CONCEPT_DIR)).replace("\\", "/")
        if rel.startswith("archive") or rel.startswith("sources"):
            continue
        stats["total"] += 1
        result = process_file(md_path)
        if result["action"] == "updated":
            stats["updated"] += 1
            updated_files.append(result)
        else:
            stats["skip"] += 1
    
    print(f"处理完成: {stats['total']} 文件")
    print(f"  已跳过 (已有标签): {stats['skip']}")
    print(f"  已更新 (注入标签): {stats['updated']}")
    if updated_files:
        print("\n更新文件列表:")
        for r in updated_files[:20]:
            print(f"  + {r['path']}")
        if len(updated_files) > 20:
            print(f"  ... 共 {len(updated_files)} 个")

if __name__ == "__main__":
    main()
