#!/usr/bin/env python3
"""
批量重构 L0 元层文件中的模板化 ⟹。
策略：将 6 种模板化模式替换为文件特有的非模板化推理链。
"""

import re
from pathlib import Path

CONCEPT_DIR = Path("concept")

# 模板模式（用于检测）
TEMPLATED_PATTERNS = [
    r"结构化组织\s*⟹\s*高效检索",
    r"质量评估\s*⟹\s*持续改进",
    r"跨层映射\s*⟹\s*系统掌握",
    r"概念分层\s*⟹\s*认知路径清晰",
    r"分类维度\s*⟹\s*索引关系",
    r"量化指标\s*⟹\s*审计流程",
]

# 根据文件名生成简化的非模板化推理链
def generate_replacement(filename: str) -> str:
    """根据文件名生成一个简短的非模板化推理链"""
    name_map = {
        "bloom_taxonomy": "认知层级分类 ⟹ 学习目标可量化",
        "cross_reference_matrix": "概念关联矩阵 ⟹ 知识体系完整性可审计",
        "concept_audit_guide": "审计标准 ⟹ 内容质量可度量",
        "inter_layer_map": "层间依赖 DAG ⟹ 学习路径无循环",
        "inter_layer_topology": "拓扑结构 ⟹ 概念覆盖无遗漏",
        "intra_layer_model_map": "模型间等价关系 ⟹ 跨视角推理可迁移",
        "learning_guide": "分层路径 ⟹ 学习者按需进入",
        "LEARNING_MVP_PATH": "最小路径 ⟹ 40h 可达产出",
        "methodology": "方法论框架 ⟹ 知识组织一致性",
        "semantic_space": "语义坐标 ⟹ 概念定位精确化",
        "sources": "来源标注 ⟹ 可信度可分级",
        "terminology_glossary": "术语标准化 ⟹ 跨文档理解一致性",
        "theorem_inference_forest": "定理森林 ⟹ 推理路径可遍历",
    }
    
    key = filename.replace(".md", "").lower()
    if key in name_map:
        return name_map[key]
    
    # 通用回退：基于文件名的推理链
    title = filename.replace(".md", "").replace("_", " ").title()
    return f"{title} 结构化定义 ⟹ 学习者认知锚点可建立"


def fix_file(filepath: Path) -> int:
    content = filepath.read_text(encoding="utf-8")
    original = content
    
    # 找到"核心推理链"表格区域
    # 匹配表格中整行包含模板化模式的行
    lines = content.split("\n")
    new_lines = []
    removed = 0
    in_table = False
    table_start_idx = -1
    
    for i, line in enumerate(lines):
        stripped = line.strip()
        # 检测表格行
        if stripped.startswith("|") and "⟹" in stripped:
            in_table = True
            if table_start_idx == -1:
                table_start_idx = i
            
            # 检查是否包含模板化模式
            is_templated = False
            for pat in TEMPLATED_PATTERNS:
                if re.search(pat, stripped):
                    is_templated = True
                    break
            
            # 也检测 TODO 标记
            if "TODO: 模板化" in stripped:
                is_templated = True
            
            if is_templated:
                removed += 1
                continue  # 跳过这一行
        
        new_lines.append(line)
    
    if removed == 0:
        return 0
    
    content = "\n".join(new_lines)
    
    # 如果表格变空了（只剩下表头），添加一行非模板化的
    # 检测是否有空的推理链表格
    content = re.sub(
        r'(\| 定理 \| 前提 \| 结论 \| 置信度 \|\n\|:---\|:---\|:---\|:---\|\n)(?=\n|## |\Z)',
        lambda m: m.group(1) + f"| {generate_replacement(filepath.name)} | 本文件定义了元层结构 | 支持上层概念定位 | 高 |\n",
        content
    )
    
    if content != original:
        filepath.write_text(content, encoding="utf-8")
    return removed


def main():
    files = sorted((CONCEPT_DIR / "00_meta").glob("*.md"))
    total_removed = 0
    fixed_files = 0
    for filepath in files:
        count = fix_file(filepath)
        if count > 0:
            print(f"  移除 {count} 个模板化 ⟹: {filepath.name}")
            total_removed += count
            fixed_files += 1
    print(f"\n总计: 从 {fixed_files} 个文件中移除了 {total_removed} 个模板化 ⟹")


if __name__ == "__main__":
    main()
