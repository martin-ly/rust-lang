#!/usr/bin/env python3
"""
执行实际可修复的链接修复
"""
import json
import os
from pathlib import Path

BASE_DIR = Path('e:/_src/rust-lang')
DOCS_DIR = BASE_DIR / 'docs'
CRATES_DIR = BASE_DIR / 'crates'

print("=" * 80)
print("执行链接修复")
print("=" * 80)

# 1. 创建缺失的目录结构
print("\n步骤 1: 创建缺失的目录...")

dirs_to_create = [
    # software_design_theory
    DOCS_DIR / 'research_notes/software_design_theory/01_design_patterns_formal/01_creational',
    DOCS_DIR / 'research_notes/software_design_theory/01_design_patterns_formal/02_structural',
    DOCS_DIR / 'research_notes/software_design_theory/01_design_patterns_formal/03_behavioral',
    DOCS_DIR / 'research_notes/software_design_theory/02_workflow_safe_complete_models',
    DOCS_DIR / 'research_notes/software_design_theory/03_execution_models',
    DOCS_DIR / 'research_notes/software_design_theory/04_compositional_engineering',
    DOCS_DIR / 'research_notes/software_design_theory/05_boundary_system',
    
    # archive
    DOCS_DIR / 'archive/deprecated/coq_skeleton',
    
    # crates
    CRATES_DIR / 'c01_ownership_borrow_scope/examples',
    CRATES_DIR / 'c01_ownership_borrow_scope/tests',
    CRATES_DIR / 'c02_type_system/examples',
    CRATES_DIR / 'c05_threads/examples',
    CRATES_DIR / 'c05_threads/benches',
    CRATES_DIR / 'c06_async/examples',
    CRATES_DIR / 'c06_async/benches',
    CRATES_DIR / 'c08_algorithms/benches',
]

created_count = 0
for dir_path in dirs_to_create:
    if not dir_path.exists():
        dir_path.mkdir(parents=True, exist_ok=True)
        created_count += 1
        print(f"  创建: {dir_path.relative_to(BASE_DIR)}")

print(f"\n创建了 {created_count} 个目录")

# 2. 创建 README.md 占位文件
print("\n步骤 2: 在新建目录中创建 README.md...")

readme_content = """# {title}

> **状态**: 🚧 建设中

此文档目录正在建设中，相关链接将很快可用。

## 相关内容

- [返回上级](../)
- [项目根目录](../../../../README.md)
"""

readme_files = [
    (DOCS_DIR / 'research_notes/software_design_theory/README.md', '软件设计理论'),
    (DOCS_DIR / 'research_notes/software_design_theory/01_design_patterns_formal/README.md', '设计模式形式化'),
    (DOCS_DIR / 'research_notes/software_design_theory/02_workflow_safe_complete_models/README.md', '工作流安全完整模型'),
    (DOCS_DIR / 'research_notes/software_design_theory/03_execution_models/README.md', '执行模型'),
    (DOCS_DIR / 'research_notes/software_design_theory/04_compositional_engineering/README.md', '组合工程'),
    (DOCS_DIR / 'research_notes/software_design_theory/05_boundary_system/README.md', '边界系统'),
    (DOCS_DIR / 'archive/deprecated/README.md', '已弃用文档'),
    (DOCS_DIR / 'archive/deprecated/coq_skeleton/README.md', 'Coq 证明骨架'),
]

readme_created = 0
for file_path, title in readme_files:
    if not file_path.exists():
        file_path.write_text(readme_content.format(title=title), encoding='utf-8')
        readme_created += 1
        print(f"  创建: {file_path.relative_to(BASE_DIR)}")

print(f"\n创建了 {readme_created} 个 README.md")

# 3. 在 crates 目录中创建 .gitkeep
print("\n步骤 3: 在 crates 子目录中创建 .gitkeep...")

gitkeep_paths = [
    CRATES_DIR / 'c01_ownership_borrow_scope/examples/.gitkeep',
    CRATES_DIR / 'c01_ownership_borrow_scope/tests/.gitkeep',
    CRATES_DIR / 'c02_type_system/examples/.gitkeep',
    CRATES_DIR / 'c05_threads/examples/.gitkeep',
    CRATES_DIR / 'c05_threads/benches/.gitkeep',
    CRATES_DIR / 'c06_async/examples/.gitkeep',
    CRATES_DIR / 'c06_async/benches/.gitkeep',
    CRATES_DIR / 'c08_algorithms/benches/.gitkeep',
]

gitkeep_created = 0
for file_path in gitkeep_paths:
    if not file_path.exists():
        file_path.write_text('', encoding='utf-8')
        gitkeep_created += 1
        print(f"  创建: {file_path.relative_to(BASE_DIR)}")

print(f"\n创建了 {gitkeep_created} 个 .gitkeep 文件")

# 4. 统计修复结果
print("\n" + "=" * 80)
print("修复总结")
print("=" * 80)
print(f"""
已执行的修复操作:
  - 创建目录: {created_count}
  - 创建 README.md: {readme_created}
  - 创建 .gitkeep: {gitkeep_created}

这些修复解决了以下问题:
  - software_design_theory 目录不存在 (47个链接)
  - archive/deprecated 目录不存在 (18个链接)
  - crates 子目录不存在 (部分问题)

注意: 还需要手动修复以下问题:
  - 外部URL格式问题 (4个)
  - 模板占位符链接 (12个)
  - rust-formal-engineering-system 目录 (37个链接)
  - 其他相对路径问题 (223个)
""")
