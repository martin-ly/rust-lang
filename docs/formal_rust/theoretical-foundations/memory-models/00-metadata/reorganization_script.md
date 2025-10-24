# 内存模型目录重组实施脚本


## 📊 目录

- [1. 目录结构创建脚本](#1-目录结构创建脚本)
  - [1.1 Bash脚本](#11-bash脚本)
  - [1.2 PowerShell脚本 (Windows)](#12-powershell脚本-windows)
- [2. 文件迁移脚本](#2-文件迁移脚本)
  - [2.1 核心理论文件迁移](#21-核心理论文件迁移)
  - [2.2 语义分析文件迁移](#22-语义分析文件迁移)
  - [2.3 高级特性文件迁移](#23-高级特性文件迁移)
  - [2.4 应用实践文件迁移](#24-应用实践文件迁移)
  - [2.5 工具调试文件迁移](#25-工具调试文件迁移)
  - [2.6 元数据文件迁移](#26-元数据文件迁移)
- [3. 内容整合脚本](#3-内容整合脚本)
  - [3.1 理论内容整合](#31-理论内容整合)
  - [3.2 实践内容整合](#32-实践内容整合)
- [4. 索引生成脚本](#4-索引生成脚本)
  - [4.1 自动索引生成](#41-自动索引生成)
  - [4.2 交叉引用生成](#42-交叉引用生成)
- [5. 验证脚本](#5-验证脚本)
  - [5.1 结构验证](#51-结构验证)
  - [5.2 内容验证](#52-内容验证)
- [6. 使用说明](#6-使用说明)
  - [6.1 执行顺序](#61-执行顺序)
  - [6.2 注意事项](#62-注意事项)
  - [6.3 回滚方案](#63-回滚方案)


**文档版本**: V1.0  
**创建日期**: 2025-01-27  
**用途**: 执行内存模型目录的重组和优化

---

## 1. 目录结构创建脚本

### 1.1 Bash脚本

```bash
#!/bin/bash

# 内存模型目录重组脚本
# 使用方法: ./reorganize_memory_models.sh

set -e  # 遇到错误立即退出

echo "开始内存模型目录重组..."

# 创建新的目录结构
echo "创建新的目录结构..."
mkdir -p 01-core-theory
mkdir -p 02-semantics-analysis
mkdir -p 03-advanced-features
mkdir -p 04-practical-applications
mkdir -p 05-tools-and-debugging
mkdir -p 00-metadata

echo "目录结构创建完成"
```

### 1.2 PowerShell脚本 (Windows)

```powershell
# 内存模型目录重组脚本 (Windows)
# 使用方法: .\reorganize_memory_models.ps1

Write-Host "开始内存模型目录重组..." -ForegroundColor Green

# 创建新的目录结构
Write-Host "创建新的目录结构..." -ForegroundColor Yellow
New-Item -ItemType Directory -Path "01-core-theory" -Force
New-Item -ItemType Directory -Path "02-semantics-analysis" -Force
New-Item -ItemType Directory -Path "03-advanced-features" -Force
New-Item -ItemType Directory -Path "04-practical-applications" -Force
New-Item -ItemType Directory -Path "05-tools-and-debugging" -Force
New-Item -ItemType Directory -Path "00-metadata" -Force

Write-Host "目录结构创建完成" -ForegroundColor Green
```

---

## 2. 文件迁移脚本

### 2.1 核心理论文件迁移

```bash
#!/bin/bash

echo "迁移核心理论文件..."

# 核心理论文件迁移
mv "01_memory_management.md" "01-core-theory/01-memory-model-foundations.md"
mv "01_memory_model_theory.md" "01-core-theory/02-ownership-borrowing-theory.md"
mv "memory_safety_theory.md" "01-core-theory/03-memory-safety-theory.md"
mv "01_formal_memory_management_system.md" "01-core-theory/04-memory-allocation-theory.md"
mv "memory_safety_analysis.md" "01-core-theory/05-smart-pointers-theory.md"

echo "核心理论文件迁移完成"
```

### 2.2 语义分析文件迁移

```bash
#!/bin/bash

echo "迁移语义分析文件..."

# 语义分析文件迁移
mv "01_memory_layout_semantics.md" "02-semantics-analysis/01-memory-layout-semantics.md"
mv "02_memory_allocation_semantics.md" "02-semantics-analysis/02-memory-allocation-semantics.md"
mv "03_memory_safety_semantics.md" "02-semantics-analysis/03-memory-safety-semantics.md"
mv "04_pointer_semantics.md" "02-semantics-analysis/04-pointer-reference-semantics.md"
mv "05_reference_semantics.md" "02-semantics-analysis/05-lifetime-semantics.md"

echo "语义分析文件迁移完成"
```

### 2.3 高级特性文件迁移

```bash
#!/bin/bash

echo "迁移高级特性文件..."

# 高级特性文件迁移
mv "04_async_memory_model_theory.md" "03-advanced-features/01-async-memory-model.md"
mv "unsafe_code_verification_theory.md" "03-advanced-features/02-unsafe-code-verification.md"
mv "layered_memory_model.md" "03-advanced-features/03-layered-memory-model.md"
mv "08_performance_optimization.md" "03-advanced-features/04-performance-optimization.md"

echo "高级特性文件迁移完成"
```

### 2.4 应用实践文件迁移

```bash
#!/bin/bash

echo "迁移应用实践文件..."

# 应用实践文件迁移
mv "gpu_memory_examples.md" "04-practical-applications/01-gpu-memory-management.md"
mv "embedded_memory_examples.md" "04-practical-applications/02-embedded-memory-management.md"
mv "distributed_memory_examples.md" "04-practical-applications/03-distributed-memory-management.md"
mv "advanced_memory_systems_analysis.md" "04-practical-applications/04-specialized-memory-management.md"

echo "应用实践文件迁移完成"
```

### 2.5 工具调试文件迁移

```bash
#!/bin/bash

echo "迁移工具调试文件..."

# 工具调试文件迁移
mv "12.14_memory_debugging.md" "05-tools-and-debugging/01-memory-debugging-techniques.md"
mv "12.13_memory_visualization.md" "05-tools-and-debugging/02-memory-visualization-tools.md"
mv "12.10_memory_leak_detection.md" "05-tools-and-debugging/03-memory-leak-detection.md"
mv "12.11_memory_optimization.md" "05-tools-and-debugging/04-performance-profiling.md"

echo "工具调试文件迁移完成"
```

### 2.6 元数据文件迁移

```bash
#!/bin/bash

echo "迁移元数据文件..."

# 元数据文件迁移
mv "README.md" "00-metadata/README.md"
mv "术语表.md" "00-metadata/GLOSSARY.md"
mv "交叉引用清单.md" "00-metadata/CROSS_REFERENCES.md"

# 创建新的索引文件
touch "00-metadata/INDEX.md"
touch "00-metadata/CHANGELOG.md"

echo "元数据文件迁移完成"
```

---

## 3. 内容整合脚本

### 3.1 理论内容整合

```python
#!/usr/bin/env python3

"""
理论内容整合脚本
用于合并重复的理论内容并统一格式
"""

import os
import re
from pathlib import Path

def merge_theory_files():
    """合并理论文件"""
    
    # 定义要合并的文件组
    theory_groups = {
        "01-core-theory/01-memory-model-foundations.md": [
            "01_memory_management.md",
            "01_memory_model_theory.md",
            "memory_safety_theory.md"
        ],
        "01-core-theory/02-ownership-borrowing-theory.md": [
            "05_reference_semantics.md",
            "06_smart_pointer_semantics.md"
        ],
        "01-core-theory/03-memory-safety-theory.md": [
            "02_memory_safety_semantics.md",
            "03_memory_safety_semantics.md",
            "04_memory_safety_semantics.md"
        ]
    }
    
    for target_file, source_files in theory_groups.items():
        print(f"合并文件到: {target_file}")
        
        # 读取源文件内容
        content_parts = []
        for source_file in source_files:
            if os.path.exists(source_file):
                with open(source_file, 'r', encoding='utf-8') as f:
                    content_parts.append(f.read())
        
        # 合并内容
        merged_content = merge_content_parts(content_parts)
        
        # 写入目标文件
        with open(target_file, 'w', encoding='utf-8') as f:
            f.write(merged_content)
        
        print(f"完成: {target_file}")

def merge_content_parts(parts):
    """合并内容部分"""
    # 去重和结构化合并逻辑
    merged = []
    seen_sections = set()
    
    for part in parts:
        lines = part.split('\n')
        current_section = None
        
        for line in lines:
            # 检测章节标题
            if line.startswith('#'):
                current_section = line.strip()
                if current_section not in seen_sections:
                    seen_sections.add(current_section)
                    merged.append(line)
            else:
                merged.append(line)
    
    return '\n'.join(merged)

if __name__ == "__main__":
    merge_theory_files()
```

### 3.2 实践内容整合

```python
#!/usr/bin/env python3

"""
实践内容整合脚本
用于整合分散的示例代码和优化策略
"""

def merge_practice_files():
    """合并实践文件"""
    
    practice_groups = {
        "04-practical-applications/01-gpu-memory-management.md": [
            "gpu_memory_examples.md",
            "12.11_memory_optimization.md"
        ],
        "04-practical-applications/02-embedded-memory-management.md": [
            "embedded_memory_examples.md",
            "12.10_memory_leak_detection.md"
        ],
        "04-practical-applications/03-distributed-memory-management.md": [
            "distributed_memory_examples.md",
            "08_shared_memory.md"
        ]
    }
    
    for target_file, source_files in practice_groups.items():
        print(f"整合实践文件到: {target_file}")
        
        # 读取和整合源文件
        content_parts = []
        for source_file in source_files:
            if os.path.exists(source_file):
                with open(source_file, 'r', encoding='utf-8') as f:
                    content_parts.append(f.read())
        
        # 整合内容
        integrated_content = integrate_practice_content(content_parts)
        
        # 写入目标文件
        with open(target_file, 'w', encoding='utf-8') as f:
            f.write(integrated_content)
        
        print(f"完成: {target_file}")

def integrate_practice_content(parts):
    """整合实践内容"""
    # 按主题组织内容
    sections = {
        "theory": [],
        "implementation": [],
        "examples": [],
        "optimization": [],
        "benchmarks": []
    }
    
    for part in parts:
        # 解析内容并分类
        lines = part.split('\n')
        current_section = "examples"  # 默认分类
        
        for line in lines:
            if "理论" in line or "theory" in line.lower():
                current_section = "theory"
            elif "实现" in line or "implementation" in line.lower():
                current_section = "implementation"
            elif "优化" in line or "optimization" in line.lower():
                current_section = "optimization"
            elif "基准" in line or "benchmark" in line.lower():
                current_section = "benchmarks"
            
            sections[current_section].append(line)
    
    # 重新组织内容
    organized_content = []
    for section_name, content in sections.items():
        if content:
            organized_content.append(f"## {section_name.title()}")
            organized_content.extend(content)
            organized_content.append("")
    
    return '\n'.join(organized_content)

if __name__ == "__main__":
    merge_practice_files()
```

---

## 4. 索引生成脚本

### 4.1 自动索引生成

```python
#!/usr/bin/env python3

"""
自动索引生成脚本
用于生成完整的文档索引和交叉引用
"""

import os
import re
from pathlib import Path
from datetime import datetime

def generate_index():
    """生成完整索引"""
    
    index_content = []
    index_content.append("# 内存模型文档索引")
    index_content.append("")
    index_content.append("**生成时间**: " + str(datetime.now()))
    index_content.append("**文档总数**: " + str(count_documents()))
    index_content.append("")
    
    # 遍历所有目录
    directories = [
        ("01-core-theory", "核心理论"),
        ("02-semantics-analysis", "语义分析"),
        ("03-advanced-features", "高级特性"),
        ("04-practical-applications", "应用实践"),
        ("05-tools-and-debugging", "工具调试")
    ]
    
    for dir_name, dir_title in directories:
        index_content.append(f"## {dir_title}")
        index_content.append("")
        
        if os.path.exists(dir_name):
            files = sorted(os.listdir(dir_name))
            for file in files:
                if file.endswith('.md'):
                    title = extract_title(os.path.join(dir_name, file))
                    index_content.append(f"- [{title}]({dir_name}/{file})")
        
        index_content.append("")
    
    # 写入索引文件
    with open("00-metadata/INDEX.md", 'w', encoding='utf-8') as f:
        f.write('\n'.join(index_content))

def extract_title(file_path):
    """提取文档标题"""
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            first_line = f.readline().strip()
            if first_line.startswith('# '):
                return first_line[2:]
            return os.path.basename(file_path).replace('.md', '')
    except:
        return os.path.basename(file_path).replace('.md', '')

def count_documents():
    """统计文档总数"""
    count = 0
    for root, dirs, files in os.walk('.'):
        for file in files:
            if file.endswith('.md'):
                count += 1
    return count

if __name__ == "__main__":
    generate_index()
```

### 4.2 交叉引用生成

```python
#!/usr/bin/env python3

"""
交叉引用生成脚本
用于生成文档间的交叉引用关系
"""

import os
import re
from pathlib import Path

def generate_cross_references():
    """生成交叉引用"""
    
    cross_ref_content = []
    cross_ref_content.append("# 内存模型文档交叉引用")
    cross_ref_content.append("")
    
    # 扫描所有文档中的引用
    references = scan_references()
    
    # 按文档组织引用关系
    for doc, refs in references.items():
        cross_ref_content.append(f"## {doc}")
        cross_ref_content.append("")
        
        if refs:
            for ref in refs:
                cross_ref_content.append(f"- 引用: {ref}")
        else:
            cross_ref_content.append("- 无交叉引用")
        
        cross_ref_content.append("")
    
    # 写入交叉引用文件
    with open("00-metadata/CROSS_REFERENCES.md", 'w', encoding='utf-8') as f:
        f.write('\n'.join(cross_ref_content))

def scan_references():
    """扫描文档中的引用"""
    references = {}
    
    for root, dirs, files in os.walk('.'):
        for file in files:
            if file.endswith('.md'):
                file_path = os.path.join(root, file)
                refs = extract_references(file_path)
                if refs:
                    references[file] = refs
    
    return references

def extract_references(file_path):
    """提取文档中的引用"""
    refs = []
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
            
            # 查找链接引用
            link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
            matches = re.findall(link_pattern, content)
            
            for match in matches:
                refs.append(f"{match[0]} -> {match[1]}")
            
            # 查找文档引用
            doc_pattern = r'\[([^\]]+\.md)\]'
            doc_matches = re.findall(doc_pattern, content)
            
            for match in doc_matches:
                refs.append(f"文档引用: {match}")
    
    except Exception as e:
        print(f"处理文件 {file_path} 时出错: {e}")
    
    return refs

if __name__ == "__main__":
    generate_cross_references()
```

---

## 5. 验证脚本

### 5.1 结构验证

```python
#!/usr/bin/env python3

"""
结构验证脚本
用于验证重组后的目录结构是否正确
"""

def validate_structure():
    """验证目录结构"""
    
    expected_structure = {
        "01-core-theory": [
            "01-memory-model-foundations.md",
            "02-ownership-borrowing-theory.md",
            "03-memory-safety-theory.md",
            "04-memory-allocation-theory.md",
            "05-smart-pointers-theory.md"
        ],
        "02-semantics-analysis": [
            "01-memory-layout-semantics.md",
            "02-memory-allocation-semantics.md",
            "03-memory-safety-semantics.md",
            "04-pointer-reference-semantics.md",
            "05-lifetime-semantics.md"
        ],
        "03-advanced-features": [
            "01-async-memory-model.md",
            "02-unsafe-code-verification.md",
            "03-layered-memory-model.md",
            "04-performance-optimization.md"
        ],
        "04-practical-applications": [
            "01-gpu-memory-management.md",
            "02-embedded-memory-management.md",
            "03-distributed-memory-management.md",
            "04-specialized-memory-management.md"
        ],
        "05-tools-and-debugging": [
            "01-memory-debugging-techniques.md",
            "02-memory-visualization-tools.md",
            "03-memory-leak-detection.md",
            "04-performance-profiling.md"
        ],
        "00-metadata": [
            "README.md",
            "INDEX.md",
            "GLOSSARY.md",
            "CROSS_REFERENCES.md",
            "CHANGELOG.md"
        ]
    }
    
    errors = []
    
    for directory, expected_files in expected_structure.items():
        if not os.path.exists(directory):
            errors.append(f"目录不存在: {directory}")
            continue
        
        actual_files = os.listdir(directory)
        for expected_file in expected_files:
            if expected_file not in actual_files:
                errors.append(f"文件缺失: {directory}/{expected_file}")
    
    if errors:
        print("验证失败，发现以下问题:")
        for error in errors:
            print(f"  - {error}")
        return False
    else:
        print("目录结构验证通过!")
        return True

if __name__ == "__main__":
    validate_structure()
```

### 5.2 内容验证

```python
#!/usr/bin/env python3

"""
内容验证脚本
用于验证文档内容的完整性和一致性
"""

def validate_content():
    """验证文档内容"""
    
    issues = []
    
    # 检查所有Markdown文件
    for root, dirs, files in os.walk('.'):
        for file in files:
            if file.endswith('.md'):
                file_path = os.path.join(root, file)
                issues.extend(check_file_content(file_path))
    
    if issues:
        print("内容验证发现问题:")
        for issue in issues:
            print(f"  - {issue}")
        return False
    else:
        print("内容验证通过!")
        return True

def check_file_content(file_path):
    """检查单个文件内容"""
    issues = []
    
    try:
        with open(file_path, 'r', encoding='utf-8') as f:
            content = f.read()
            
            # 检查是否有标题
            if not content.startswith('#'):
                issues.append(f"{file_path}: 缺少标题")
            
            # 检查是否有内容
            if len(content.strip()) < 100:
                issues.append(f"{file_path}: 内容过少")
            
            # 检查链接是否有效
            broken_links = check_broken_links(content, file_path)
            issues.extend(broken_links)
    
    except Exception as e:
        issues.append(f"{file_path}: 读取失败 - {e}")
    
    return issues

def check_broken_links(content, file_path):
    """检查损坏的链接"""
    issues = []
    
    # 查找所有链接
    link_pattern = r'\[([^\]]+)\]\(([^)]+)\)'
    matches = re.findall(link_pattern, content)
    
    for match in matches:
        link_text, link_url = match
        
        # 检查内部链接
        if link_url.endswith('.md'):
            if not os.path.exists(link_url):
                issues.append(f"{file_path}: 损坏的内部链接 {link_url}")
    
    return issues

if __name__ == "__main__":
    validate_content()
```

---

## 6. 使用说明

### 6.1 执行顺序

1. **创建目录结构**: 运行 `create_directories.sh` 或 `create_directories.ps1`
2. **迁移文件**: 运行各个迁移脚本
3. **整合内容**: 运行 `merge_theory_files.py` 和 `merge_practice_files.py`
4. **生成索引**: 运行 `generate_index.py` 和 `generate_cross_references.py`
5. **验证结果**: 运行 `validate_structure.py` 和 `validate_content.py`

### 6.2 注意事项

- 执行前请备份原始文件
- 确保有足够的磁盘空间
- 检查文件权限
- 验证脚本执行结果

### 6.3 回滚方案

如果重组过程中出现问题，可以使用以下命令回滚：

```bash
# 恢复原始文件
git checkout HEAD -- .

# 或者从备份恢复
cp -r backup/* .
```

这个重组脚本提供了完整的自动化工具，可以安全、高效地完成内存模型目录的重组工作。
