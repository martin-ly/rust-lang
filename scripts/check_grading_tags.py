#!/usr/bin/env python3
"""
分级标签自动化检查：
验证每个 concept/ 文件是否包含 `**受众**:` 和 `**内容分级**:` 标签。
CI 可运行此脚本阻断无标签 PR。
"""

import sys
from pathlib import Path

CONCEPT_DIR = Path("concept")
VALID_AUDIENCES = {"[初学者]", "[进阶]", "[专家]", "[研究者]"}
VALID_GRADINGS = {"[综述级]", "[实验级]", "[专家级]", "[研究者级]"}


def check_file(md_path: Path) -> list:
    content = md_path.read_text(encoding="utf-8", errors="ignore")
    rel = str(md_path.relative_to(CONCEPT_DIR)).replace("\\", "/")
    errors = []
    
    # 检查受众标签
    if "**受众**:" not in content:
        errors.append(f"{rel}: 缺少 **受众** 标签")
    else:
        # 提取标签值
        for line in content.splitlines()[:50]:
            if "**受众**:" in line:
                if not any(v in line for v in VALID_AUDIENCES):
                    errors.append(f"{rel}: **受众** 标签值无效 ({line.strip()})")
                break
    
    # 检查内容分级标签
    if "**内容分级**:" not in content:
        errors.append(f"{rel}: 缺少 **内容分级** 标签")
    else:
        for line in content.splitlines()[:50]:
            if "**内容分级**:" in line:
                if not any(v in line for v in VALID_GRADINGS):
                    errors.append(f"{rel}: **内容分级** 标签值无效 ({line.strip()})")
                break
    
    return errors


def main():
    files = sorted(CONCEPT_DIR.rglob("*.md"))
    files = [f for f in files if "archive" not in str(f) and "sources" not in str(f)]
    
    all_errors = []
    for md_path in files:
        all_errors.extend(check_file(md_path))
    
    print(f"检查完成: {len(files)} 个文件")
    if all_errors:
        print(f"❌ 发现 {len(all_errors)} 个问题:")
        for e in all_errors:
            print(f"  - {e}")
        sys.exit(1)
    else:
        print("✅ 所有文件均包含有效的双标签")
        sys.exit(0)


if __name__ == "__main__":
    main()
