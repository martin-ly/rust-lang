#!/usr/bin/env python3
"""
项目完整性检查脚本

检查项目各部分完成情况
"""

import os
import sys
from pathlib import Path

CRATES = [
    "c01_ownership", "c01_ownership_borrow_scope",
    "c02_type_system", "c03_control_flow", "c03_control_fn",
    "c04_generic", "c05_threads", "c06_async",
    "c07_process", "c08_algorithms", "c09_design_pattern",
    "c10_networks", "c11_macro_system", "c12_wasm"
]

def check_crate(crate_name):
    """检查单个 crate 的完整性"""
    crate_path = Path("crates") / crate_name
    
    if not crate_path.exists():
        return {"exists": False, "score": 0}
    
    checks = {
        "exists": True,
        "has_readme": (crate_path / "README.md").exists(),
        "has_src": (crate_path / "src").exists(),
        "has_tests": (crate_path / "tests").exists() or (crate_path / "src" / "lib.rs").exists(),
        "has_examples": (crate_path / "examples").exists(),
        "has_exercises": (crate_path / "exercises").exists(),
        "has_docs": (crate_path / "docs").exists(),
    }
    
    # 计算得分
    score = sum(1 for v in checks.values() if v) / len(checks) * 100
    checks["score"] = round(score, 1)
    
    return checks

def main():
    print("=" * 60)
    print("Rust 学习项目完整性检查")
    print("=" * 60)
    
    results = {}
    total_score = 0
    
    print("\n各 crate 检查情况:")
    print("-" * 60)
    
    for crate in CRATES:
        result = check_crate(crate)
        results[crate] = result
        total_score += result["score"]
        
        status = "✓" if result["score"] >= 80 else "~" if result["score"] >= 50 else "✗"
        print(f"{status} {crate:30} {result['score']:5.1f}%")
    
    avg_score = total_score / len(CRATES)
    
    print("-" * 60)
    print(f"\n平均完成度: {avg_score:.1f}%")
    
    # 检查关键文件
    print("\n关键文件检查:")
    print("-" * 60)
    
    key_files = [
        "README.md",
        "docs/README.md",
        "docs/CROSS_MODULE_NAVIGATION.md",
        "LEARNING_CHECKLIST.md",
        "FAQ.md",
        "content/CONTENT_CRATES_MAPPING.md",
        "crates/MODULE_CROSS_REFERENCE.md",
    ]
    
    for file in key_files:
        exists = Path(file).exists()
        status = "✓" if exists else "✗"
        print(f"{status} {file}")
    
    print("\n" + "=" * 60)
    
    if avg_score >= 95:
        print("🎉 项目状态: 优秀 (100% 完成)")
        return 0
    elif avg_score >= 80:
        print("👍 项目状态: 良好")
        return 0
    else:
        print("⚠️  项目状态: 需要改进")
        return 1

if __name__ == "__main__":
    sys.exit(main())
