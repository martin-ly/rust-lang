#!/usr/bin/env python3
"""
修复示例文件名冲突问题
通过为每个 crate 的示例添加前缀来解决冲突
"""

import os
import shutil
from pathlib import Path

# 项目根目录
ROOT_DIR = Path("E:/_src/rust-lang")
CRATES_DIR = ROOT_DIR / "crates"

# 需要重命名的冲突示例
CONFLICTING_EXAMPLES = [
    "rust_193_features_demo.rs",
    "rust_192_features_demo.rs", 
    "rust_191_features_demo.rs",
    "rust_190_features_demo.rs",
    "performance_optimization_demo.rs",
]

def get_crate_prefix(crate_name: str) -> str:
    """从 crate 名称获取前缀"""
    return crate_name.split('_')[0]  # e.g., c01_ownership -> c01

def fix_examples_in_crate(crate_path: Path):
    """修复单个 crate 中的示例文件名"""
    crate_name = crate_path.name
    prefix = get_crate_prefix(crate_name)
    examples_dir = crate_path / "examples"
    
    if not examples_dir.exists():
        return
    
    for example_file in examples_dir.glob("*.rs"):
        if example_file.name in CONFLICTING_EXAMPLES:
            new_name = f"{prefix}_{example_file.name}"
            new_path = example_file.parent / new_name
            
            # 更新 Cargo.toml 中的示例配置
            cargo_toml = crate_path / "Cargo.toml"
            if cargo_toml.exists():
                content = cargo_toml.read_text(encoding='utf-8')
                old_name = example_file.name.replace('.rs', '')
                new_example_name = new_name.replace('.rs', '')
                
                # 替换示例配置中的名称
                content = content.replace(
                    f'name = "{old_name}"',
                    f'name = "{new_example_name}"'
                )
                content = content.replace(
                    f'path = "examples/{example_file.name}"',
                    f'path = "examples/{new_name}"'
                )
                cargo_toml.write_text(content, encoding='utf-8')
            
            # 重命名文件
            shutil.move(example_file, new_path)
            print(f"✅ 重命名: {crate_name}/examples/{example_file.name} -> {new_name}")

def main():
    print("🔧 开始修复示例文件名冲突...\n")
    
    for crate_dir in sorted(CRATES_DIR.iterdir()):
        if crate_dir.is_dir() and crate_dir.name.startswith('c'):
            fix_examples_in_crate(crate_dir)
    
    print("\n✅ 示例文件名修复完成")
    print("\n⚠️  注意: 如果有代码中引用这些示例，需要手动更新引用")

if __name__ == "__main__":
    main()
