#!/usr/bin/env python3
"""
修复 CI 配置中的 Rust 版本
"""

from pathlib import Path

# 项目根目录
ROOT_DIR = Path("E:/_src/rust-lang")
CI_FILE = ROOT_DIR / ".github" / "workflows" / "ci.yml"

def fix_ci_version():
    """修复 CI 文件中的 Rust 版本"""
    
    if not CI_FILE.exists():
        print(f"❌ CI 文件不存在: {CI_FILE}")
        return
    
    content = CI_FILE.read_text(encoding='utf-8')
    
    # 检查当前版本
    if 'RUST_VERSION: 1.94.0' in content:
        print("✅ CI 配置已经是 Rust 1.94.0")
        return
    
    # 替换版本号
    old_content = content
    content = content.replace('RUST_VERSION: 1.92.0', 'RUST_VERSION: 1.94.0')
    content = content.replace('toolchain: 1.92.0', 'toolchain: 1.94.0')
    
    if content != old_content:
        CI_FILE.write_text(content, encoding='utf-8')
        print("✅ 已将 CI Rust 版本更新为 1.94.0")
    else:
        print("⚠️ 未找到需要更新的版本号")

def enhance_ci():
    """增强 CI 配置，添加更多检查"""
    
    if not CI_FILE.exists():
        return
    
    content = CI_FILE.read_text(encoding='utf-8')
    
    # 检查是否已有增强的检查
    if 'cargo clippy' in content:
        print("✅ CI 配置已有 clippy 检查")
        return
    
    # 在测试命令后添加更多检查
    enhanced_steps = """      - run: cargo build --workspace --verbose
      - run: cargo test --workspace --verbose
      - run: cargo clippy --workspace -- -D warnings
      - run: cargo fmt --all -- --check
      - run: cargo doc --workspace --no-deps"""
    
    old_steps = """      - run: cargo build --workspace --verbose
      - run: cargo test --workspace --verbose"""
    
    if old_steps in content:
        content = content.replace(old_steps, enhanced_steps)
        CI_FILE.write_text(content, encoding='utf-8')
        print("✅ 已增强 CI 配置，添加 clippy, fmt, doc 检查")
    else:
        print("⚠️ 无法自动增强 CI 配置，请手动添加")

def main():
    print("🔧 开始修复 CI 配置...\n")
    
    fix_ci_version()
    enhance_ci()
    
    print("\n✅ CI 配置修复完成")

if __name__ == "__main__":
    main()
