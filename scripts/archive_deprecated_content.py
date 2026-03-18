#!/usr/bin/env python3
"""
过时内容归档脚本

自动识别并归档项目中的过时内容，保留历史记录但不再维护。

用法:
    python scripts/archive_deprecated_content.py [--dry-run]

选项:
    --dry-run    预览将要归档的内容，不实际执行
"""

import argparse
import os
import shutil
import sys
from datetime import datetime
from pathlib import Path

# 项目根目录
PROJECT_ROOT = Path(__file__).parent.parent

# 不应归档的文件 (最新文档)
EXCLUDE_FILES = {
    "2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW.md",
    "SUSTAINABLE_DEVELOPMENT_PLAN_2026.md", 
    "PROJECT_COMPREHENSIVE_REVIEW_AND_ROADMAP_2026.md",
    "MIGRATION_GUIDE_2026.md",
    "RUST_194_MIGRATION_GUIDE.md",
    "FINAL_COMPLETION_REPORT.md",
    "ARCHIVE_EXECUTION_SUMMARY.md",
    "README.md",
}

# 过时内容模式 (路径, 归档原因)
DEPRECATED_PATTERNS = [
    # 过时的代码模式文档
    ("docs/**/async_trait_*.md", "async-trait crate不再需要，Rust原生支持"),
    ("docs/**/lazy_static_*.md", "使用std::sync::LazyLock替代"),
    ("docs/**/futures_01_*.md", "futures 0.1已废弃，使用0.3"),
    ("docs/**/rls_*.md", "RLS已停止维护，使用rust-analyzer"),
    
    # 过时的工具指南
    ("docs/**/cargo_workspace_2021*.md", "Workspace配置已更新"),
    ("docs/**/edition_2021*.md", "Edition 2024已发布"),
    
    # 过时的Rust版本
    ("docs/**/rust_1.8[0-9]_*.md", "Rust 1.90+版本已可用"),
    ("docs/**/rust_1.7[0-9]_*.md", "Rust 1.90+版本已可用"),
    
    # 需要更新的内容
    ("docs/archive/deprecated/*", "已在deprecated目录，无需处理"),
]

# 需要保留但不维护的内容
PRESERVE_PATTERNS = [
    "docs/archive/**",
    "examples/archive/**",
    "crates/*/archive/**",
]


def find_deprecated_files():
    """查找需要归档的过时文件"""
    deprecated_files = []
    
    # 查找过时的代码示例
    for pattern, reason in DEPRECATED_PATTERNS:
        if "**" in pattern:
            # 处理通配符模式
            parts = pattern.split("/**/")
            base = PROJECT_ROOT / parts[0]
            if base.exists():
                for path in base.rglob(parts[1] if len(parts) > 1 else "*"):
                    if path.is_file() and "archive" not in str(path.relative_to(PROJECT_ROOT)):
                        deprecated_files.append((path, reason))
    
    # 检查特定的过时模式
    deprecated_patterns = [
        ("lazy_static::lazy_static!", "使用std::sync::LazyLock替代lazy_static crate"),
        ("#[async_trait]", "Rust 1.75+原生支持async trait，无需crate"),
        ("async_trait::", "Rust 1.75+原生支持async trait，无需crate"),
        ("futures 0.1", "futures 0.1已废弃，升级到0.3"),
        ("futures01", "futures 0.1已废弃，升级到0.3"),
        ("edition = \"2018\"", "Edition 2024已可用，建议升级"),
        ("edition=\"2018\"", "Edition 2024已可用，建议升级"),
    ]
    
    for root, dirs, files in os.walk(PROJECT_ROOT / "docs"):
        # 跳过已归档的目录
        if "archive" in Path(root).parts:
            continue
            
        for file in files:
            if file.endswith(".md"):
                # 跳过不应归档的文件
                if file in EXCLUDE_FILES:
                    continue
                    
                file_path = Path(root) / file
                try:
                    content = file_path.read_text(encoding='utf-8', errors='ignore')
                    
                    for pattern, reason in deprecated_patterns:
                        if pattern in content:
                            deprecated_files.append((file_path, reason))
                            break
                except Exception:
                    pass
    
    return deprecated_files


def archive_files(files, dry_run=False):
    """归档文件到archive目录"""
    archive_dir = PROJECT_ROOT / "docs" / "archive" / f"deprecated_{datetime.now().strftime('%Y%m%d')}"
    
    if not dry_run:
        archive_dir.mkdir(parents=True, exist_ok=True)
        
        # 创建归档说明
        readme = archive_dir / "README.md"
        readme.write_text(f"""# 归档内容说明

**归档日期**: {datetime.now().isoformat()}

## 归档原因

以下文件包含过时的内容，已被归档但保留供历史参考：

| 文件 | 归档原因 | 替代方案 |
|------|---------|---------|
""", encoding='utf-8')
    
    archived_count = 0
    
    for file_path, reason in files:
        rel_path = file_path.relative_to(PROJECT_ROOT)
        target_path = archive_dir / rel_path.name
        
        print(f"{'[DRY RUN] ' if dry_run else ''}归档: {rel_path}")
        print(f"         原因: {reason}")
        
        if not dry_run:
            # 复制文件到归档目录
            shutil.copy2(file_path, target_path)
            
            # 在原位置添加重定向说明
            redirect_content = f"""# 内容已归档

> **注意**: 此文档内容已过时，已于 {datetime.now().strftime('%Y-%m-%d')} 归档。

## 归档原因

{reason}

## 替代资源

- 最新文档: [ docs/05_guides/ ]
- 归档位置: `{archive_dir.relative_to(PROJECT_ROOT)}/{file_path.name}`

---

**状态**: ⚠️ 已归档
"""
            file_path.write_text(redirect_content, encoding='utf-8')
            
            # 更新归档说明
            with open(readme, 'a', encoding='utf-8') as f:
                f.write(f"| {rel_path} | {reason} | 见替代资源 |\n")
        
        archived_count += 1
    
    return archived_count


def generate_migration_guide():
    """生成迁移指南"""
    guide_path = PROJECT_ROOT / "docs" / "MIGRATION_GUIDE_2026.md"
    
    guide_content = """# 2026年迁移指南

> **日期**: 2026-03-18  
> **目标**: 从旧版Rust工具链迁移到最新生态

## 迁移清单

### 1. 工具链更新

```bash
# 更新Rust到1.94.0
rustup update stable
rustup default 1.94.0

# 安装/更新工具
rustup component add rustfmt clippy rust-analyzer
cargo install cargo-update cargo-tree cargo-outdated
```

### 2. 代码现代化

#### lazy_static → LazyLock

```rust
// 旧代码
use lazy_static::lazy_static;
lazy_static! {
    static ref CONFIG: String = load_config();
}

// 新代码
use std::sync::LazyLock;
static CONFIG: LazyLock<String> = LazyLock::new(|| load_config());
```

#### async-trait → 原生async trait

```rust
// 旧代码
#[async_trait::async_trait]
trait Storage {
    async fn read(&self) -> Vec<u8>;
}

// 新代码 (Rust 1.75+)
trait Storage {
    async fn read(&self) -> Vec<u8>;
}
```

#### 生成器 → gen关键字

```rust
// 旧代码 (不稳定特性)
#![feature(generators)]
|| { yield 1; }

// 新代码 (Edition 2024)
gen fn my_gen() -> i32 { yield 1; }
```

### 3. 配置更新

#### Cargo.toml

```toml
[package]
edition = "2024"  # 升级到2024
rust-version = "1.94"

[lints.clippy]
all = { level = "warn", priority = -1 }
correctness = "deny"
```

### 4. CI/CD更新

```yaml
# 更新actions版本
- uses: actions/checkout@v4
- uses: dtolnay/rust-toolchain@stable
  with:
    toolchain: "1.94.0"
    components: rustfmt, clippy
```

---

**详细指南**: [2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW.md](./2026_RUST_ECOSYSTEM_COMPREHENSIVE_REVIEW.md)
"""
    
    guide_path.write_text(guide_content, encoding='utf-8')
    print(f"生成迁移指南: {guide_path}")


def main():
    parser = argparse.ArgumentParser(description="归档过时内容")
    parser.add_argument("--dry-run", action="store_true", help="预览不执行")
    args = parser.parse_args()
    
    print("=" * 60)
    print("Rust项目过时内容归档工具")
    print("=" * 60)
    
    if args.dry_run:
        print("\n[预览模式] 不会实际修改文件\n")
    
    # 查找过时文件
    print("\n1. 查找过时文件...")
    deprecated_files = find_deprecated_files()
    print(f"   找到 {len(deprecated_files)} 个需要归档的文件")
    
    if not deprecated_files:
        print("\n✅ 没有需要归档的过时内容")
        return
    
    # 归档文件
    print("\n2. 归档文件...")
    count = archive_files(deprecated_files, dry_run=args.dry_run)
    
    # 生成迁移指南
    if not args.dry_run:
        print("\n3. 生成迁移指南...")
        generate_migration_guide()
    
    print("\n" + "=" * 60)
    if args.dry_run:
        print(f"预览完成，{count} 个文件将被归档")
        print("运行时不加 --dry-run 执行实际归档")
    else:
        print(f"✅ 完成，已归档 {count} 个文件")
    print("=" * 60)


if __name__ == "__main__":
    main()
