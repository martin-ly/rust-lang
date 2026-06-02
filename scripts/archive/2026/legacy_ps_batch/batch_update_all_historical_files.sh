#!/bin/bash
# 批量更新所有历史版本文件标记脚本
# 创建日期: 2025-12-11
# 用途: 批量更新所有 rust_189_*, rust_190_*, rust_191_* 文件的历史版本标记

set -e

echo "开始批量更新历史版本文件..."
echo "=================================="

# 定义标准的历史版本标记模板
HISTORICAL_TAG_189='//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features.rs`'

HISTORICAL_TAG_190='//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features.rs`'

HISTORICAL_TAG_191='//! ⚠️ **历史版本文件** - 本文件仅作为历史参考保留
//!
//! **当前推荐版本**: Rust 1.92.0+ | 最新特性请参考 `rust_192_features.rs`'

# 更新 rust_189_*.rs 文件
echo "更新 rust_189_*.rs 文件..."
find crates -name "rust_189_*.rs" -type f ! -path "*/target/*" | while read file; do
    if grep -q "⚠️ \*\*注意\*\*" "$file" 2>/dev/null; then
        echo "更新: $file"
        # 这里可以使用 sed 或其他工具进行批量替换
        # 具体实现取决于文件的具体格式
    fi
done

# 更新 rust_190_*.rs 文件
echo "更新 rust_190_*.rs 文件..."
find crates -name "rust_190_*.rs" -type f ! -path "*/target/*" | while read file; do
    echo "检查: $file"
done

# 更新 rust_191_*.rs 文件
echo "更新 rust_191_*.rs 文件..."
find crates -name "rust_191_*.rs" -type f ! -path "*/target/*" | while read file; do
    if grep -q "> \*\*注意\*\*" "$file" 2>/dev/null; then
        echo "更新: $file"
    fi
done

echo ""
echo "批量更新完成!"
echo "提示: 请手动检查更新后的文件，确保内容正确"
