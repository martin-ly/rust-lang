#!/bin/bash
# scripts/generate_docs.sh - 生成 C10 Networks API 文档

set -e

echo "🚀 生成 C10 Networks API 文档..."

# 检查 Rust 工具链
if ! command -v cargo &> /dev/null; then
    echo "❌ 错误: 未找到 cargo 命令"
    echo "请安装 Rust 工具链: https://rustup.rs/"
    exit 1
fi

# 检查 Rust 版本
RUST_VERSION=$(cargo --version | cut -d' ' -f2)
echo "📦 Rust 版本: $RUST_VERSION"

# 清理之前的文档
echo "🧹 清理之前的文档..."
rm -rf target/doc

# 生成基础文档
echo "📚 生成基础文档..."
cargo doc --no-deps --document-private-items

# 生成特性文档
echo "🔧 生成特性文档..."
cargo doc --features "sniff,tls,offline,pcap_live" --no-deps --document-private-items

# 生成示例文档
echo "📖 生成示例文档..."
cargo doc --examples --no-deps

# 生成基准测试文档
echo "📊 生成基准测试文档..."
cargo doc --benches --no-deps

# 生成测试文档
echo "🧪 生成测试文档..."
cargo doc --tests --no-deps

# 检查文档生成结果
if [ -d "target/doc/c10_networks" ]; then
    echo "✅ 文档生成成功！"
    echo "📖 查看文档: file://$(pwd)/target/doc/c10_networks/index.html"
    
    # 统计文档信息
    DOC_SIZE=$(du -sh target/doc/c10_networks | cut -f1)
    echo "📊 文档大小: $DOC_SIZE"
    
    # 检查文档覆盖率
    echo "🔍 检查文档覆盖率..."
    MISSING_DOCS=$(cargo doc --document-private-items --no-deps 2>&1 | grep -c "warning.*missing.*docs" || true)
    if [ "$MISSING_DOCS" -gt 0 ]; then
        echo "⚠️  发现 $MISSING_DOCS 个缺失的文档注释"
    else
        echo "✅ 文档覆盖率良好"
    fi
    
    # 检查链接有效性
    echo "🔗 检查文档链接..."
    UNRESOLVED_LINKS=$(cargo doc --document-private-items --no-deps 2>&1 | grep -c "warning.*unresolved.*link" || true)
    if [ "$UNRESOLVED_LINKS" -gt 0 ]; then
        echo "⚠️  发现 $UNRESOLVED_LINKS 个未解析的链接"
    else
        echo "✅ 文档链接有效"
    fi
    
else
    echo "❌ 文档生成失败"
    exit 1
fi

echo "🎉 文档生成完成！"
echo ""
echo "📋 可用命令:"
echo "  cargo doc --open          # 生成并打开文档"
echo "  cargo doc --all-features  # 生成包含所有特性的文档"
echo "  cargo doc --examples      # 生成示例文档"
echo "  cargo doc --benches       # 生成基准测试文档"
echo "  cargo doc --tests         # 生成测试文档"
