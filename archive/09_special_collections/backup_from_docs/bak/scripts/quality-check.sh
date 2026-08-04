#!/bin/bash
# Rust项目质量检查脚本
# 创建时间: 2025年9月25日 13:05

echo "🔍 开始Rust项目质量检查..."
echo "检查时间: $(date)"
echo "================================"

# 1. 代码格式检查
echo "📝 检查代码格式..."
cargo fmt --all -- --check
if [ $? -eq 0 ]; then
    echo "✅ 代码格式检查通过"
else
    echo "❌ 代码格式检查失败"
    echo "请运行: cargo fmt --all"
fi

# 2. 代码质量检查
echo "🔧 检查代码质量..."
cargo clippy --all-targets --all-features -- -D warnings
if [ $? -eq 0 ]; then
    echo "✅ 代码质量检查通过"
else
    echo "❌ 代码质量检查失败"
    echo "请修复Clippy警告"
fi

# 3. 单元测试
echo "🧪 运行单元测试..."
cargo test --all
if [ $? -eq 0 ]; then
    echo "✅ 单元测试通过"
else
    echo "❌ 单元测试失败"
    echo "请修复失败的测试"
fi

# 4. 文档生成检查
echo "📚 检查文档生成..."
cargo doc --all --no-deps
if [ $? -eq 0 ]; then
    echo "✅ 文档生成成功"
else
    echo "❌ 文档生成失败"
    echo "请修复文档错误"
fi

# 5. 检查死链接
echo "🔗 检查文档死链接..."
if command -v cargo-deadlinks &> /dev/null; then
    cargo deadlinks
    if [ $? -eq 0 ]; then
        echo "✅ 文档链接检查通过"
    else
        echo "❌ 发现死链接"
        echo "请修复文档链接"
    fi
else
    echo "⚠️  cargo-deadlinks未安装，跳过链接检查"
    echo "安装命令: cargo install cargo-deadlinks"
fi

echo "================================"
echo "🎉 质量检查完成!"
echo "完成时间: $(date)"
