#!/bin/bash

# C12 WASM 项目快速设置脚本
# 用于快速设置开发环境

set -e

echo "🦀 C12 WASM 项目环境设置"
echo "========================"
echo ""

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# 检查命令是否存在
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# 打印成功消息
print_success() {
    echo -e "${GREEN}✓${NC} $1"
}

# 打印错误消息
print_error() {
    echo -e "${RED}✗${NC} $1"
}

# 打印警告消息
print_warning() {
    echo -e "${YELLOW}⚠${NC} $1"
}

# 1. 检查 Rust 安装
echo "📦 检查 Rust 安装..."
if command_exists rustc; then
    RUST_VERSION=$(rustc --version)
    print_success "Rust 已安装: $RUST_VERSION"
else
    print_error "Rust 未安装"
    echo "请运行以下命令安装 Rust:"
    echo "curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh"
    exit 1
fi

# 2. 检查 Rust 版本
echo ""
echo "🔍 检查 Rust 版本..."
RUST_VERSION=$(rustc --version | cut -d' ' -f2)
REQUIRED_VERSION="1.90.0"

if [ "$(printf '%s\n' "$REQUIRED_VERSION" "$RUST_VERSION" | sort -V | head -n1)" = "$REQUIRED_VERSION" ]; then
    print_success "Rust 版本满足要求 (>= $REQUIRED_VERSION)"
else
    print_warning "Rust 版本可能过低，建议升级到 $REQUIRED_VERSION 或更高版本"
    echo "运行: rustup update"
fi

# 3. 安装 WASM 目标
echo ""
echo "🎯 安装 WASM 编译目标..."

echo "  安装 wasm32-unknown-unknown..."
if rustup target add wasm32-unknown-unknown 2>/dev/null; then
    print_success "wasm32-unknown-unknown 已安装"
else
    print_warning "wasm32-unknown-unknown 可能已经安装"
fi

echo "  安装 wasm32-wasi..."
if rustup target add wasm32-wasi 2>/dev/null; then
    print_success "wasm32-wasi 已安装"
else
    print_warning "wasm32-wasi 可能已经安装"
fi

# 4. 安装 wasm-pack
echo ""
echo "📦 检查 wasm-pack..."
if command_exists wasm-pack; then
    WASM_PACK_VERSION=$(wasm-pack --version)
    print_success "wasm-pack 已安装: $WASM_PACK_VERSION"
else
    print_warning "wasm-pack 未安装，正在安装..."
    curl https://rustwasm.github.io/wasm-pack/installer/init.sh -sSf | sh
    print_success "wasm-pack 安装完成"
fi

# 5. 安装开发工具
echo ""
echo "🛠️  安装开发工具..."

echo "  安装 rustfmt..."
if rustup component add rustfmt 2>/dev/null; then
    print_success "rustfmt 已安装"
else
    print_warning "rustfmt 可能已经安装"
fi

echo "  安装 clippy..."
if rustup component add clippy 2>/dev/null; then
    print_success "clippy 已安装"
else
    print_warning "clippy 可能已经安装"
fi

# 6. 检查可选工具
echo ""
echo "🔧 检查可选工具..."

if command_exists wasmtime; then
    print_success "wasmtime 已安装"
else
    print_warning "wasmtime 未安装（可选）"
    echo "  安装: curl https://wasmtime.dev/install.sh -sSf | bash"
fi

if command_exists wasmedge; then
    print_success "WasmEdge 已安装"
else
    print_warning "WasmEdge 未安装（可选）"
    echo "  安装: curl -sSf https://raw.githubusercontent.com/WasmEdge/WasmEdge/master/utils/install.sh | bash"
fi

# 7. 构建项目
echo ""
echo "🏗️  构建项目..."
if cargo check --lib; then
    print_success "项目构建成功"
else
    print_error "项目构建失败"
    exit 1
fi

# 8. 运行测试
echo ""
echo "🧪 运行测试..."
if cargo test --lib; then
    print_success "测试通过"
else
    print_error "测试失败"
    exit 1
fi

# 9. 构建 WASM
echo ""
echo "🌐 构建 WASM 模块..."
if wasm-pack build --target web; then
    print_success "WASM 模块构建成功"
    echo "  输出目录: pkg/"
else
    print_error "WASM 模块构建失败"
    exit 1
fi

# 10. 完成
echo ""
echo "========================"
echo -e "${GREEN}✓ 环境设置完成！${NC}"
echo ""
echo "📚 下一步:"
echo "  1. 查看文档: cat README.md"
echo "  2. 运行测试: cargo test"
echo "  3. 运行示例: cargo run --example 01_basic_add"
echo "  4. 启动演示: python -m http.server 8080"
echo "     然后访问: http://localhost:8080/demo/"
echo ""
echo "🎉 开始愉快地编码吧！"
