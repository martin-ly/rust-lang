#!/bin/bash

# C12 WASM 全平台构建脚本
# 构建所有目标平台的 WASM 模块

set -e

echo "🚀 C12 WASM 全平台构建"
echo "====================="
echo ""

# 颜色定义
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
NC='\033[0m'

print_step() {
    echo -e "${BLUE}▶${NC} $1"
}

print_success() {
    echo -e "${GREEN}✓${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}⚠${NC} $1"
}

# 1. 清理之前的构建
print_step "清理之前的构建..."
cargo clean
rm -rf pkg/
rm -rf target/
print_success "清理完成"
echo ""

# 2. 格式化代码
print_step "格式化代码..."
cargo fmt --all
print_success "代码格式化完成"
echo ""

# 3. Clippy 检查
print_step "运行 Clippy 检查..."
cargo clippy --all-targets --all-features -- -D warnings
print_success "Clippy 检查通过"
echo ""

# 4. 运行测试
print_step "运行测试套件..."
cargo test --lib
print_success "测试通过"
echo ""

# 5. 构建 WASM (浏览器)
print_step "构建 WASM 模块 (浏览器目标)..."
wasm-pack build --target web --out-dir pkg/web
print_success "浏览器 WASM 构建完成"
echo ""

print_step "构建 WASM 模块 (Node.js 目标)..."
wasm-pack build --target nodejs --out-dir pkg/nodejs
print_success "Node.js WASM 构建完成"
echo ""

print_step "构建 WASM 模块 (Bundler 目标)..."
wasm-pack build --target bundler --out-dir pkg/bundler
print_success "Bundler WASM 构建完成"
echo ""

# 6. 构建 WASI
print_step "构建 WASI 模块..."
cargo build --target wasm32-wasi --release
print_success "WASI 模块构建完成"
echo ""

# 7. 运行 WASI 测试
print_step "运行 WASI 测试..."
cargo test --target wasm32-wasi
print_success "WASI 测试通过"
echo ""

# 8. 优化 WASM 大小（如果 wasm-opt 可用）
if command -v wasm-opt >/dev/null 2>&1; then
    print_step "优化 WASM 二进制大小..."

    for target in web nodejs bundler; do
        if [ -f "pkg/$target/c12_wasm_bg.wasm" ]; then
            echo "  优化 pkg/$target/c12_wasm_bg.wasm..."
            wasm-opt -Oz -o "pkg/$target/c12_wasm_bg_opt.wasm" "pkg/$target/c12_wasm_bg.wasm"

            # 显示大小对比
            ORIGINAL_SIZE=$(stat -f%z "pkg/$target/c12_wasm_bg.wasm" 2>/dev/null || stat -c%s "pkg/$target/c12_wasm_bg.wasm")
            OPTIMIZED_SIZE=$(stat -f%z "pkg/$target/c12_wasm_bg_opt.wasm" 2>/dev/null || stat -c%s "pkg/$target/c12_wasm_bg_opt.wasm")
            REDUCTION=$((100 - (OPTIMIZED_SIZE * 100 / ORIGINAL_SIZE)))

            echo "    原始大小: $ORIGINAL_SIZE 字节"
            echo "    优化后: $OPTIMIZED_SIZE 字节"
            echo "    减小: $REDUCTION%"
        fi
    done

    print_success "WASM 优化完成"
    echo ""
else
    print_warning "wasm-opt 未安装，跳过优化步骤"
    echo "  安装: npm install -g wasm-opt"
    echo ""
fi

# 9. 构建文档
print_step "构建文档..."
cargo doc --no-deps --all-features
print_success "文档构建完成"
echo ""

# 10. 运行基准测试（可选）
if [ "$1" = "--bench" ]; then
    print_step "运行基准测试..."
    cargo bench --no-fail-fast
    print_success "基准测试完成"
    echo ""
fi

# 11. 生成构建报告
print_step "生成构建报告..."

echo "构建报告" > BUILD_REPORT.txt
echo "========" >> BUILD_REPORT.txt
echo "" >> BUILD_REPORT.txt
echo "构建时间: $(date)" >> BUILD_REPORT.txt
echo "Rust 版本: $(rustc --version)" >> BUILD_REPORT.txt
echo "" >> BUILD_REPORT.txt
echo "构建产物:" >> BUILD_REPORT.txt
echo "" >> BUILD_REPORT.txt

# Web 目标
if [ -d "pkg/web" ]; then
    echo "Web 目标:" >> BUILD_REPORT.txt
    ls -lh pkg/web/*.wasm | awk '{print "  " $9 ": " $5}' >> BUILD_REPORT.txt
    echo "" >> BUILD_REPORT.txt
fi

# Node.js 目标
if [ -d "pkg/nodejs" ]; then
    echo "Node.js 目标:" >> BUILD_REPORT.txt
    ls -lh pkg/nodejs/*.wasm | awk '{print "  " $9 ": " $5}' >> BUILD_REPORT.txt
    echo "" >> BUILD_REPORT.txt
fi

# WASI 目标
if [ -f "target/wasm32-wasi/release/c12_wasm.wasm" ]; then
    echo "WASI 目标:" >> BUILD_REPORT.txt
    ls -lh target/wasm32-wasi/release/*.wasm | awk '{print "  " $9 ": " $5}' >> BUILD_REPORT.txt
    echo "" >> BUILD_REPORT.txt
fi

print_success "构建报告已生成: BUILD_REPORT.txt"
echo ""

# 完成
echo "====================="
echo -e "${GREEN}✓ 所有构建完成！${NC}"
echo ""
echo "📦 构建产物:"
echo "  - pkg/web/          - 浏览器 WASM"
echo "  - pkg/nodejs/       - Node.js WASM"
echo "  - pkg/bundler/      - Bundler WASM"
echo "  - target/wasm32-wasi/ - WASI 模块"
echo "  - target/doc/       - API 文档"
echo ""
echo "📊 查看构建报告: cat BUILD_REPORT.txt"
echo ""
echo "🎉 构建成功！"
