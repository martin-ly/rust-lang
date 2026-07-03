#!/bin/bash
# Miri 测试运行脚本
# 用于运行所有 Miri 测试并检测未定义行为

set -e

echo "=========================================="
echo "    Miri 测试运行脚本"
echo "=========================================="
echo ""

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# 检查 Miri 是否安装
echo "[1/4] 检查 Miri 安装..."
if ! rustup component list --installed | grep -q miri; then
    echo "${YELLOW}Miri 未安装，正在安装...${NC}"
    rustup component add miri
else
    echo "${GREEN}Miri 已安装${NC}"
fi

# 设置 Miri
echo ""
echo "[2/4] 设置 Miri 环境..."
cargo miri setup

# 设置 Miri 环境变量
# -Zmiri-tree-borrows: 使用 Tree Borrows 模型（推荐）
# -Zmiri-tag-raw-pointers: 标记裸指针
# -Zmiri-disable-isolation: 禁用隔离（允许文件系统访问等）
export MIRIFLAGS="-Zmiri-tree-borrows -Zmiri-disable-isolation"

echo "MIRIFLAGS: $MIRIFLAGS"

# 运行测试
echo ""
echo "[3/4] 运行 Miri 测试..."
echo ""

# 函数：运行单个 crate 的测试
run_crate_tests() {
    local crate_name=$1
    echo "------------------------------------------"
    echo "测试 crate: $crate_name"
    echo "------------------------------------------"
    
    if cargo miri test -p "$crate_name" --lib -- miri_tests 2>&1; then
        echo "${GREEN}✓ $crate_name 测试通过${NC}"
    else
        echo "${RED}✗ $crate_name 测试失败${NC}"
        return 1
    fi
    echo ""
}

# 运行所有包含 miri_tests 的 crate
CRATES=(
    "c01_ownership_borrow_scope"
    "c02_type_system"
    "c03_control_fn"
    "c04_generic"
    "c05_threads"
    "c06_async"
    "c07_process"
    "c08_algorithms"
    "c09_design_pattern"
    "c10_networks"
    "c12_wasm"
)

FAILED=0
for crate in "${CRATES[@]}"; do
    if ! run_crate_tests "$crate"; then
        FAILED=1
    fi
done

# 总结
echo ""
echo "=========================================="
echo "[4/4] 测试总结"
echo "=========================================="

if [ $FAILED -eq 0 ]; then
    echo "${GREEN}✓ 所有 Miri 测试通过！${NC}"
    echo ""
    echo "测试说明:"
    echo "  - 使用了 Tree Borrows 模型"
    echo "  - 检测了内存安全问题"
    echo "  - 验证了 unsafe 代码的正确性"
    exit 0
else
    echo "${RED}✗ 部分测试失败${NC}"
    echo ""
    echo "可能的错误类型:"
    echo "  - Use-after-free: 使用已释放的内存"
    echo "  - Data race: 数据竞争"
    echo "  - Invalid memory access: 无效内存访问"
    echo "  - Alignment violation: 对齐违规"
    exit 1
fi
