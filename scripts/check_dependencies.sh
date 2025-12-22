#!/bin/bash
# 依赖更新检查脚本
# 创建日期: 2025-12-11
# 用途: 检查项目依赖的可用更新

set -e

echo "=========================================="
echo "依赖更新检查脚本"
echo "=========================================="
echo ""

# 颜色定义
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m' # No Color

# 1. 检查可用更新
echo -e "${GREEN}[1/4]${NC} 检查可用更新..."
cargo update --dry-run 2>&1 | grep -E "Updating|Locking|Unchanged" || true
echo ""

# 2. 详细检查
echo -e "${GREEN}[2/4]${NC} 详细检查可用更新..."
cargo update --verbose 2>&1 | grep -E "Unchanged.*available" || echo "所有依赖都是最新版本"
echo ""

# 3. 检查安全漏洞
echo -e "${GREEN}[3/4]${NC} 检查安全漏洞..."
if command -v cargo-audit &> /dev/null; then
    cargo audit || echo -e "${YELLOW}警告: 发现安全漏洞，请查看详细报告${NC}"
else
    echo -e "${YELLOW}警告: cargo-audit 未安装，跳过安全检查${NC}"
    echo "安装命令: cargo install cargo-audit"
fi
echo ""

# 4. 检查过时依赖
echo -e "${GREEN}[4/4]${NC} 检查过时依赖..."
if command -v cargo-outdated &> /dev/null; then
    cargo outdated || true
else
    echo -e "${YELLOW}警告: cargo-outdated 未安装，跳过过时依赖检查${NC}"
    echo "安装命令: cargo install cargo-outdated"
fi
echo ""

echo "=========================================="
echo "检查完成！"
echo "=========================================="
echo ""
echo "待迁移的依赖请查看: DEPENDENCY_UPDATE_CHECK.md"
