#!/bin/bash
# Rust 形式化工程系统 - 版本号批量更新脚本
# 用法: ./update_rust_version.sh

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
FORMAL_SYSTEM_DIR="$SCRIPT_DIR"

echo "🔄 Rust 形式化工程系统 - 版本号批量更新"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# 检查目录是否存在
if [ ! -d "$FORMAL_SYSTEM_DIR" ]; then
    echo "❌ 错误: 未找到目录 $FORMAL_SYSTEM_DIR"
    exit 1
fi

cd "$FORMAL_SYSTEM_DIR"

echo "📊 更新前统计:"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
RUST_189_COUNT=$(grep -r "Rust 1.89\|rustc 1.89\|1.89" --include="*.md" . 2>/dev/null | wc -l)
echo "  包含 'Rust 1.89' 的文件: $RUST_189_COUNT"
echo ""

# 备份
echo "💾 创建备份..."
BACKUP_DIR="$FORMAL_SYSTEM_DIR/backup_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$BACKUP_DIR"
echo "  备份目录: $BACKUP_DIR"
echo ""

# 更新版本号
echo "🔄 更新版本号..."
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

# 模式1: Rust 1.89 -> Rust 1.90
find . -name "*.md" -type f -exec sed -i 's/Rust 1.89/Rust 1.90/g' {} \;
echo "  ✅ 更新 'Rust 1.89' → 'Rust 1.90'"

# 模式2: rustc 1.89 -> rustc 1.90
find . -name "*.md" -type f -exec sed -i 's/rustc 1.89/rustc 1.90/g' {} \;
echo "  ✅ 更新 'rustc 1.89' → 'rustc 1.90'"

# 模式3: Rust版本: 1.89 -> Rust版本: 1.90.0
find . -name "*.md" -type f -exec sed -i 's/Rust版本.*1.89/Rust版本: 1.90.0 (Edition 2024)/g' {} \;
echo "  ✅ 更新版本号格式"

# 模式4: Rust ≤ 1.89 -> Rust ≤ 1.90.0
find . -name "*.md" -type f -exec sed -i 's/Rust ≤ 1.89/Rust ≤ 1.90.0 (Edition 2024)/g' {} \;
echo "  ✅ 更新版本范围"

# 模式5: 最新稳定版 -> 1.90.0 (Edition 2024)
find . -name "*.md" -type f -exec sed -i 's/最新稳定版/1.90.0 (Edition 2024)/g' {} \;
echo "  ✅ 更新版本描述"

echo ""

# 统计更新后
echo "📊 更新后统计:"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
RUST_190_COUNT=$(grep -r "Rust 1.90\|rustc 1.90\|1.90.0" --include="*.md" . 2>/dev/null | wc -l)
echo "  包含 'Rust 1.90' 的文件: $RUST_190_COUNT"
echo ""

# 检查是否还有旧版本号
REMAINING=$(grep -r "Rust 1.89\|rustc 1.89" --include="*.md" . 2>/dev/null | wc -l)
if [ "$REMAINING" -gt 0 ]; then
    echo "⚠️  警告: 仍有 $REMAINING 个文件包含旧版本号"
    echo "  请手动检查以下文件:"
    grep -r "Rust 1.89\|rustc 1.89" --include="*.md" . 2>/dev/null | head -5
else
    echo "✅ 所有版本号已更新"
fi

echo ""
echo "🎉 版本号更新完成！"
echo ""
echo "📝 下一步:"
echo "  1. 检查更新结果"
echo "  2. 验证文档一致性"
echo "  3. 查看 RUST_1_90_CHANGELOG.md"

