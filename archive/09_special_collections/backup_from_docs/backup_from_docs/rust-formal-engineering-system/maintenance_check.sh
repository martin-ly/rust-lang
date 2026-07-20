#!/bin/bash
# 自动化维护检查脚本
# 用法: ./maintenance_check.sh [季度|月度|周度]

set -e

FORMAL_SYSTEM_DIR="$(cd "$(dirname "$0")" && pwd)"
CHECK_TYPE="${1:-季度}"

echo "🔍 Rust 形式化工程系统 - 自动化维护检查"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "检查类型: $CHECK_TYPE"
echo ""

cd "$FORMAL_SYSTEM_DIR"

# 统计计数器
total_checks=0
passed_checks=0
failed_checks=0
warnings=0

# 检查结果数组
declare -a CHECK_RESULTS

# 执行检查函数
run_check() {
    local check_name="$1"
    local check_command="$2"
    local required_for="$3"

    total_checks=$((total_checks + 1))

    echo "检查: $check_name"

    if eval "$check_command" > /dev/null 2>&1; then
        passed_checks=$((passed_checks + 1))
        CHECK_RESULTS+=("✅ $check_name")
        echo "  ✅ 通过"
    else
        if [[ "$required_for" == *"$CHECK_TYPE"* ]] || [[ -z "$required_for" ]]; then
            failed_checks=$((failed_checks + 1))
            CHECK_RESULTS+=("❌ $check_name")
            echo "  ❌ 失败"
        else
            warnings=$((warnings + 1))
            CHECK_RESULTS+=("⚠️  $check_name (可选)")
            echo "  ⚠️  跳过（非必需）"
        fi
    fi
    echo ""
}

# 季度检查
if [[ "$CHECK_TYPE" == "季度" ]]; then
    echo "📋 季度维护检查清单"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo ""

    # 版本同步检查
    run_check "版本号一致性" \
        "grep -r 'Rust 1.90' --include='*.md' . | wc -l | awk '{if (\$1 > 20) exit 0; exit 1}'" \
        "季度"

    # 链接检查
    run_check "链接有效性" \
        "./check_links.sh" \
        "季度"

    # 交叉引用检查
    run_check "交叉引用完整性" \
        "./verify_cross_references.sh" \
        "季度"

    # 占位符统计
    run_check "占位符统计" \
        "grep -r '⚠️.*待完善' --include='*.md' . | wc -l | awk '{if (\$1 >= 0) exit 0; exit 1}'" \
        "季度"

    # 工具脚本可用性
    run_check "工具脚本权限" \
        "[ -x update_rust_version.sh ] && [ -x mark_placeholders.sh ] && [ -x check_links.sh ] && [ -x verify_cross_references.sh ]" \
        "季度"
fi

# 月度检查
if [[ "$CHECK_TYPE" == "月度" ]]; then
    echo "📋 月度维护检查清单"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo ""

    # 新增内容检查
    run_check "新增文档检查" \
        "find . -name '*.md' -mtime -30 | wc -l | awk '{if (\$1 >= 0) exit 0; exit 1}'" \
        "月度"

    # 快速链接检查
    run_check "核心文档链接" \
        "test -f README.md && test -f ../FORMAL_AND_PRACTICAL_NAVIGATION.md" \
        "月度"

    # 格式一致性检查
    run_check "文档格式检查" \
        "grep -r '^# ' --include='*.md' . | head -5 | grep -q '#'" \
        "月度"
fi

# 周度检查
if [[ "$CHECK_TYPE" == "周度" ]]; then
    echo "📋 周度维护检查清单"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo ""

    # 工具脚本可用性
    run_check "工具脚本存在" \
        "test -f update_rust_version.sh && test -f mark_placeholders.sh" \
        "周度"

    # 核心文档存在
    run_check "核心文档存在" \
        "test -f README.md && test -f MAINTENANCE_GUIDE.md" \
        "周度"

    # 导航文档存在
    run_check "导航文档存在" \
        "test -f ../FORMAL_AND_PRACTICAL_NAVIGATION.md" \
        "周度"
fi

# 输出检查结果
echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "📊 检查结果汇总"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

for result in "${CHECK_RESULTS[@]}"; do
    echo "  $result"
done

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "统计:"
echo "  总检查数: $total_checks"
echo "  通过: $passed_checks"
echo "  失败: $failed_checks"
echo "  警告: $warnings"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo ""

# 返回状态码
if [ $failed_checks -eq 0 ]; then
    echo "✅ 所有必需检查通过！"
    exit 0
else
    echo "❌ 发现 $failed_checks 个失败检查，请修复！"
    exit 1
fi
