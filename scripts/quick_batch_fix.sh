#!/bin/bash

# 快速批量修复脚本
# 用于快速执行术语标准化和结构检查

set -e  # 遇到错误立即退出

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# 日志函数
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# 显示帮助信息
show_help() {
    echo "快速批量修复脚本"
    echo ""
    echo "用法: $0 <目标目录> [选项]"
    echo ""
    echo "选项:"
    echo "  --dry-run     试运行，不实际修改文件"
    echo "  --no-backup   不创建备份文件"
    echo "  --help        显示此帮助信息"
    echo ""
    echo "示例:"
    echo "  $0 ./formal_rust                    # 执行完整修复"
    echo "  $0 ./formal_rust --dry-run          # 试运行"
    echo "  $0 ./formal_rust --no-backup        # 不创建备份"
}

# 检查参数
if [ $# -eq 0 ]; then
    log_error "请指定目标目录"
    show_help
    exit 1
fi

if [ "$1" = "--help" ] || [ "$1" = "-h" ]; then
    show_help
    exit 0
fi

# 解析参数
TARGET_DIR="$1"
DRY_RUN=false
NO_BACKUP=false

shift
while [[ $# -gt 0 ]]; do
    case $1 in
        --dry-run)
            DRY_RUN=true
            shift
            ;;
        --no-backup)
            NO_BACKUP=true
            shift
            ;;
        *)
            log_error "未知选项: $1"
            show_help
            exit 1
            ;;
    esac
done

# 检查目标目录是否存在
if [ ! -d "$TARGET_DIR" ]; then
    log_error "目标目录不存在: $TARGET_DIR"
    exit 1
fi

# 显示执行信息
log_info "开始快速批量修复..."
log_info "目标目录: $TARGET_DIR"
log_info "试运行: $DRY_RUN"
log_info "备份: $([ "$NO_BACKUP" = true ] && echo "否" || echo "是")"
echo ""

# 检查Rust环境
if ! command -v cargo &> /dev/null; then
    log_error "未找到cargo，请确保已安装Rust"
    exit 1
fi

# 编译工具
log_info "编译修正工具..."
cd tools
if ! cargo build --release; then
    log_error "工具编译失败"
    exit 1
fi
cd ..

# 设置工具路径
TERMINOLOGY_FIXER="./tools/target/release/terminology_fixer"
STRUCTURE_CHECKER="./tools/target/release/structure_checker"
BATCH_EXECUTOR="./scripts/target/release/batch_fix_executor"

# 检查工具是否存在
if [ ! -f "$TERMINOLOGY_FIXER" ]; then
    log_error "术语修正工具未找到: $TERMINOLOGY_FIXER"
    exit 1
fi

if [ ! -f "$STRUCTURE_CHECKER" ]; then
    log_error "结构检查工具未找到: $STRUCTURE_CHECKER"
    exit 1
fi

# 构建参数
TERMINOLOGY_ARGS=""
STRUCTURE_ARGS=""

if [ "$DRY_RUN" = true ]; then
    TERMINOLOGY_ARGS="$TERMINOLOGY_ARGS --dry-run"
fi

if [ "$NO_BACKUP" = true ]; then
    TERMINOLOGY_ARGS="$TERMINOLOGY_ARGS --no-backup"
fi

# 执行术语修正
log_info "步骤1: 执行术语标准化..."
if ! $TERMINOLOGY_FIXER "$TARGET_DIR" $TERMINOLOGY_ARGS; then
    log_error "术语修正失败"
    exit 1
fi
log_success "术语修正完成!"

# 执行结构检查
log_info "步骤2: 执行结构检查..."
if ! $STRUCTURE_CHECKER "$TARGET_DIR"; then
    log_error "结构检查失败"
    exit 1
fi
log_success "结构检查完成!"

# 生成综合报告
log_info "步骤3: 生成综合报告..."

# 检查报告文件
TERMINOLOGY_REPORT="$TARGET_DIR/terminology_fix_report.md"
STRUCTURE_REPORT="$TARGET_DIR/structure_check_report.md"

if [ -f "$TERMINOLOGY_REPORT" ]; then
    log_info "术语修正报告: $TERMINOLOGY_REPORT"
fi

if [ -f "$STRUCTURE_REPORT" ]; then
    log_info "结构检查报告: $STRUCTURE_REPORT"
fi

# 创建综合报告
COMPREHENSIVE_REPORT="$TARGET_DIR/quick_batch_fix_report.md"
cat > "$COMPREHENSIVE_REPORT" << EOF
# 快速批量修复综合报告

**执行时间**: $(date)
**目标目录**: $TARGET_DIR
**试运行**: $DRY_RUN
**备份**: $([ "$NO_BACKUP" = true ] && echo "否" || echo "是")

## 执行概览

本次快速批量修复包含以下步骤：

1. **术语标准化**: 修正文档中的术语使用不一致问题
2. **结构检查**: 检查文档结构是否符合标准模板
3. **综合报告**: 生成详细的修复报告

## 详细报告

### 术语修正报告
EOF

if [ -f "$TERMINOLOGY_REPORT" ]; then
    echo "术语修正报告已生成: \`terminology_fix_report.md\`" >> "$COMPREHENSIVE_REPORT"
else
    echo "术语修正报告未生成" >> "$COMPREHENSIVE_REPORT"
fi

cat >> "$COMPREHENSIVE_REPORT" << EOF

### 结构检查报告
EOF

if [ -f "$STRUCTURE_REPORT" ]; then
    echo "结构检查报告已生成: \`structure_check_report.md\`" >> "$COMPREHENSIVE_REPORT"
else
    echo "结构检查报告未生成" >> "$COMPREHENSIVE_REPORT"
fi

cat >> "$COMPREHENSIVE_REPORT" << EOF

## 下一步行动

1. **查看详细报告**: 检查生成的报告文件
2. **验证修正效果**: 确认修正结果符合预期
3. **继续改进**: 根据报告建议进行进一步优化
4. **建立监控**: 建立持续的质量监控机制

## 注意事项

- 如果使用了备份功能，原始文件已备份为 \`.md.backup\` 文件
- 如果是试运行，文件内容未实际修改
- 建议在正式环境中使用前先在测试环境验证

---
**脚本版本**: 1.0
**生成时间**: $(date)
EOF

log_success "综合报告已生成: $COMPREHENSIVE_REPORT"

# 显示执行摘要
echo ""
log_success "快速批量修复执行完成!"
log_info "请查看以下报告文件:"
if [ -f "$TERMINOLOGY_REPORT" ]; then
    echo "  - 术语修正报告: $TERMINOLOGY_REPORT"
fi
if [ -f "$STRUCTURE_REPORT" ]; then
    echo "  - 结构检查报告: $STRUCTURE_REPORT"
fi
echo "  - 综合报告: $COMPREHENSIVE_REPORT"

# 如果存在备份文件，显示备份信息
if [ "$NO_BACKUP" = false ] && [ "$DRY_RUN" = false ]; then
    BACKUP_COUNT=$(find "$TARGET_DIR" -name "*.md.backup" | wc -l)
    if [ "$BACKUP_COUNT" -gt 0 ]; then
        log_info "已创建 $BACKUP_COUNT 个备份文件"
    fi
fi

echo ""
log_info "修复完成！请检查报告文件以了解详细结果。" 