#!/bin/bash
# Rust 1.90 代码质量改进 - 工作恢复脚本
# 用于中断后恢复工作状态

set -e  # 遇到错误立即退出

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
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

log_step() {
    echo -e "${CYAN}[STEP]${NC} $1"
}

# 检查命令是否存在
check_command() {
    if ! command -v "$1" &> /dev/null; then
        log_error "$1 命令未找到，请先安装"
        return 1
    fi
    return 0
}

# 检查是否在正确的目录
check_project_root() {
    if [ ! -f "Cargo.toml" ]; then
        log_error "未找到 Cargo.toml，请在项目根目录运行此脚本"
        exit 1
    fi
    log_success "项目根目录检查通过"
}

# 恢复 Git 状态
restore_git_state() {
    log_step "恢复 Git 状态..."
    
    if [ -d ".git" ]; then
        # 检查是否有未提交的更改
        if ! git diff --quiet; then
            log_warning "发现未提交的更改，正在保存..."
            git add .
            git commit -m "WIP: 代码质量改进进度保存 $(date)"
        fi
        
        # 检查是否有未推送的提交
        if [ "$(git rev-list --count @{u}..HEAD)" -gt 0 ]; then
            log_info "发现未推送的提交，正在推送..."
            git push origin HEAD
        fi
        
        log_success "Git 状态恢复完成"
    else
        log_warning "未找到 Git 仓库"
    fi
}

# 检查进度跟踪文件
check_progress() {
    log_step "检查工作进度..."
    
    if [ -f "PROGRESS_TRACKING.md" ]; then
        log_info "发现进度跟踪文件，显示当前状态："
        cat PROGRESS_TRACKING.md
        echo ""
    else
        log_warning "未找到进度跟踪文件，创建新的跟踪文件..."
        create_progress_file
    fi
}

# 创建进度跟踪文件
create_progress_file() {
    cat > PROGRESS_TRACKING.md << EOF
# 代码质量改进进度跟踪

## 当前状态
- 安全漏洞修复: 0/6 完成
- Default 实现添加: 0/30 完成
- Clippy 警告修复: 0/135 完成
- 依赖更新: 0/50 完成

## 下一步行动
1. 运行安全审计
2. 修复安全漏洞
3. 添加 Default 实现
4. 修复 Clippy 警告

## 最后更新
$(date)
EOF
    log_success "进度跟踪文件已创建"
}

# 运行基础检查
run_basic_checks() {
    log_step "运行基础检查..."
    
    # 检查 Rust 工具链
    if check_command "cargo"; then
        log_success "Cargo 工具链检查通过"
    else
        log_error "Cargo 未安装，请先安装 Rust 工具链"
        exit 1
    fi
    
    # 检查项目编译状态
    log_info "检查项目编译状态..."
    if cargo check --workspace --quiet; then
        log_success "项目编译检查通过"
    else
        log_warning "项目编译存在问题，请检查错误信息"
    fi
}

# 运行 Clippy 检查
run_clippy_check() {
    log_step "运行 Clippy 检查..."
    
    if check_command "cargo"; then
        log_info "运行 Clippy 检查..."
        if cargo clippy --workspace -- -W clippy::all 2>&1 | tee clippy_report.txt; then
            log_success "Clippy 检查完成，无警告"
        else
            log_warning "Clippy 发现警告，报告已保存到 clippy_report.txt"
        fi
    fi
}

# 运行安全审计
run_security_audit() {
    log_step "运行安全审计..."
    
    if check_command "cargo-audit"; then
        log_info "运行安全审计..."
        if cargo audit 2>&1 | tee security_audit_report.txt; then
            log_success "安全审计通过，无漏洞"
        else
            log_warning "安全审计发现漏洞，报告已保存到 security_audit_report.txt"
        fi
    else
        log_warning "cargo-audit 未安装，跳过安全审计"
        log_info "安装命令: cargo install cargo-audit"
    fi
}

# 检查依赖状态
check_dependencies() {
    log_step "检查依赖状态..."
    
    if check_command "cargo-outdated"; then
        log_info "检查过时依赖..."
        cargo outdated 2>&1 | tee outdated_deps_report.txt
        log_warning "过时依赖报告已保存到 outdated_deps_report.txt"
    else
        log_warning "cargo-outdated 未安装，跳过依赖检查"
        log_info "安装命令: cargo install cargo-outdated"
    fi
}

# 生成恢复报告
generate_recovery_report() {
    log_step "生成恢复报告..."
    
    local report_file="RECOVERY_REPORT_$(date +%Y%m%d_%H%M%S).md"
    
    cat > "$report_file" << EOF
# 工作恢复报告

## 恢复时间
$(date)

## 检查结果
- 项目编译状态: $(if cargo check --workspace --quiet 2>/dev/null; then echo "✅ 正常"; else echo "❌ 存在问题"; fi)
- Clippy 警告: $(if [ -f "clippy_report.txt" ]; then echo "📄 报告已生成"; else echo "⏳ 未检查"; fi)
- 安全审计: $(if [ -f "security_audit_report.txt" ]; then echo "📄 报告已生成"; else echo "⏳ 未检查"; fi)
- 依赖状态: $(if [ -f "outdated_deps_report.txt" ]; then echo "📄 报告已生成"; else echo "⏳ 未检查"; fi)

## 下一步建议
1. 查看生成的报告文件
2. 根据报告修复问题
3. 更新进度跟踪文件
4. 继续代码质量改进工作

## 可用的修复脚本
- \`./scripts/automated_fix_script.ps1 -All\` - 执行所有自动修复
- \`./scripts/automated_fix_script.ps1 -FixClippy\` - 修复 Clippy 警告
- \`./scripts/automated_fix_script.ps1 -SecurityAudit\` - 运行安全审计

## 相关文档
- 改进计划: RUST_190_CODE_QUALITY_IMPROVEMENT_PLAN_2025.md
- 进度跟踪: PROGRESS_TRACKING.md
EOF
    
    log_success "恢复报告已生成: $report_file"
}

# 显示下一步操作建议
show_next_steps() {
    log_step "下一步操作建议："
    echo ""
    echo "1. 查看生成的报告文件："
    echo "   - clippy_report.txt (Clippy 警告)"
    echo "   - security_audit_report.txt (安全审计)"
    echo "   - outdated_deps_report.txt (过时依赖)"
    echo ""
    echo "2. 运行自动修复脚本："
    echo "   ./scripts/automated_fix_script.ps1 -All"
    echo ""
    echo "3. 手动修复需要人工干预的问题"
    echo ""
    echo "4. 更新进度跟踪文件："
    echo "   vim PROGRESS_TRACKING.md"
    echo ""
    echo "5. 提交更改："
    echo "   git add ."
    echo "   git commit -m '修复代码质量问题'"
    echo ""
}

# 主函数
main() {
    echo -e "${CYAN}🚀 Rust 1.90 代码质量改进 - 工作恢复脚本${NC}"
    echo -e "${CYAN}============================================${NC}"
    echo ""
    
    # 检查项目根目录
    check_project_root
    
    # 恢复 Git 状态
    restore_git_state
    
    # 检查进度
    check_progress
    
    # 运行基础检查
    run_basic_checks
    
    # 运行各种检查
    run_clippy_check
    run_security_audit
    check_dependencies
    
    # 生成恢复报告
    generate_recovery_report
    
    # 显示下一步操作建议
    show_next_steps
    
    log_success "工作恢复完成！"
}

# 错误处理
trap 'log_error "脚本执行出错，退出码: $?"' ERR

# 执行主函数
main "$@"
