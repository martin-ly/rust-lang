#!/bin/bash

# Rust 1.89 控制流与函数特性研究项目状态检查脚本
# 检查项目的完整性、测试状态、文档状态等

set -e

# 颜色定义
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
NC='\033[0m' # No Color

# 项目根目录
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# 统计变量
TOTAL_FILES=0
TOTAL_LINES=0
TEST_FILES=0
DOC_FILES=0
EXAMPLE_FILES=0
SOURCE_FILES=0

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

log_header() {
    echo -e "${CYAN}=== $1 ===${NC}"
}

# 统计文件数量和行数
count_files_and_lines() {
    local dir="$1"
    local pattern="$2"
    local description="$3"

    if [[ -d "$dir" ]]; then
        local files=($(find "$dir" -name "$pattern" -type f 2>/dev/null))
        local count=${#files[@]}
        local lines=0

        for file in "${files[@]}"; do
            if [[ -f "$file" ]]; then
                local file_lines=$(wc -l < "$file" 2>/dev/null || echo "0")
                lines=$((lines + file_lines))
            fi
        done

        echo "$count|$lines|$description"
    else
        echo "0|0|$description (目录不存在)"
    fi
}

# 检查Rust版本
check_rust_version() {
    log_header "Rust版本检查"

    if ! command -v rustc &> /dev/null; then
        log_error "Rust未安装"
        return 1
    fi

    local rust_version=$(rustc --version | cut -d' ' -f2)
    local required_version="1.92.0"

    log_info "当前Rust版本: $rust_version"
    log_info "需要Rust版本: $required_version"

    if [[ "$rust_version" < "$required_version" ]]; then
        log_warning "Rust版本可能过低，建议升级到1.92.0或更高版本"
    else
        log_success "Rust版本符合要求"
    fi

    echo
}

# 检查项目结构
check_project_structure() {
    log_header "项目结构检查"

    local required_dirs=(
        "src"
        "examples"
        "docs"
        "tests"
        "benches"
        "scripts"
    )

    local required_files=(
        "Cargo.toml"
        "README.md"
        "LICENSE"
        "src/lib.rs"
    )

    # 检查目录
    for dir in "${required_dirs[@]}"; do
        if [[ -d "$PROJECT_ROOT/$dir" ]]; then
            log_success "目录存在: $dir"
        else
            log_warning "目录缺失: $dir"
        fi
    done

    # 检查文件
    for file in "${required_files[@]}"; do
        if [[ -f "$PROJECT_ROOT/$file" ]]; then
            log_success "文件存在: $file"
        else
            log_warning "文件缺失: $file"
        fi
    done

    echo
}

# 统计项目文件
count_project_files() {
    log_header "项目文件统计"

    # 统计源代码文件
    local source_stats=$(count_files_and_lines "$PROJECT_ROOT/src" "*.rs" "源代码文件")
    IFS='|' read -r count lines description <<< "$source_stats"
    SOURCE_FILES=$count
    TOTAL_FILES=$((TOTAL_FILES + count))
    TOTAL_LINES=$((TOTAL_LINES + lines))
    log_info "$description: $count 个文件, $lines 行代码"

    # 统计示例文件
    local example_stats=$(count_files_and_lines "$PROJECT_ROOT/examples" "*.rs" "示例文件")
    IFS='|' read -r count lines description <<< "$example_stats"
    EXAMPLE_FILES=$count
    TOTAL_FILES=$((TOTAL_FILES + count))
    TOTAL_LINES=$((TOTAL_LINES + lines))
    log_info "$description: $count 个文件, $lines 行代码"

    # 统计文档文件
    local doc_stats=$(count_files_and_lines "$PROJECT_ROOT/docs" "*.md" "文档文件")
    IFS='|' read -r count lines description <<< "$doc_stats"
    DOC_FILES=$count
    TOTAL_FILES=$((TOTAL_FILES + count))
    TOTAL_LINES=$((TOTAL_LINES + lines))
    log_info "$description: $count 个文件, $lines 行代码"

    # 统计测试文件
    local test_stats=$(count_files_and_lines "$PROJECT_ROOT/tests" "*.rs" "测试文件")
    IFS='|' read -r count lines description <<< "$test_stats"
    TEST_FILES=$count
    TOTAL_FILES=$((TOTAL_FILES + count))
    TOTAL_LINES=$((TOTAL_LINES + lines))
    log_info "$description: $count 个文件, $lines 行代码"

    # 统计基准测试文件
    local bench_stats=$(count_files_and_lines "$PROJECT_ROOT/benches" "*.rs" "基准测试文件")
    IFS='|' read -r count lines description <<< "$bench_stats"
    TOTAL_FILES=$((TOTAL_FILES + count))
    TOTAL_LINES=$((TOTAL_LINES + lines))
    log_info "$description: $count 个文件, $lines 行代码"

    # 统计脚本文件
    local script_stats=$(count_files_and_lines "$PROJECT_ROOT/scripts" "*.sh" "Shell脚本")
    IFS='|' read -r count lines description <<< "$script_stats"
    TOTAL_FILES=$((TOTAL_FILES + count))
    TOTAL_LINES=$((TOTAL_LINES + lines))
    log_info "$description: $count 个文件, $lines 行代码"

    local script_stats=$(count_files_and_lines "$PROJECT_ROOT/scripts" "*.bat" "批处理脚本")
    IFS='|' read -r count lines description <<< "$script_stats"
    TOTAL_FILES=$((TOTAL_FILES + count))
    TOTAL_LINES=$((TOTAL_LINES + lines))
    log_info "$description: $count 个文件, $lines 行代码"

    echo
    log_info "总计: $TOTAL_FILES 个文件, $TOTAL_LINES 行代码"
    echo
}

# 检查Cargo配置
check_cargo_config() {
    log_header "Cargo配置检查"

    if [[ -f "$PROJECT_ROOT/Cargo.toml" ]]; then
        log_success "Cargo.toml 存在"

        # 检查版本
        local version=$(grep "^version = " "$PROJECT_ROOT/Cargo.toml" | cut -d'"' -f2)
        log_info "项目版本: $version"

        # 检查edition
        local edition=$(grep "^edition = " "$PROJECT_ROOT/Cargo.toml" | cut -d'"' -f2)
        log_info "Rust Edition: $edition"

        # 检查依赖数量
        local deps=$(grep -c "^\[dependencies\]" "$PROJECT_ROOT/Cargo.toml" || echo "0")
        log_info "依赖配置块数量: $deps"

    else
        log_error "Cargo.toml 不存在"
    fi

    if [[ -f "$PROJECT_ROOT/.cargo/config.toml" ]]; then
        log_success "Cargo配置文件存在"
    else
        log_warning "Cargo配置文件不存在"
    fi

    echo
}

# 检查测试状态
check_test_status() {
    log_header "测试状态检查"

    if [[ $TEST_FILES -gt 0 ]]; then
        log_info "运行测试..."
        cd "$PROJECT_ROOT"

        if cargo test --quiet; then
            log_success "所有测试通过"
        else
            log_error "测试失败"
            return 1
        fi
    else
        log_warning "没有找到测试文件"
    fi

    echo
}

# 检查构建状态
check_build_status() {
    log_header "构建状态检查"

    cd "$PROJECT_ROOT"

    log_info "检查代码..."
    if cargo check --quiet; then
        log_success "代码检查通过"
    else
        log_error "代码检查失败"
        return 1
    fi

    log_info "构建项目..."
    if cargo build --quiet; then
        log_success "项目构建成功"
    else
        log_error "项目构建失败"
        return 1
    fi

    echo
}

# 检查文档状态
check_documentation_status() {
    log_header "文档状态检查"

    if [[ $DOC_FILES -gt 0 ]]; then
        log_success "文档文件数量: $DOC_FILES"

        # 检查README
        if [[ -f "$PROJECT_ROOT/README.md" ]]; then
            local readme_lines=$(wc -l < "$PROJECT_ROOT/README.md")
            log_info "README.md: $readme_lines 行"
        fi

        # 检查项目完成报告
        if [[ -f "$PROJECT_ROOT/PROJECT_COMPLETION_REPORT.md" ]]; then
            log_success "项目完成报告存在"
        else
            log_warning "项目完成报告不存在"
        fi

    else
        log_warning "没有找到文档文件"
    fi

    echo
}

# 检查CI/CD配置
check_cicd_config() {
    log_header "CI/CD配置检查"

    local cicd_dir="$PROJECT_ROOT/.github/workflows"

    if [[ -d "$cicd_dir" ]]; then
        local workflow_files=($(find "$cicd_dir" -name "*.yml" -o -name "*.yaml"))
        local count=${#workflow_files[@]}

        if [[ $count -gt 0 ]]; then
            log_success "CI/CD工作流配置: $count 个文件"
            for file in "${workflow_files[@]}"; do
                local filename=$(basename "$file")
                log_info "  - $filename"
            done
        else
            log_warning "CI/CD工作流目录为空"
        fi
    else
        log_warning "CI/CD配置目录不存在"
    fi

    echo
}

# 检查脚本状态
check_scripts_status() {
    log_header "脚本状态检查"

    local scripts_dir="$PROJECT_ROOT/scripts"

    if [[ -d "$scripts_dir" ]]; then
        local shell_scripts=($(find "$scripts_dir" -name "*.sh" -type f))
        local batch_scripts=($(find "$scripts_dir" -name "*.bat" -type f))

        local shell_count=${#shell_scripts[@]}
        local batch_count=${#batch_scripts[@]}

        if [[ $shell_count -gt 0 ]]; then
            log_success "Shell脚本: $shell_count 个"
            for script in "${shell_scripts[@]}"; do
                local filename=$(basename "$script")
                if [[ -x "$script" ]]; then
                    log_info "  - $filename (可执行)"
                else
                    log_warning "  - $filename (不可执行)"
                fi
            done
        fi

        if [[ $batch_count -gt 0 ]]; then
            log_success "批处理脚本: $batch_count 个"
            for script in "${batch_scripts[@]}"; do
                local filename=$(basename "$script")
                log_info "  - $filename"
            done
        fi

    else
        log_warning "脚本目录不存在"
    fi

    echo
}

# 生成项目状态报告
generate_status_report() {
    log_header "项目状态报告"

    local completion_rate=0

    # 计算完成度
    if [[ $TOTAL_FILES -gt 0 ]]; then
        local required_files=10  # 假设需要10个核心文件
        completion_rate=$((TOTAL_FILES * 100 / required_files))
        if [[ $completion_rate -gt 100 ]]; then
            completion_rate=100
        fi
    fi

    # 状态评估
    local status=""
    if [[ $completion_rate -ge 90 ]]; then
        status="优秀"
    elif [[ $completion_rate -ge 80 ]]; then
        status="良好"
    elif [[ $completion_rate -ge 70 ]]; then
        status="一般"
    else
        status="需要改进"
    fi

    echo "项目完成度: $completion_rate% ($status)"
    echo "文件统计:"
    echo "  - 源代码: $SOURCE_FILES 个文件"
    echo "  - 示例: $EXAMPLE_FILES 个文件"
    echo "  - 文档: $DOC_FILES 个文件"
    echo "  - 测试: $TEST_FILES 个文件"
    echo "  - 总计: $TOTAL_FILES 个文件, $TOTAL_LINES 行代码"
    echo

    # 建议
    if [[ $completion_rate -lt 100 ]]; then
        log_info "改进建议:"
        if [[ $TEST_FILES -eq 0 ]]; then
            echo "  - 添加测试文件"
        fi
        if [[ $DOC_FILES -lt 3 ]]; then
            echo "  - 完善文档系统"
        fi
        if [[ ! -d "$PROJECT_ROOT/benches" ]]; then
            echo "  - 添加基准测试"
        fi
        if [[ ! -d "$PROJECT_ROOT/.github/workflows" ]]; then
            echo "  - 配置CI/CD"
        fi
    else
        log_success "项目状态优秀！"
    fi

    echo
}

# 主函数
main() {
    echo -e "${CYAN}🚀 Rust 1.89 控制流与函数特性研究项目状态检查${NC}"
    echo "项目路径: $PROJECT_ROOT"
    echo

    # 执行各项检查
    check_rust_version
    check_project_structure
    count_project_files
    check_cargo_config
    check_test_status
    check_build_status
    check_documentation_status
    check_cicd_config
    check_scripts_status
    generate_status_report

    log_success "状态检查完成！"
}

# 脚本入口点
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    main "$@"
fi
