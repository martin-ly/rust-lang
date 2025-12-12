#!/bin/bash

# Rust 1.89 控制流与函数特性研究项目构建脚本
# 支持多平台构建和测试

set -e

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

# 检查Rust版本
check_rust_version() {
    log_info "检查Rust版本..."

    if ! command -v rustc &> /dev/null; then
        log_error "Rust未安装，请先安装Rust"
        exit 1
    fi

    local rust_version=$(rustc --version | cut -d' ' -f2)
    local required_version="1.92.0"

    log_info "当前Rust版本: $rust_version"
    log_info "需要Rust版本: $required_version"

    # 简单的版本比较（这里可以改进）
    if [[ "$rust_version" < "$required_version" ]]; then
        log_warning "Rust版本可能过低，建议升级到1.92.0或更高版本"
    fi
}

# 安装依赖
install_dependencies() {
    log_info "安装项目依赖..."

    # 安装rustup组件
    rustup component add rustfmt clippy

    # 安装cargo工具
    cargo install cargo-audit
    cargo install cargo-tarpaulin
    cargo install cargo-criterion

    log_success "依赖安装完成"
}

# 代码格式化
format_code() {
    log_info "格式化代码..."
    cargo fmt --all -- --check
    log_success "代码格式化检查完成"
}

# 代码检查
check_code() {
    log_info "检查代码..."
    cargo clippy --all-targets --all-features -- -D warnings
    log_success "代码检查完成"
}

# 安全审计
audit_code() {
    log_info "安全审计..."
    cargo audit
    log_success "安全审计完成"
}

# 构建项目
build_project() {
    local profile=${1:-debug}

    log_info "构建项目 (profile: $profile)..."

    case $profile in
        debug)
            cargo build --verbose
            ;;
        release)
            cargo build --release --verbose
            ;;
        *)
            log_error "未知的构建配置: $profile"
            exit 1
            ;;
    esac

    log_success "项目构建完成"
}

# 运行测试
run_tests() {
    local features=${1:-""}

    log_info "运行测试..."

    if [[ -n "$features" ]]; then
        cargo test --features "$features" --verbose
    else
        cargo test --verbose
    fi

    log_success "测试完成"
}

# 运行基准测试
run_benchmarks() {
    log_info "运行基准测试..."
    cargo criterion --message-format=json
    log_success "基准测试完成"
}

# 生成文档
generate_docs() {
    log_info "生成文档..."

    # 生成公共API文档
    cargo doc --no-deps --all-features

    # 生成私有API文档
    cargo doc --no-deps --document-private-items --all-features

    log_success "文档生成完成"
    log_info "文档位置: target/doc"
}

# 代码覆盖率
run_coverage() {
    log_info "运行代码覆盖率测试..."
    cargo tarpaulin --out Html --output-dir coverage
    log_success "代码覆盖率测试完成"
    log_info "覆盖率报告位置: coverage"
}

# 清理构建文件
clean_build() {
    log_info "清理构建文件..."
    cargo clean
    log_success "清理完成"
}

# 显示帮助信息
show_help() {
    echo "Rust 1.89 控制流与函数特性研究项目构建脚本"
    echo ""
    echo "用法: $0 [选项] [命令]"
    echo ""
    echo "选项:"
    echo "  -h, --help     显示此帮助信息"
    echo "  -v, --verbose  详细输出"
    echo "  -f, --features 指定特性 (例如: async,generics,performance)"
    echo ""
    echo "命令:"
    echo "  check          检查代码 (格式化 + clippy + 审计)"
    echo "  build          构建项目"
    echo "  test           运行测试"
    echo "  bench          运行基准测试"
    echo "  doc            生成文档"
    echo "  coverage       运行代码覆盖率测试"
    echo "  clean          清理构建文件"
    echo "  all            执行所有步骤"
    echo ""
    echo "示例:"
    echo "  $0 check                    # 检查代码"
    echo "  $0 build release            # 发布模式构建"
    echo "  $0 test async,generics      # 运行特定特性的测试"
    echo "  $0 all                      # 执行所有步骤"
}

# 主函数
main() {
    local verbose=false
    local features=""
    local command=""

    # 解析命令行参数
    while [[ $# -gt 0 ]]; do
        case $1 in
            -h|--help)
                show_help
                exit 0
                ;;
            -v|--verbose)
                verbose=true
                shift
                ;;
            -f|--features)
                features="$2"
                shift 2
                ;;
            check|build|test|bench|doc|coverage|clean|all)
                command="$1"
                shift
                ;;
            debug|release)
                if [[ "$command" == "build" ]]; then
                    build_profile="$1"
                fi
                shift
                ;;
            *)
                log_error "未知参数: $1"
                show_help
                exit 1
                ;;
        esac
    done

    # 如果没有指定命令，显示帮助
    if [[ -z "$command" ]]; then
        show_help
        exit 0
    fi

    # 设置详细输出
    if [[ "$verbose" == true ]]; then
        set -x
    fi

    # 检查Rust版本
    check_rust_version

    # 执行命令
    case $command in
        check)
            format_code
            check_code
            audit_code
            ;;
        build)
            build_project "${build_profile:-debug}"
            ;;
        test)
            run_tests "$features"
            ;;
        bench)
            run_benchmarks
            ;;
        doc)
            generate_docs
            ;;
        coverage)
            run_coverage
            ;;
        clean)
            clean_build
            ;;
        all)
            log_info "执行所有步骤..."
            install_dependencies
            format_code
            check_code
            audit_code
            build_project release
            run_tests "$features"
            run_benchmarks
            generate_docs
            run_coverage
            log_success "所有步骤执行完成！"
            ;;
        *)
            log_error "未知命令: $command"
            exit 1
            ;;
    esac
}

# 脚本入口点
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    main "$@"
fi
