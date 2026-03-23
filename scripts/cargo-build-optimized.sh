#!/bin/bash
# Cargo 编译优化脚本 (Linux/macOS 版本)
# 用法: ./scripts/cargo-build-optimized.sh [check|build|test|clean-cache|stats|install-tools]

set -e

# 颜色输出
INFO() { echo -e "\033[36m[INFO]\033[0m $1"; }
OK() { echo -e "\033[32m[OK]\033[0m $1"; }
WARN() { echo -e "\033[33m[WARN]\033[0m $1"; }

# 设置编译优化环境变量
set_build_optimizations() {
    # 使用所有CPU核心
    CORES=$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)
    JOBS=$((CORES - 1))
    export CARGO_BUILD_JOBS="$JOBS"
    INFO "设置并行编译作业数: $JOBS (检测到的核心数: $CORES)"
    
    # 启用sccache
    if command -v sccache &> /dev/null; then
        export RUSTC_WRAPPER="sccache"
        INFO "启用 sccache 缓存"
    else
        WARN "sccache 未安装，建议安装: cargo install sccache"
    fi
    
    # 链接器优化
    export CARGO_PROFILE_DEV_LTO="off"
    export CARGO_PROFILE_RELEASE_LTO="thin"
}

# 显示编译统计
show_build_stats() {
    INFO "========== 编译统计信息 =========="
    
    # 项目统计
    CRATE_COUNT=$(find crates -maxdepth 1 -type d | wc -l)
    echo "Workspace crates: $((CRATE_COUNT - 1))"
    
    # 依赖统计
    DEP_COUNT=$(cargo tree --prefix=none 2>/dev/null | wc -l)
    echo "Total dependencies: ~$DEP_COUNT"
    
    # 缓存统计
    if command -v sccache &> /dev/null; then
        echo ""
        echo "sccache 统计:"
        sccache --show-stats | grep -E "Cache hits|Cache misses|Cache size"
    fi
    
    # target目录大小
    if [ -d "target" ]; then
        TARGET_SIZE=$(du -sh target 2>/dev/null | cut -f1)
        echo ""
        echo "target directory size: $TARGET_SIZE"
    fi
    
    # 编译时间历史
    if [ -f ".cargo-build-times" ]; then
        echo ""
        echo "历史编译时间:"
        tail -10 .cargo-build-times
    fi
}

# 清理缓存
clear_build_cache() {
    INFO "清理编译缓存..."
    
    cargo clean
    
    if command -v sccache &> /dev/null; then
        sccache --stop-server 2>/dev/null || true
        sccache --start-server
        OK "sccache 已重启"
    fi
    
    if [ -d "target" ]; then
        rm -rf target
        OK "target 目录已清理"
    fi
}

# 安装工具
install_build_tools() {
    INFO "安装编译优化工具..."
    
    tools=("sccache" "cargo-bloat" "cargo-tree" "cargo-expand" "cargo-cache")
    
    for tool in "${tools[@]}"; do
        if ! command -v "$tool" &> /dev/null; then
            INFO "安装 $tool..."
            cargo install "$tool"
        else
            OK "$tool 已安装"
        fi
    done
}

# 主函数
main() {
    COMMAND="${1:-check}"
    PROFILE="${2:-dev}"
    
    set_build_optimizations
    
    case "$COMMAND" in
        check)
            INFO "执行快速检查 (cargo check --profile check-fast)..."
            START=$(date +%s)
            cargo check --profile check-fast
            END=$(date +%s)
            DURATION=$((END - START))
            OK "检查完成，耗时: ${DURATION}s"
            echo "$(date '+%Y-%m-%d %H:%M:%S'): check-fast - ${DURATION}s" >> .cargo-build-times
            ;;
            
        build)
            INFO "执行优化构建 (profile: $PROFILE)..."
            START=$(date +%s)
            cargo build --profile "$PROFILE"
            END=$(date +%s)
            DURATION=$((END - START))
            OK "构建完成，耗时: ${DURATION}s"
            echo "$(date '+%Y-%m-%d %H:%M:%S'): build-$PROFILE - ${DURATION}s" >> .cargo-build-times
            ;;
            
        test)
            INFO "执行测试..."
            START=$(date +%s)
            cargo test --profile test
            END=$(date +%s)
            DURATION=$((END - START))
            OK "测试完成，耗时: ${DURATION}s"
            ;;
            
        clean-cache)
            clear_build_cache
            ;;
            
        stats)
            show_build_stats
            ;;
            
        install-tools)
            install_build_tools
            ;;
            
        *)
            echo "用法: $0 [check|build|test|clean-cache|stats|install-tools]"
            exit 1
            ;;
    esac
}

main "$@"
