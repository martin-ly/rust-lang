#!/usr/bin/env bash
#
# Rust 练习题自动化评测脚本 (Bash)
#
# 用法:
#   ./scripts/exercise-check.sh
#   ./scripts/exercise-check.sh --topic concurrency
#   ./scripts/exercise-check.sh --topic all --json
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"

TOPIC="all"
JSON_OUTPUT=false

# 解析参数
while [[ $# -gt 0 ]]; do
    case "$1" in
        --topic)
            TOPIC="$2"
            shift 2
            ;;
        --json)
            JSON_OUTPUT=true
            shift
            ;;
        -h|--help)
            echo "用法: $0 [--topic <主题>] [--json]"
            echo ""
            echo "可用主题:"
            echo "  ownership_borrowing, type_system, generics_traits,"
            echo "  concurrency, async_programming, error_handling,"
            echo "  macros, unsafe_rust, rustlings, all"
            exit 0
            ;;
        *)
            echo "未知参数: $1"
            exit 1
            ;;
    esac
done

# 颜色定义
GREEN='\033[32m'
RED='\033[31m'
YELLOW='\033[33m'
CYAN='\033[36m'
RESET='\033[0m'

cd "${PROJECT_ROOT}"

# 主题配置
declare -A TOPIC_FILTER=(
    [ownership_borrowing]="ownership_borrowing::"
    [type_system]="type_system::"
    [generics_traits]="generics_traits::"
    [concurrency]="concurrency::"
    [async_programming]="async_programming::"
    [error_handling]="error_handling::"
    [macros]="macros::"
    [unsafe_rust]="unsafe_rust::"
)

declare -A TOPIC_LABEL=(
    [ownership_borrowing]="所有权与借用"
    [type_system]="类型系统"
    [generics_traits]="泛型与特质"
    [concurrency]="并发编程"
    [async_programming]="异步编程"
    [error_handling]="错误处理"
    [macros]="宏系统"
    [unsafe_rust]="Unsafe Rust"
)

# 报告数据结构
RESULTS=()

run_crate_tests() {
    local filter="$1"
    local label="$2"
    local output
    local status="unknown"
    local tests_run=0
    local tests_passed=0
    local tests_failed=0

    if output=$(cargo test -p exercises --lib "$filter" 2>&1); then
        if echo "$output" | grep -q "running 0 tests"; then
            status="no_tests"
        else
            local line
            line=$(echo "$output" | grep "test result:" | tail -n 1 || true)
            if [[ "$line" =~ ok\.\ ([0-9]+)\ passed;\ ([0-9]+)\ failed; ]]; then
                tests_passed="${BASH_REMATCH[1]}"
                tests_failed="${BASH_REMATCH[2]}"
                tests_run=$((tests_passed + tests_failed))
                if [[ "$tests_failed" -eq 0 ]]; then
                    status="passed"
                else
                    status="partial"
                fi
            fi
        fi
    else
        local line
        line=$(echo "$output" | grep "test result:" | tail -n 1 || true)
        if [[ "$line" =~ FAILED\.\ ([0-9]+)\ passed;\ ([0-9]+)\ failed; ]]; then
            tests_passed="${BASH_REMATCH[1]}"
            tests_failed="${BASH_REMATCH[2]}"
            tests_run=$((tests_passed + tests_failed))
            if [[ "$tests_passed" -gt 0 ]]; then
                status="partial"
            else
                status="failed"
            fi
        else
            status="failed"
        fi
    fi

    # 保存结果 (topic|label|status|run|passed|failed)
    RESULTS+=("${filter%%::}|${label}|${status}|${tests_run}|${tests_passed}|${tests_failed}")
}

run_rustlings_tests() {
    local rustlings_dir="${PROJECT_ROOT}/exercises/rustlings_style"
    if [[ ! -d "$rustlings_dir" ]]; then
        return
    fi

    for dir in "$rustlings_dir"/*/; do
        [[ -f "$dir/Cargo.toml" ]] || continue
        local name
        name=$(basename "$dir")
        local output
        local status="unknown"
        local tests_run=0
        local tests_passed=0
        local tests_failed=0

        if output=$(cargo test --manifest-path "$dir/Cargo.toml" 2>&1); then
            local line
            line=$(echo "$output" | grep "test result:" | tail -n 1 || true)
            if [[ "$line" =~ ok\.\ ([0-9]+)\ passed;\ ([0-9]+)\ failed; ]]; then
                tests_passed="${BASH_REMATCH[1]}"
                tests_failed="${BASH_REMATCH[2]}"
                tests_run=$((tests_passed + tests_failed))
                if [[ "$tests_failed" -eq 0 ]]; then
                    status="passed"
                else
                    status="partial"
                fi
            fi
        else
            local line
            line=$(echo "$output" | grep "test result:" | tail -n 1 || true)
            if [[ "$line" =~ FAILED\.\ ([0-9]+)\ passed;\ ([0-9]+)\ failed; ]]; then
                tests_passed="${BASH_REMATCH[1]}"
                tests_failed="${BASH_REMATCH[2]}"
                tests_run=$((tests_passed + tests_failed))
                if [[ "$tests_passed" -gt 0 ]]; then
                    status="partial"
                else
                    status="failed"
                fi
            else
                status="failed"
            fi
        fi

        RESULTS+=("rustlings|Rustlings: ${name}|${status}|${tests_run}|${tests_passed}|${tests_failed}")
    done
}

# ====== 主程序 ======

if [[ "$TOPIC" == "all" ]]; then
    for t in "${!TOPIC_FILTER[@]}"; do
        run_crate_tests "${TOPIC_FILTER[$t]}" "${TOPIC_LABEL[$t]}"
    done
    run_rustlings_tests
elif [[ "$TOPIC" == "rustlings" ]]; then
    run_rustlings_tests
else
    if [[ -z "${TOPIC_FILTER[$TOPIC]:-}" ]]; then
        echo "错误: 未知主题 '$TOPIC'"
        echo "可用主题: ${!TOPIC_LABEL[*]} rustlings all"
        exit 1
    fi
    run_crate_tests "${TOPIC_FILTER[$TOPIC]}" "${TOPIC_LABEL[$TOPIC]}"
fi

# 统计
total_passed=0
total_failed=0
total_partial=0
total_tests_run=0
total_tests_passed=0

for r in "${RESULTS[@]}"; do
    IFS='|' read -r _topic _label _status _run _passed _failed <<< "$r"
    case "$_status" in
        passed) ((total_passed++)) ;;
        failed) ((total_failed++)) ;;
        partial) ((total_partial++)) ;;
    esac
    ((total_tests_run += _run))
    ((total_tests_passed += _passed))
done

# 输出
if [[ "$JSON_OUTPUT" == true ]]; then
    echo "{"
    echo '  "summary": {'
    echo "    \"topics_checked\": ${#RESULTS[@]},"
    echo "    \"passed\": $total_passed,"
    echo "    \"failed\": $total_failed,"
    echo "    \"partial\": $total_partial,"
    echo "    \"total_tests_run\": $total_tests_run,"
    echo "    \"total_tests_passed\": $total_tests_passed"
    echo '  },'
    echo '  "details": ['
    local first=true
    for r in "${RESULTS[@]}"; do
        IFS='|' read -r _topic _label _status _run _passed _failed <<< "$r"
        if [[ "$first" == true ]]; then
            first=false
        else
            echo ","
        fi
        echo -n "    {\"topic\": \"$_topic\", \"label\": \"$_label\", \"status\": \"$_status\", \"tests_run\": $_run, \"tests_passed\": $_passed, \"tests_failed\": $_failed}"
    done
    echo ""
    echo '  ]'
    echo "}"
else
    echo ""
    echo -e "${CYAN}═══════════════════════════════════════════${RESET}"
    echo -e "${CYAN}      Rust 练习题自动化评测报告${RESET}"
    echo -e "${CYAN}═══════════════════════════════════════════${RESET}"
    echo ""

    for r in "${RESULTS[@]}"; do
        IFS='|' read -r _topic _label _status _run _passed _failed <<< "$r"
        color="$YELLOW"
        icon="?"
        case "$_status" in
            passed)
                color="$GREEN"
                icon="✓"
                ;;
            failed)
                color="$RED"
                icon="✗"
                ;;
            partial)
                color="$YELLOW"
                icon="◐"
                ;;
        esac
        printf "%s [%-7s] %s (%s/%s 测试通过)\n" "$icon" "${_status^^}" "$_label" "$_passed" "$_run"
    done

    echo ""
    echo -e "${CYAN}───────────────────────────────────────────${RESET}"
    echo "  主题数: ${#RESULTS[@]}"
    echo -e "${GREEN}  通过  : $total_passed${RESET}"
    echo -e "${RED}  失败  : $total_failed${RESET}"
    echo -e "${YELLOW}  部分  : $total_partial${RESET}"
    echo "  测试数: $total_tests_passed / $total_tests_run 通过"
    echo -e "${CYAN}───────────────────────────────────────────${RESET}"

    if [[ "$total_failed" -eq 0 && "$total_partial" -eq 0 ]]; then
        echo ""
        echo -e "${GREEN}🎉 所有测试全部通过！${RESET}"
    elif [[ "$total_failed" -eq 0 ]]; then
        echo ""
        echo -e "${YELLOW}⚠️  所有主题都有测试通过，但部分未完全通过。${RESET}"
    else
        echo ""
        echo -e "${RED}❌ 存在完全失败的主题，请检查输出。${RESET}"
    fi
    echo ""
fi
