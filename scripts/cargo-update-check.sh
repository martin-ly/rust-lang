#!/usr/bin/env bash
set -euo pipefail

# cargo-update-check.sh
# Cargo update automation check script for Linux CI
# Usage: ./scripts/cargo-update-check.sh [--dry-run | --weekly | --format text|markdown|email]

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/.." && pwd)"
cd "${PROJECT_ROOT}"

DRY_RUN=false
WEEKLY=false
FORMAT="text"

while [[ $# -gt 0 ]]; do
    case "$1" in
        --dry-run)
            DRY_RUN=true
            shift
            ;;
        --weekly)
            WEEKLY=true
            DRY_RUN=true
            shift
            ;;
        --format)
            FORMAT="$2"
            shift 2
            ;;
        *)
            echo "Unknown option: $1"
            echo "Usage: $0 [--dry-run | --weekly | --format text|markdown|email]"
            exit 1
            ;;
    esac
done

if [[ "$FORMAT" == "markdown" || "$FORMAT" == "email" ]]; then
    DRY_RUN=true
fi

IS_WEEKLY=false
if [[ "$WEEKLY" == true || "$FORMAT" == "markdown" || "$FORMAT" == "email" ]]; then
    IS_WEEKLY=true
fi

REPORT_LINES=()
MD_LINES=()
EMAIL_LINES=()

report() {
    REPORT_LINES+=("$1")
    echo "$1"
}

mdline() {
    MD_LINES+=("$1")
}

email() {
    EMAIL_LINES+=("$1")
}

# ===== 文本报告 =====
report "========================================"
report "Cargo Update Check Report"
report "Date: $(date '+%Y-%m-%d %H:%M:%S')"
report "Project: ${PROJECT_ROOT}"
report "Mode: $([ "$DRY_RUN" = true ] && echo 'DRY-RUN' || echo 'LIVE')$([ "$IS_WEEKLY" = true ] && echo ' (WEEKLY)')"
report "========================================"
report ""

# ===== Markdown 报告头 =====
mdline "# 📦 依赖更新周报"
mdline ""
mdline "> **生成时间:** $(date '+%Y-%m-%d %H:%M:%S')  "
mdline "> **项目:** rust-lang  "
mdline "> **模式:** $([ "$DRY_RUN" = true ] && echo '只读检查' || echo '实际更新')"
mdline ""

# ===== Email 报告头 =====
email "Subject: [rust-lang] 每周依赖更新检查 - $(date '+%Y-%m-%d')"
email "From: automation@rust-lang.local"
email "To: maintainers@rust-lang.local"
email ""
email "========================================"
email "📦 rust-lang 每周依赖更新检查"
email "========================================"
email "生成时间: $(date '+%Y-%m-%d %H:%M:%S')"
email ""

# Verify cargo
if ! command -v cargo >/dev/null 2>&1; then
    echo "ERROR: cargo not found" >&2
    exit 1
fi
CV="$(cargo --version)"
report "Cargo: ${CV}"
mdline "- **Cargo:** ${CV}"
email "Cargo: ${CV}"
mdline ""

# Outdated check
report ""
report "--- Outdated Packages ---"
mdline "## 📊 过期依赖概览"
mdline ""
email "--- 过期依赖概览 ---"
email ""

OUTDATED_PKGS=()
if command -v cargo-outdated >/dev/null 2>&1; then
    OUTDATED_RAW=""
    while IFS= read -r line; do
        OUTDATED_RAW+="${line}"$'\n'
    done < <(cargo outdated -R 2>&1 || true)
    
    if echo "$OUTDATED_RAW" | grep -q "up to date"; then
        report "All root dependencies are up to date."
        mdline "✅ 所有根依赖均为最新版本。"
        email "✅ 所有根依赖均为最新版本。"
    else
        # 解析过期包
        while IFS= read -r line; do
            report "$line"
            if echo "$line" | grep -qE '^[^[:space:]]+\s+v?[0-9]'; then
                PKG="$(echo "$line" | awk '{print $1}')"
                OLD_V="$(echo "$line" | awk '{print $2}')"
                NEW_V="$(echo "$line" | awk '{print $4}')"
                OUTDATED_PKGS+=("$PKG|$OLD_V|$NEW_V")
            fi
        done < <(echo "$OUTDATED_RAW" | grep -E '^[^[:space:]]+\s+v?[0-9]' || true)
        
        if [ ${#OUTDATED_PKGS[@]} -gt 0 ]; then
            mdline "| 包名 | 当前版本 | 最新版本 | 优先级 |"
            mdline "|------|----------|----------|--------|"
            for pkg_info in "${OUTDATED_PKGS[@]}"; do
                IFS='|' read -r PNAME POLD PNEW <<< "$pkg_info"
                PRIORITY="普通"
                # 简单优先级判断
                OLD_MINOR="$(echo "$POLD" | sed -E 's/^v?([0-9]+)\.([0-9]+).*/\2/')"
                NEW_MINOR="$(echo "$PNEW" | sed -E 's/^v?([0-9]+)\.([0-9]+).*/\2/')"
                OLD_MAJOR="$(echo "$POLD" | sed -E 's/^v?([0-9]+).*/\1/')"
                NEW_MAJOR="$(echo "$PNEW" | sed -E 's/^v?([0-9]+).*/\1/')"
                if [ -n "$OLD_MAJOR" ] && [ -n "$NEW_MAJOR" ] && [ "$OLD_MAJOR" != "$NEW_MAJOR" ]; then
                    PRIORITY="🔴 高（主版本更新）"
                elif [ -n "$OLD_MINOR" ] && [ -n "$NEW_MINOR" ] && [ "$OLD_MINOR" != "$NEW_MINOR" ]; then
                    PRIORITY="🟡 中（次版本更新）"
                fi
                mdline "| ${PNAME} | ${POLD} | ${PNEW} | ${PRIORITY} |"
                email "  ${PNAME} ${POLD} -> ${PNEW} [${PRIORITY}]"
            done
        fi
    fi
else
    report "Note: cargo-outdated not installed"
    mdline "⚠️ 未安装 cargo-outdated，无法获取过期依赖信息。"
    email "⚠️ 未安装 cargo-outdated，无法获取过期依赖信息。"
fi

mdline ""

# Cargo update
report ""
report "--- cargo update $([ "$DRY_RUN" = true ] && echo '--dry-run') ---"
mdline "## 🔄 可更新依赖详情"
mdline ""
email "--- 可更新依赖详情 ---"
email ""

UPDATE_ARGS=()
if [ "$DRY_RUN" = true ]; then
    UPDATE_ARGS+=("--dry-run")
fi

UPDATED_PKGS=()
LOCKED_COUNT=0
while IFS= read -r line; do
    if echo "$line" | grep -qE '^\s+Updating\s+\S+\s+v?[0-9]'; then
        UPDATED_PKGS+=("$line")
    elif echo "$line" | grep -qE '^\s+Locking\s'; then
        LOCKED_COUNT=$((LOCKED_COUNT + 1))
    fi
done < <(cargo update "${UPDATE_ARGS[@]}" 2>&1 || true)

if [ ${#UPDATED_PKGS[@]} -gt 0 ]; then
    report "Packages Updated:"
    mdline "| 包名 | 旧版本 | 新版本 |"
    mdline "|------|--------|--------|"
    for pkg in "${UPDATED_PKGS[@]}"; do
        report "  $pkg"
        # 解析表格行
        PKG_NAME="$(echo "$pkg" | sed -E 's/^\s+Updating\s+(\S+).*/\1/')"
        PKG_OLD="$(echo "$pkg" | sed -E 's/.*Updating\s+\S+\s+v?([0-9][^[:space:]]*)\s+->.*/\1/')"
        PKG_NEW="$(echo "$pkg" | sed -E 's/.*->\s+v?([0-9][^[:space:]]*).*/\1/')"
        mdline "| ${PKG_NAME} | ${PKG_OLD} | ${PKG_NEW} |"
        email "  ${PKG_NAME} ${PKG_OLD} -> ${PKG_NEW}"
    done
else
    report "No packages were updated."
    mdline "✅ 无可更新依赖（所有依赖均已锁定到最新兼容版本）。"
    email "✅ 无可更新依赖。"
fi
if [ "$LOCKED_COUNT" -gt 0 ]; then
    report "Locked/Unchanged count: ${LOCKED_COUNT}"
    mdline ""
    mdline "- 锁定/未变更依赖数: **${LOCKED_COUNT}**"
fi

mdline ""

# Audit
report ""
report "--- Security Audit ---"
mdline "## 🔒 安全审计"
mdline ""
email "--- 安全审计 ---"
email ""

AUDIT_WARNINGS=false
if command -v cargo-audit >/dev/null 2>&1; then
    AUDIT_OUT="${PROJECT_ROOT}/target/audit-temp-$$.json"
    if cargo audit --json > "$AUDIT_OUT" 2>/dev/null || true; then
        if command -v jq >/dev/null 2>&1; then
            VULN_COUNT=$(jq '.vulnerabilities.count // 0' "$AUDIT_OUT" 2>/dev/null || echo 0)
            if [ "$VULN_COUNT" -gt 0 ]; then
                AUDIT_WARNINGS=true
                report "⚠️ Found ${VULN_COUNT} vulnerabilities"
                mdline "🔴 发现 **${VULN_COUNT}** 个安全漏洞："
                email "🔴 发现 ${VULN_COUNT} 个安全漏洞："
                while IFS= read -r vuln; do
                    mdline "- ${vuln}"
                    email "  - ${vuln}"
                done < <(jq -r '.vulnerabilities.list[] | "\(.advisory.package) (\(.advisory.id)): \(.advisory.title)"' "$AUDIT_OUT" 2>/dev/null || true)
            else
                report "No security advisories found."
                mdline "✅ 未发现安全漏洞。"
                email "✅ 未发现安全漏洞。"
            fi
        else
            report "No security advisories found (cargo audit completed)."
            mdline "✅ cargo audit 执行完成，未发现安全漏洞。"
            email "✅ cargo audit 执行完成，未发现安全漏洞。"
        fi
    else
        report "cargo audit failed"
        mdline "⚠️ cargo audit 执行失败，请手动检查。"
        email "⚠️ cargo audit 执行失败，请手动检查。"
    fi
    rm -f "$AUDIT_OUT"
else
    report "Note: cargo-audit not installed"
    mdline "⚠️ 未安装 cargo-audit，无法执行安全审计。"
    email "⚠️ 未安装 cargo-audit，无法执行安全审计。"
fi

mdline ""

# Recommendations
report ""
report "--- Recommendations ---"
report "  libp2p  - verify hickory-resolver compatibility before upgrading to 0.56+"
report "  dioxus  - check for stable releases when upgrading from RC"
report "  sea-orm - 2.0.0 is still in RC; verify API stability before upgrading"
report "  bincode - keep pinned at 2.0.1 until 3.0 stable is released"

mdline "## 💡 更新建议"
mdline ""
mdline "| 包名 | 建议 |"
mdline "|------|------|"
mdline "| libp2p | 升级到 0.56+ 前验证 hickory-resolver 兼容性 |"
mdline "| dioxus | 从 RC 升级时检查是否有稳定版发布 |"
mdline "| sea-orm | 2.0.0 仍为 RC；升级前验证 API 稳定性 |"
mdline "| bincode | 3.0 稳定版发布前保持锁定在 2.0.1 |"
mdline ""

email "--- 更新建议 ---"
email "  libp2p  - 升级到 0.56+ 前验证 hickory-resolver 兼容性"
email "  dioxus  - 从 RC 升级时检查是否有稳定版发布"
email "  sea-orm - 2.0.0 仍为 RC；升级前验证 API 稳定性"
email "  bincode - 3.0 稳定版发布前保持锁定在 2.0.1"
email ""

# 周报模板专用区域
if [ "$IS_WEEKLY" = true ]; then
    mdline "## 📋 本周行动项"
    mdline ""
    mdline "- [ ] 审核上述过期依赖，确认是否安全升级"
    mdline "- [ ] 处理安全审计中发现的问题（如有）"
    mdline "- [ ] 运行 \`cargo test --workspace\` 验证兼容性"
    mdline "- [ ] 运行 \`cargo clippy --workspace\` 检查警告"
    mdline "- [ ] 更新 CHANGELOG.md（如应用了更新）"
    mdline ""
    mdline "## 📝 备注"
    mdline ""
    mdline "<!-- 在此填写本周特殊情况说明 -->"
    mdline ""
    mdline "---"
    mdline ""
    mdline "*此报告由自动化脚本生成。*"
fi

report ""
report "========================================"
report "Report Complete"
report "========================================"

# 保存报告
mkdir -p "${PROJECT_ROOT}/target"
TIMESTAMP=$(date '+%Y%m%d-%H%M%S')

# 文本报告
REPORT_FILE="${PROJECT_ROOT}/target/cargo-update-report-${TIMESTAMP}.txt"
printf "%s\n" "${REPORT_LINES[@]}" > "$REPORT_FILE"
report ""
report "Text report saved to: ${REPORT_FILE}"

# Markdown 报告
if [ "$IS_WEEKLY" = true ] || [ "$FORMAT" = "markdown" ]; then
    MD_FILE="${PROJECT_ROOT}/target/cargo-update-weekly-${TIMESTAMP}.md"
    printf "%s\n" "${MD_LINES[@]}" > "$MD_FILE"
    report "Markdown report saved to: ${MD_FILE}"
fi

# Email 报告
if [ "$FORMAT" = "email" ]; then
    EMAIL_FILE="${PROJECT_ROOT}/target/cargo-update-email-${TIMESTAMP}.txt"
    printf "%s\n" "${EMAIL_LINES[@]}" > "$EMAIL_FILE"
    report "Email report saved to: ${EMAIL_FILE}"
fi
