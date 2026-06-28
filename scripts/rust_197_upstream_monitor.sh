#!/usr/bin/env bash
# Rust 1.97.0 上游发布动态监控脚本
# 用法: bash scripts/rust_197_upstream_monitor.sh
# 建议: 2026-07-03 ~ 2026-07-08 每日运行一次，记录发布动态。

set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_ROOT"

RUST_VERSION="1.97.0"
RELEASE_DATE="2026-07-09"
LOG_DIR="${PROJECT_ROOT}/reports"
LOG_FILE="${LOG_DIR}/RUST_197_UPSTREAM_MONITOR.log"

mkdir -p "$LOG_DIR"

timestamp() {
    date -Iseconds
}

record() {
    echo "[$(timestamp)] $1" | tee -a "$LOG_FILE"
}

record "=== Rust ${RUST_VERSION} 上游监控 ==="
record "预计发布日期: ${RELEASE_DATE}"
record "当前日期: $(date -Iseconds)"

# ---------------------------------------------------------------------------
# 检查 1: static.rust-lang.org 是否已上架 1.97.0 stable 的 channel 清单
# ---------------------------------------------------------------------------
CHANNEL_URL="https://static.rust-lang.org/dist/channel-rust-${RUST_VERSION}.toml"
record "检查 channel 清单: ${CHANNEL_URL}"

if command -v curl >/dev/null 2>&1; then
    http_code=$(curl -s -o /dev/null -w "%{http_code}" "$CHANNEL_URL" || true)
    if [[ "$http_code" == "200" ]]; then
        record "✅ Rust ${RUST_VERSION} stable 的 channel 清单已上架（HTTP 200）"
    else
        record "⏳ Rust ${RUST_VERSION} stable 尚未上架（HTTP ${http_code:-unknown}）"
    fi
else
    record "⚠️ 未安装 curl，跳过 channel 清单检查"
fi

# ---------------------------------------------------------------------------
# 检查 2: rustup 是否可安装 1.97.0（可选，若已发布则很快可用）
# ---------------------------------------------------------------------------
if command -v rustup >/dev/null 2>&1; then
    record "检查 rustup toolchain list..."
    if rustup toolchain list | grep -q "^${RUST_VERSION}"; then
        record "✅ 本机已安装 Rust ${RUST_VERSION}"
    else
        record "⏳ 本机尚未安装 Rust ${RUST_VERSION}"
    fi
else
    record "⚠️ 未安装 rustup，跳过本地工具链检查"
fi

# ---------------------------------------------------------------------------
# 检查 3: 官方博客最新发布页是否提到 1.97.0
# ---------------------------------------------------------------------------
BLOG_URL="https://blog.rust-lang.org/releases/latest/"
record "检查官方博客: ${BLOG_URL}"

if command -v curl >/dev/null 2>&1; then
    blog_html=$(curl -s -L "$BLOG_URL" || true)
    blog_version=$(echo "$blog_html" | grep -oE "Rust-[0-9]+\.[0-9]+\.[0-9]+" | head -1 | sed 's/Rust-//' || true)
    if [[ -z "$blog_version" ]]; then
        blog_version=$(echo "$blog_html" | grep -oE "Rust [0-9]+\.[0-9]+\.[0-9]+" | head -1 || true)
    fi
    if [[ -n "$blog_version" ]]; then
        record "ℹ️ 官方博客最新发布版本: ${blog_version}"
        if [[ "$blog_version" == *"${RUST_VERSION}"* ]]; then
            record "✅ 官方博客已发布 Rust ${RUST_VERSION} 公告"
        else
            record "⏳ 官方博客最新公告不是 ${RUST_VERSION}（当前为 ${blog_version}）"
        fi
    else
        record "⚠️ 无法解析官方博客版本"
    fi
else
    record "⚠️ 未安装 curl，跳过博客检查"
fi

# ---------------------------------------------------------------------------
# 检查 4: releases.rs 页面是否显示 1.97.0
# ---------------------------------------------------------------------------
RELEASES_RS_URL="https://releases.rs/"
record "检查 releases.rs: ${RELEASES_RS_URL}"

if command -v curl >/dev/null 2>&1; then
    if curl -s "$RELEASES_RS_URL" | grep -q "${RUST_VERSION}"; then
        record "✅ releases.rs 已包含 Rust ${RUST_VERSION} 信息"
    else
        record "⏳ releases.rs 尚未包含 Rust ${RUST_VERSION} 信息"
    fi
else
    record "⚠️ 未安装 curl，跳过 releases.rs 检查"
fi

record "=== 监控结束 ==="
record ""
