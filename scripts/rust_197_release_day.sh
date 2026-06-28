#!/usr/bin/env bash
# Rust 1.97.0 发布日执行辅助脚本
# 用法: bash scripts/rust_197_release_day.sh
# 注意: 本脚本应在 Rust 1.97.0 stable 实际发布后再运行。

set -euo pipefail

PROJECT_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$PROJECT_ROOT"

RELEASE_DATE="2026-07-09"
RUST_VERSION="1.97.0"

echo "=== Rust ${RUST_VERSION} 发布日执行脚本 ==="
echo "项目根目录: $PROJECT_ROOT"
echo "当前日期: $(date -Iseconds)"
echo ""

# ---------------------------------------------------------------------------
# 阶段 0: 确认网络与版本可用性
# ---------------------------------------------------------------------------
echo "--- 阶段 0: 确认 Rust ${RUST_VERSION} 可用 ---"

if rustup toolchain install "${RUST_VERSION}" --profile default 2>/dev/null; then
    echo "✅ Rust ${RUST_VERSION} 已安装或已可用"
else
    echo "❌ 无法安装 Rust ${RUST_VERSION}，可能尚未发布"
    exit 1
fi

if ! rustup run "${RUST_VERSION}" rustc --version | grep -q "${RUST_VERSION}"; then
    echo "❌ Rust ${RUST_VERSION} 版本不匹配"
    exit 1
fi

echo "✅ 版本验证通过"
echo ""

# ---------------------------------------------------------------------------
# 阶段 1: 工具链策略确认
# ---------------------------------------------------------------------------
echo "--- 阶段 1: 工具链策略确认 ---"

echo "说明: workspace 中多处使用 nightly feature gates（gen_blocks、never_type、"
echo "      core_intrinsics 等），无法整体切换到 ${RUST_VERSION} stable。"
echo "      保持 rust-toolchain.toml 为 nightly，仅在 nightly 上激活 1.97 稳定 API。"

if grep -q '^channel = "nightly"' rust-toolchain.toml; then
    echo "✅ rust-toolchain.toml 已保持为 nightly"
else
    echo "⚠️ rust-toolchain.toml 不是 nightly，请人工确认是否意图切换"
fi

rustup show
rustc --version

echo ""

# ---------------------------------------------------------------------------
# 阶段 2: 尝试编译以发现可用 API
# ---------------------------------------------------------------------------
echo "--- 阶段 2: 首次编译基线 ---"

if cargo check --workspace; then
    echo "✅ nightly 基线编译通过"
else
    echo "⚠️ nightly 基线编译存在错误，需人工介入"
fi

echo ""

# ---------------------------------------------------------------------------
# 阶段 3: 探测并提示需要手动激活的 API
# ---------------------------------------------------------------------------
echo "--- 阶段 3: 1.97 API 可用性探测 ---"

if [[ -f scripts/probe_rust_197_apis.rs ]]; then
    echo "运行独立探测程序（在 nightly 上编译并执行，1.97 stable API 在 nightly 上同样可用）..."
    rustc --edition 2024 scripts/probe_rust_197_apis.rs -o /tmp/probe_197 || true
    if [[ -x /tmp/probe_197 ]]; then
        /tmp/probe_197 || true
    fi
else
    echo "⚠️ 未找到 scripts/probe_rust_197_apis.rs，跳过自动探测"
fi

cat <<'EOF'
请根据 Rust 1.97.0 Release Notes 和上方探测结果，手动检查并激活以下文件中的等效实现：

  crates/c08_algorithms/src/rust_197_features.rs
    - VecDeque::truncate_front
    - VecDeque::retain_back（若未进入 1.97，保留等效实现并标注“推迟至 1.98”）
    - NonZero 位操作 API (highest_one / lowest_one / bit_width)
    - char::is_control() const
    - float_algebraic（若未进入 1.97，标注 1.98）
    - RandomSource / DefaultRandomSource（若未进入 1.97，标注跟踪中）
    - C-variadic fn definitions（若未进入 1.97，标注 nightly）
    - box_vec_non_null（若未进入 1.97，标注 1.98）

  建议验证命令（保持 nightly 工具链）:
    cargo check -p c08_algorithms
    # 然后取消注释真实 API 调用，再次运行 cargo check
EOF

echo ""

# ---------------------------------------------------------------------------
# 阶段 4: 全 Workspace 验证
# ---------------------------------------------------------------------------
echo "--- 阶段 4: 全 Workspace 验证 ---"

cargo check --workspace
cargo test --workspace
cargo clippy --workspace --all-features -- -D warnings

echo "✅ 全 Workspace 验证通过"
echo ""

# ---------------------------------------------------------------------------
# 阶段 5: 文档状态刷新提示
# ---------------------------------------------------------------------------
echo "--- 阶段 5: 文档状态刷新 ---"

cat <<'EOF'
请手动完成以下文档更新：

  1. concept/07_future/rust_1_97_preview.md
     - 标题改为 "Rust 1.97 稳定特性"
     - 将 🧪 Nightly / 🔄 PFCP 标记更新为 ✅ Stable 或 📋 跟踪
     - 添加官方 Release Notes 引用: https://blog.rust-lang.org/2026/07/09/Rust-1.97.0.html
     - 删除 "预计稳定日期" 等前瞻性措辞

  2. （可选）迁移到 docs/06_toolchain/06_21_rust_1_97_features.md

  3. concept/00_meta/terminology_glossary.md
     - 将 1.97 术语状态改为 ✅ Stable

  4. 搜索全仓库 `1.97` 相关标记，统一刷新状态
EOF

echo ""

# ---------------------------------------------------------------------------
# 阶段 6: 练习补全提示
# ---------------------------------------------------------------------------
echo "--- 阶段 6: 练习补全 ---"

cat <<'EOF'
请根据实际稳定特性更新或新增练习：

  - exercises/tests/l3_rust_197_alignment.rs（已存在，按实际 API 切换）
  - 新增 VecDeque::truncate_front / retain_back 行为验证
  - 新增 NonZero 位操作 / char::is_control const 测验
EOF

echo ""

# ---------------------------------------------------------------------------
# 阶段 7: CHANGELOG 与版本号
# ---------------------------------------------------------------------------
echo "--- 阶段 7: CHANGELOG 与版本号 ---"

cat <<'EOF'
请手动完善 CHANGELOG.md [3.1.0] 条目：

  - 列出实际进入 1.97.0 的稳定特性
  - 未进入的特性标注 “推迟至 1.98”
  - 确认根 Cargo.toml [workspace.package] version = "3.1.0"
EOF

echo ""

# ---------------------------------------------------------------------------
# 阶段 8: 提交与归档提示
# ---------------------------------------------------------------------------
echo "--- 阶段 8: 提交与归档 ---"

cat <<'EOF'
最终操作：

  git add -A
  git commit -m "chore: stabilize Rust 1.97.0 support"
  # 创建 PR / 合并
  # 将 .kimi/EXECUTION_RUST_1_97_RELEASE_2026_07_09.md 归档到 archive/project_reports/
EOF

echo ""
echo "=== 脚本执行完毕 ==="
echo "请根据上方提示完成需要人工判断的步骤。"
