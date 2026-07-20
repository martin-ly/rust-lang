# `wasm32-wasi` → `wasm32-wasip1/p2` 迁移清单

> **生成日期**: 2026-06-22
> **扫描范围**: 全仓库 Markdown (*.md) + Rust 源码 (*.rs) + Cargo 清单 (*.toml)
> **状态**: 代码层与活跃文档已基本完成迁移，旧目标名仅保留在历史迁移指南与归档文档中

---

## 扫描结果摘要

| 类别 | 命中数 | 处理建议 |
|:---|:---|:---|
| `rust-toolchain.toml` 等工具链配置 | 1 | ✅ 已配置 `wasm32-wasip1` |
| 历史迁移指南 (`crates/c12_wasm/src/wasi_migration.rs`) | ~10 | ✅ 保留旧名作为历史对照 |
| 活跃文档顶部状态提示横幅 | ~150 | ✅ 提示本身包含旧名，无需修改 |
| 历史/归档报告与 Roadmap | ~30 | ✅ 保持原样 |
| 实际构建脚本/CI 中使用旧目标 | 0 | 🟢 无 |
| 疑似需要修改的残留 | 0 | 🟢 无 |

---

## 关键发现

### 1. 工具链已迁移

`rust-toolchain.toml` 已安装 `wasm32-wasip1`：

```toml
[toolchain]
components = ["rustfmt", "clippy", "rust-analyzer"]
targets = [
    "wasm32-unknown-unknown",
    "wasm32-wasip1",
]
```

### 2. 代码与示例

- `crates/c12_wasm/` 示例已使用 `wasm32-wasip1` / `wasm32-wasip2`：
  - `05_wasi_file_processor.rs`
  - `08_container_microservice.rs`
  - `10_ai_inference_wasinn.rs`
  - `11_crypto_operations.rs`
  - `09_wasi_02_component_example.rs`
  - `component_model_demo.rs`
- `content/emerging/wasm_advanced_topics.md` 已使用 `wasm32-wasip2`。

### 3. 唯一保留旧名的源代码文件

**`crates/c12_wasm/src/wasi_migration.rs`**

- 性质：专门的 **WASI 迁移指南**，标题即为《从 wasm32-wasi 到 wasm32-wasip1/p2》。
- 内容：包含旧目标名的时间线、对照表、迁移步骤，属于**历史对照用途**。
- 建议：**保留**，不修改。这是教授 "旧目标为什么被移除 / 如何迁移" 的核心材料。

### 4. 活跃文档顶部横幅

大量活跃 `.md` 文件顶部有统一的生态状态提示：

```markdown
> **生态状态提示**：本文档提及 `async-std` 与/或 `wasm32-wasi`。请注意：
> - `wasm32-wasi` 旧目标名已重命名为 **`wasm32-wasip1`**；WASI Preview 2 对应目标为 **`wasm32-wasip2`**。
```

这是全局批量治理脚本 (`scripts/maintenance/bulk_active_ecosystem_update.py`) 生成的提示，**不应删除**，因为它明确告知读者旧目标状态。

### 5. 历史/归档与 Roadmap 文件

以下文件提及 `wasm32-wasi` 作为历史事件/执行记录，应保持原样：

- `archive/*`
- `reports/ARCHIVED_ECOSYSTEM_REFERENCES_CLEANUP_PLAN_2026_06_19.md`
- `reports/MIGRATION_SCOPE_ASSESSMENT_2026_05_31.md`
- `reports/SYMMETRIC_DIFFERENCE_GLOBAL_AUDIT_2026_06_08.md`
- `.kimi/EXECUTION_PLAN_*.md`
- `.kimi/CRITICAL_ASSESSMENT_AND_ROADMAP_2026_05_29.md`

---

## 验证命令

```bash
# 全仓库旧目标命中（含横幅与历史文档）
grep -R --include='*.md' --include='*.rs' --include='*.toml' 'wasm32-wasi' . | wc -l

# 实际构建命令或目标配置中使用旧目标
grep -R --include='*.toml' --include='*.yml' --include='*.yaml' 'wasm32-wasi' . \
  | grep -vE 'wasm32-wasip1|wasm32-wasip2|历史|生态状态'

# Cargo.lock / 依赖中是否包含旧目标相关包
grep -i 'wasm32-wasi' Cargo.lock  # 应无命中
```

---

## 结论与下一步

- **WASI 目标迁移目标已达成**：`rust-toolchain.toml` 使用 `wasm32-wasip1`，代码示例使用 `wasip1/wasip2`，活跃文档已加提示横幅。
- **无需进一步大规模修改**。
- 后续仅需在新增/修改 WASM 相关内容时保持一致性：
  - 新示例统一使用 `wasm32-wasip1`（模块级 WASI）或 `wasm32-wasip2`（组件模型）
  - 避免在命令/配置中重新引入 `wasm32-wasi`
