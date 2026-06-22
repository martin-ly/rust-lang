# Rust 1.97.0 发布日执行清单

> **执行日期**: 2026-07-09（预计稳定发布日）
> **目标版本**: Rust 1.97.0
> **预计耗时**: 8 小时（可分 1-2 天完成）
> **前置依赖**: `.kimi/plan_rust_1_97_stabilization.md` 已就绪

---

## 阶段 0：环境确认（15 分钟）

- [ ] 确认 Rust 1.97.0 已发布：`rustup check` 或访问 <https://releases.rs>
- [ ] 确认本机网络可访问 `static.rust-lang.org`
- [ ] 从当前分支创建发布日工作分支：`git checkout -b rust-1.97-release-day`
- [ ] 备份当前 `Cargo.lock`（可选）：`cp Cargo.lock Cargo.lock.pre-1.97`

---

## 阶段 1：工具链切换（15 分钟）

- [ ] 修改 `rust-toolchain.toml` 的 channel：

  ```toml
  channel = "1.97.0"
  ```

- [ ] 安装目标并验证：

  ```bash
  rustup show
  rustc --version  # 应输出 1.97.0
  ```

- [ ] 运行 `cargo check --workspace` 确认 1.97 编译基线通过

---

## 阶段 2：Crate 代码激活（1.5 小时）

目标文件：`crates/c08_algorithms/src/rust_197_features.rs`

- [ ] `VecDeque::truncate_front`：
  - 取消注释真实 API 调用
  - 删除等效的 `while deque.len() > n { deque.pop_front(); }` 循环
  - 验证边界条件（空 deque、`n >= len`）
- [ ] `VecDeque::retain_back`：
  - **仅当 nightly/beta 已确认该方法进入 1.97 时才激活**
  - 若未稳定，保持等效实现，并在注释中标注 "推迟至 1.98"
- [ ] `float_algebraic` / `RandomSource` / `box_vec_non_null` / `int_format_into` / C-variadic：
  - 对照 1.97 Release Notes 逐条确认是否稳定
  - 稳定的取消注释并写实际调用；未稳定的保持现状并更新注释
- [ ] 运行：`cd crates/c08_algorithms && cargo test --lib`

---

## 阶段 3：全 Workspace 验证（1 小时）

- [ ] `cargo check --workspace`
- [ ] `cargo test --workspace`
- [ ] `cargo clippy --workspace -- -D warnings`（若项目启用）
- [ ] 修复所有因 1.97 引入的编译/Clippy 警告

---

## 阶段 4：文档状态刷新（2 小时）

### 4.1 `concept/07_future/rust_1_97_preview.md`

- [ ] 标题改为 "Rust 1.97 稳定特性"
- [ ] 将 🧪 Nightly / 🔄 PFCP 标记更新为 ✅ Stable（未稳定的改为 📋 跟踪）
- [ ] 在文档顶部添加 1.97 Release Notes 引用：

  ```markdown
  > **官方发布说明**: <https://blog.rust-lang.org/2026/07/09/Rust-1.97.0.html>
  ```

- [ ] 删除或更新 "预计稳定日期" 等前瞻性措辞
- [ ] 检查所有 `rust,ignore` 代码块，确认 1.97 稳定的示例可改为 `rust` 可编译

### 4.2 迁移至稳定特性文档目录（可选，建议执行）

- [ ] 将 `concept/07_future/rust_1_97_preview.md` 复制/迁移到 `docs/06_toolchain/06_21_rust_1_97_features.md`
- [ ] 在原文件顶部添加重定向说明：

  ```markdown
  > **已稳定**: 本文档中的特性已在 Rust 1.97.0 稳定。详细内容已迁移至 `docs/06_toolchain/06_21_rust_1_97_features.md`。
  ```

### 4.3 相关概念文档状态更新

- [ ] `concept/03_advanced/08_nll_and_polonius.md`：更新时间戳
- [ ] `concept/00_meta/terminology_glossary.md`：将 1.97 术语状态改为 ✅ Stable
- [ ] 搜索全仓库 `1.97` 相关标记，统一刷新状态

---

## 阶段 5：练习补全（1.5 小时）

- [ ] 在 `exercises/src/` 或 `exercises/tests/` 中新增 1.97 特性测验：
  - `VecDeque::truncate_front` 行为验证
  - `VecDeque::retain_back`（若已稳定）
  - `RandomSource` / 浮点代数方法（若已稳定）
- [ ] 运行：`cd exercises && cargo test`

---

## 阶段 6：CHANGELOG 与版本号（1 小时）

- [x] `CHANGELOG.md` 顶部已预置 `[3.1.0]` 模板（2026-06-22）
- [ ] 发布日：根据实际稳定特性，完善 `[3.1.0]` 条目细节
- [ ] 若项目使用语义化版本，更新 `Cargo.toml` workspace version：`3.1.0`

---

## 阶段 7：发布与归档（30 分钟）

- [ ] 运行最终验证：`cargo test --workspace`
- [ ] 提交并推送：`git commit -m "chore: stabilize Rust 1.97.0 support"`
- [ ] 创建 Pull Request 并请求 review（或按仓库流程直接合并）
- [ ] 更新 `.kimi/EXECUTION_CHECKLIST_2026_06_22.md` 中 A3.x 系列条目为完成
- [ ] 将本清单归档到 `archive/project_reports/` 或类似位置

---

## 风险快速检查表

| 现象 | 应对措施 |
|:---|:---|
| 某特性未进入 1.97 | 保持等效实现；更新文档状态为 "推迟至 1.98" |
| 稳定 API 签名与 nightly 不同 | 不要直接取消注释，按实际签名重写 |
| Windows 构建失败 | 检查 `aws-lc-rs`/`ring` 依赖是否需要 `--no-default-features` |
| 测试超时或不稳定 | 单独运行失败测试，排除网络/文件系统依赖 |

---

## 参考链接

- Rust 1.97 Release Notes（发布当日替换为真实 URL）: `https://blog.rust-lang.org/2026/07/09/Rust-1.97.0.html`
- 项目 1.97 准备计划: `.kimi/plan_rust_1_97_stabilization.md`
- 4 周执行检查清单: `.kimi/EXECUTION_CHECKLIST_2026_06_22.md`
