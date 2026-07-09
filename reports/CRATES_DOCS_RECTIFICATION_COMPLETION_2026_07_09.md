# `crates/*/docs/` AGENTS.md §6.4 合规整治完成报告

**日期**: 2026-07-09
**范围**: `e:\_src\rust-lang\crates\*\docs\` 下全部 Markdown 文件
**整治目标**: 消除 `crates/*/docs/` 中的通用 Rust 概念重复正文，确保每个概念仅有 `concept/` 一个权威来源

---

## 1. 整治结果

| 指标 | 数值 |
|---|---|
| 扫描文件总数 | 568 |
| 已含 canonical header 文件 | 568 (100%) |
| 缺 canonical header 文件 | 0 |
| 迁移/新建 `concept/` 权威页 | 数十个（详见各 subagent 报告） |
| 替换为 stub 的概念指南/参考/FAQ/术语表/项目概览 | ~210+ |
| 补加 canonical header 的代码示例/教程 | ~30+ |

---

## 2. 主要操作

1. **概念指南迁移**: 将 `crates/*/docs/` 中关于所有权、借用、生命周期、类型系统、控制流、泛型、Trait、并发、异步、进程 IPC、算法、设计模式、网络、宏系统、WebAssembly、嵌入式等通用概念解释迁移到对应 `concept/` 权威页。
2. **原文件 stub 化**: 每个被迁移的原文件已替换为标题 + `**EN**` / `**Summary**` 元数据 + `> **权威来源**: concept/...` 链接 + 主题索引。
3. **代码示例类文件**: 保留内容，补加 canonical header，明确其 crate-specific 定位。
4. **导航/导图/矩阵/报告类文件**: 替换为重定向 stub 或摘要页，避免与 `concept/` 重复维护。
5. **`concept/SUMMARY.md`**: 随新建权威页持续更新索引。

---

## 3. 验证结果

| 检查项 | 命令 | 结果 |
|---|---|---|
| 内容重叠检测 | `python scripts/detect_content_overlap.py` | ✅ 通过；仅 2 对预存在的 Rust 1.97 版本追踪重复 |
| 死链/跨层引用检查 | `python scripts/kb_auditor.py --link-check` | ✅ 0 死链，0 跨层问题 |
| 编译检查 | `cargo check --workspace` | ✅ 通过 |
| Clippy | `cargo clippy --workspace -- -D warnings` | ✅ 通过 |
| 测试 | `cargo test --workspace` | ✅ 通过 |
| 安全审计 | `cargo audit --no-fetch` | ✅ 0 漏洞 |
| 供应链审计 | `cargo vet` | ✅ 通过（829 exempted / 922 audited） |
| mdbook 构建 | `mdbook build` | ✅ 通过（仅 search-index 过大警告） |

---

## 4. 备注

- 本次整治未执行 `git commit`；工作区共有约 565 个文件发生变更。
- 整治工作大量依赖并行 subagent；过程中曾一度触发 LLM API 配额上限，随后通过直接脚本 + 后续 subagent 批次继续推进并完成。
- 仅存的 2 对内容重复为 `concept/07_future/00_version_tracking/rust_1_97_preview.md` / `rust_1_97_stabilized.md` 与 `docs/06_toolchain/06_21_rust_1_97_features.md` 的 canonical + quick-reference 组合，属于预存允许重复。
- `cargo vet` 曾因 GitHub raw 内容 429 限流短暂失败，等待后重试通过。

---

## 5. 后续建议

1. 择机运行 `cargo vet prune` 清理历史豁免。
2. 建议将本次整治中生成/使用的临时脚本（`tmp/stub_*.py`、`tmp/add_*.py`）归档或清理，避免提交到版本控制。
3. 后续新增 `crates/*/docs/` 文件时，应直接遵循 AGENTS.md §6.4：通用概念必须链接到 `concept/`，禁止重复正文。
