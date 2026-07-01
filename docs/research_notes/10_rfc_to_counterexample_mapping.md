# RFC 到反例自动化映射索引 {#rfc-到反例自动化映射索引}

> **概念族**: 权威来源对齐 / RFC / 反例
> **内容分级**: [核心级]
> **层级**: L0-L5
> **Bloom 层级**: L5-L6 (分析/评价)
> **Rust 版本**: 1.96.0+ (Edition 2024)
> **状态**: ✅ 已完成
> **创建日期**: 2026-06-29
> **最后更新**: 2026-06-29

---

## 目录 {#目录}

- [RFC 到反例自动化映射索引 {#rfc-到反例自动化映射索引}](#rfc-到反例自动化映射索引-rfc-到反例自动化映射索引)
  - [目录 {#目录}](#目录-目录)
  - [一、说明 {#一说明}](#一说明-一说明)
  - [二、RFC 到反例映射表 {#二rfc-到反例映射表}](#二rfc-到反例映射表-二rfc-到反例映射表)
  - [三、自动化映射建议 {#三自动化映射建议}](#三自动化映射建议-三自动化映射建议)
  - [四、维护清单 {#四维护清单}](#四维护清单-四维护清单)
  - [相关概念 {#相关概念}](#相关概念-相关概念)
  - [学术权威参考 {#学术权威参考}](#学术权威参考-学术权威参考)
  - [社区权威参考 {#社区权威参考}](#社区权威参考-社区权威参考)

---

## 一、说明 {#一说明}

本文档建立 **Rust RFC** 与项目内 **反例/形式化文档** 之间的双向映射，帮助维护者：

1. 快速定位某个 RFC 在哪些反例文件中有对应覆盖；
2. 快速判断某个反例文件引用了哪些 RFC 权威来源；
3. 为后续自动化脚本扫描 RFC 链接、生成映射报告提供人工基线。

> **编号核对说明**：下表中的 RFC 编号已与 `rust-lang.github.io/rfcs/` 和 `github.com/rust-lang/rfcs` 实际内容核对。原稿中部分编号存在笔误，已更正为实际对应 RFC：
>
> - "Unsafe blocks in unsafe fn" 对应 **RFC 2585**（非 2584）；
> - "Async fn in trait" 对应 **RFC 3185**（非 3381）；
> - "gen blocks" 对应 **RFC 3513**（非 3516）。

---

## 二、RFC 到反例映射表 {#二rfc-到反例映射表}

| RFC 编号 | RFC 标题 | 稳定版本 | 关键约束 | 对应反例文档 | 状态 |
|----------|----------|----------|----------|--------------|------|
| [RFC 1858](https://github.com/rust-lang/rfcs/pull/1858) | Immovable types | 未合并（已关闭） | 不可移动类型、自引用与 `Pin` 的前身讨论 | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) | 📝 |
| [RFC 2094](https://rust-lang.github.io/rfcs/2094-nll.html) | Non-lexical lifetimes | 1.63 | 借用检查器基于 MIR 的非词法生命周期分析，打破词法作用域限制 | [formal_methods/60_ownership_counterexamples.md](formal_methods/60_ownership_counterexamples.md) / [type_theory/10_lifetime_formalization.md](type_theory/10_lifetime_formalization.md) | ✅ |
| [RFC 2394](https://rust-lang.github.io/rfcs/2394-async_await.html) | async/await | 1.39 | `async fn`/`async {}` 语法、Future 状态机、`.await` 语义 | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) / [formal_methods/10_async_state_machine.md](formal_methods/10_async_state_machine.md) | ✅ |
| [RFC 2580](https://rust-lang.github.io/rfcs/2580-ptr-meta.html) | Pointer metadata | 未稳定（nightly `ptr_metadata`） | `Pointee::Metadata`、`metadata()`、`DynMetadata`、胖指针拆装 | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) | 🔄 |
| [RFC 2585](https://rust-lang.github.io/rfcs/2585-unsafe-block-in-unsafe-fn.html) | Unsafe blocks in unsafe fn | 1.52.0（lint 稳定）；2024 Edition 默认 warn | `unsafe fn` 体不再隐式视为 `unsafe {}`，需显式 `unsafe_op_in_unsafe_fn` | [formal_methods/60_unsafe_counterexamples.md](formal_methods/60_unsafe_counterexamples.md) / [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) | ✅ |
| [RFC 3185](https://rust-lang.github.io/rfcs/3185-static-async-fn-in-trait.html) | Static async fn in traits | 1.75 | trait 中 `async fn` 语法糖、匿名关联类型、静态分发限制 | [formal_methods/60_concurrency_async_counterexamples.md](formal_methods/60_concurrency_async_counterexamples.md) | ✅ |
| [RFC 3513](https://rust-lang.github.io/rfcs/3513-gen-blocks.html) | gen blocks | 未稳定（Rust 2024 保留 `gen` 关键字） | `gen {}` 生成器块、`yield` 语义、迭代器与借用跨越 yield 点限制 | [10_version_evolution_counterexamples.md](10_version_evolution_counterexamples.md) | 🔄 |

状态图例：

- ✅ — RFC 已稳定且反例文档已覆盖关键约束；
- 🔄 — RFC 尚未稳定或部分稳定，反例文档标记为预览/实验；
- 📝 — RFC 未合并，仅作为概念历史参考。

---

## 三、自动化映射建议 {#三自动化映射建议}

未来可通过一个维护脚本实现 RFC→反例映射的半自动生成：

1. **扫描范围**
   - 遍历 `docs/research_notes/**/*.md`；
   - 仅关注文件名包含 `counterexample` 或 `反例` 的 Markdown 文件。

2. **RFC 链接识别**
   - 匹配以下两类权威 URL：
     - `https://rust-lang.github.io/rfcs/NNNN-*.html`
     - `https://github.com/rust-lang/rfcs/(pull|issues|blob)/NNNN*`
   - 从 URL 中提取 RFC 编号。

3. **映射输出**
   - 对每个反例文件，输出其中引用的 RFC 编号列表；
   - 对每个 RFC，聚合引用它的反例文件列表；
   - 对未引用任何 RFC 的反例文件，打印 informational 列表（ℹ️），供维护者人工补充，不影响退出码。

4. **与本文档对齐**
   - 将脚本输出与上表人工基线进行 diff；
   - 当新的 RFC 稳定或新的反例文件加入时，触发本文档增量更新。

5. **集成入口**
   - 建议在 `scripts/maintenance/check_research_notes.py` 中新增 `check_rfc_counterexample_mapping()` 作为信息性检查项；
   - 在 CI 中每日运行，生成映射报告并提交到 `.kimi/` 或 `reports/`。

---

## 四、维护清单 {#四维护清单}

- [x] 核对 RFC 编号与 `rust-lang.github.io/rfcs/` 实际页面；
- [x] 确认所有对应反例文档路径存在；
- [x] 记录各 RFC 稳定版本与关键约束；
- [ ] 待 `ptr_metadata` / `gen_blocks` 稳定后更新状态列；
- [ ] 待自动化脚本实现后，将输出结果回填到本表。

> **权威来源**: [Rust RFCs](https://rust-lang.github.io/rfcs/) | [Rust RFC Repository](https://github.com/rust-lang/rfcs) | [Rust Tracking Issues](https://github.com/rust-lang/rust/labels/C-tracking-issue)

## 相关概念 {#相关概念}

- [RFC 对齐索引](10_rfc_alignment_index.md)
- [RFC 实现状态追踪表](10_rfc_tracking_status.md)
- [权威来源对齐网络总索引](10_authoritative_source_alignment_network.md)
- [形式化方法总索引](10_formal_methods_master_index.md)
- [版本演进边界与迁移反例](10_version_evolution_counterexamples.md)
- [知识图谱索引](10_knowledge_graph_index.md)

---

## 学术权威参考 {#学术权威参考}

本对齐矩阵同时参考以下 P1 学术权威来源，以形成完整的官方-学术对照网络：

- [RustBelt](https://plv.mpi-sws.org/rustbelt/popl18/)
- [Tree Borrows](https://plf.inf.ethz.ch/research/pldi25-tree-borrows.html)
- [RustSEM](https://link.springer.com/article/10.1007/s10703-024-00460-3)
- [Aeneas](https://aeneas-verification.github.io/)

## 社区权威参考 {#社区权威参考}

- [Inside Rust Blog](https://blog.rust-lang.org/inside-rust/)
- [This Week in Rust](https://this-week-in-rust.org/)
