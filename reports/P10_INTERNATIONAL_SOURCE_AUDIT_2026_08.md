# P10 国际权威来源语义等价性审计报告

**EN**: P10 International Authority Source Semantic Equivalence Audit Report
**Summary**: Audit 10 core `concept/` pages against Reference/Nomicon/TRPL/latest RFCs, fix terminology drift and dead links, and record remaining risks for P10-7.

**日期**: 2026-08-04
**范围**: 10 个核心 `concept/` 权威页 + `scripts/check_authority_freshness.py --strict` 全库新鲜度巡检
**执行人**: P10-7 子任务代理

---

## 1. 执行摘要

本轮 P10-7 完成了：

1. **权威源新鲜度巡检**：运行 `scripts/check_authority_freshness.py --strict`，上游 stable 1.97.1 与库内一致；1.98.0 beta 迁移尚未到期。
2. **10 个核心页抽样**：覆盖所有权、借用、生命周期、trait、泛型、并发、async、Pin/Unpin、unsafe、错误处理。
3. **术语与链接漂移修复**：
   - 将 `concept/03_advanced/01_async/01_async.md` 中误标的 **RFC 2592 → Pin** 修正为 **RFC 2349**，同步更新权威来源表。
   - 将 5 个概念页中已失效的 `doc.rust-lang.org/nomicon/pin.html` 替换为现行 `doc.rust-lang.org/std/pin/index.html`。
   - 修复 `concept/05_comparative/05_idioms_patterns_architecture/` 下 9 个骨架页的前置概念死链（Result/Option、structs、Drop、Send/Sync、channels 等相对路径）。
4. **术语表**：`concept/00_meta/01_terminology/01_terminology_glossary.md` 已包含 `dyn 兼容性`、`Pin`、`Unpin` 等条目，本次无需新增。

**关键结论**：抽样页与国际权威来源保持语义等价；`kb_auditor --link-check` 死链从 9 个降至 **0**；剩余 **25 个跨层引用问题** 集中在 `05_idioms_patterns_architecture` 骨架页（缺少 L4 向下引用），属于 P10-3 内容填充范畴，不在本次审计范围内修复。

---

## 2. 自动化新鲜度巡检

```bash
python scripts/check_authority_freshness.py --strict
```

结果：

- `release notes`: 54 页引用
- `rust-lang blog`: 125 页引用
- `RFC repo / RFC book`: 228 页引用
- `Reference / Nomicon`: 643 页引用
- `TRPL / std docs`: 598 页引用
- `Ferrocene`: 36 页引用
- `Project Goals`: 58 页引用
- `Inside Rust / internals`: 57 页引用
- 上游 stable: **1.97.1**，与库内一致
- 1.98.0 稳定日: 2026-08-20，距到期 16 天
- **exit 0，无 WARN**

完整报告：[`reports/INTERNATIONAL_ALIGNMENT_FRESHNESS_2026_09.md`](./INTERNATIONAL_ALIGNMENT_FRESHNESS_2026_09.md)

---

## 3. 抽样页与语义等价性复核

| # | 抽样页 | 主题 | 对照权威来源 | 复核结论 | 修复项 |
|---:|---|---|---|---|---|
| 1 | `concept/01_foundation/01_ownership_borrow_lifetime/01_ownership.md` | 所有权 | TRPL Ch4、Reference | ✅ 语义等价 | 无 |
| 2 | `concept/01_foundation/01_ownership_borrow_lifetime/02_borrowing.md` | 借用 | TRPL Ch4、Reference | ✅ 语义等价 | 无 |
| 3 | `concept/01_foundation/01_ownership_borrow_lifetime/03_lifetimes.md` | 生命周期 | Reference lifetime-elision、TRPL Ch10 | ✅ 语义等价；P9 已将 `reference/lifetimes.html` 修正为 `reference/lifetime-elision.html` | 无 |
| 4 | `concept/02_intermediate/00_traits/01_traits.md` | trait / dyn 兼容性 | Reference items/traits、RFC 255 | ✅ 术语已对齐；`object safety` 统一为 `dyn compatibility` | 无 |
| 5 | `concept/02_intermediate/01_generics/01_generics.md` | 泛型 | TRPL Ch10、Reference | ✅ 语义等价 | 无 |
| 6 | `concept/03_advanced/00_concurrency/01_concurrency.md` | 并发 | TRPL Ch16、Reference | ✅ 语义等价 | 无 |
| 7 | `concept/03_advanced/01_async/01_async.md` | async/await | TRPL Ch17、RFC 2394/2592/2349 | ⚠️ 发现术语/链接漂移：Pin 被误标为 RFC 2592；nomicon/pin.html 死链 | 已修正（见 §4） |
| 8 | `concept/03_advanced/01_async/08_pin_unpin.md` | Pin/Unpin | std::pin、RFC 2349、Rustonomicon | ✅ P9 已修复 nomicon/pin.html；当前链接健康 | 无 |
| 9 | `concept/03_advanced/02_unsafe/01_unsafe.md` | unsafe | Reference、Nomicon | ✅ 语义等价 | 无 |
| 10 | `concept/02_intermediate/03_error_handling/01_error_handling.md` | 错误处理 | TRPL Ch9、std::result | ✅ 语义等价 | 无 |

### 3.1 外部链接抽样检查

对 10 个抽样页各取前 1–2 条外部权威链接进行 HEAD/GET 探测（超时 10s），结果全部 200：

| 来源页 | URL | 状态 |
|---|---|---:|
| `01_ownership.md` | `https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html` | 200 |
| `02_borrowing.md` | `https://doc.rust-lang.org/book/ch04-02-references-and-borrowing.html` | 200 |
| `03_lifetimes.md` | `https://doc.rust-lang.org/reference/lifetime-elision.html` | 200 |
| `01_traits.md` | `https://doc.rust-lang.org/reference/items/traits.html#dyn-compatibility` | 200 |
| `01_generics.md` | `https://doc.rust-lang.org/book/ch10-00-generics.html` | 200 |
| `01_concurrency.md` | `https://doc.rust-lang.org/book/ch16-04-extensible-concurrency-sync-and-send.html` | 200 |
| `01_async.md` | `https://doc.rust-lang.org/book/ch17-00-async-await.html` | 200 |
| `08_pin_unpin.md` | `https://doc.rust-lang.org/std/pin/index.html` | 200 |
| `01_unsafe.md` | `https://doc.rust-lang.org/nomicon/` | 200 |
| `01_error_handling.md` | `https://doc.rust-lang.org/book/ch09-00-error-handling.html` | 200 |

---

## 4. 修复明细

### 4.1 RFC 编号漂移：`RFC 2592` 误用于 Pin

**问题**：`concept/03_advanced/01_async/01_async.md` 与 `concept/03_advanced/01_async/03_async_patterns.md` 中将 Pin 设计 RFC 标为 `RFC 2592`。实际上 RFC 2592 是 `futures_api`（Future trait / RawWaker），Pin 由 **RFC 2349** 引入。

**修复**：

- `concept/03_advanced/01_async/01_async.md:271`：改为 `[RFC 2349 — Pin](https://rust-lang.github.io/rfcs/2349-pin.html)`，并将 `Future` trait 来源指向 `[RFC 2592](https://rust-lang.github.io/rfcs/2592-futures.html)`。
- `concept/03_advanced/01_async/01_async.md:2496`：权威来源表中的 Pin 行同步改为 RFC 2349。
- `concept/03_advanced/01_async/03_async_patterns.md:705`：表格中 `RFC 2592 — Pin` 改为 `RFC 2349 — Pin`。

### 4.2 死链：`doc.rust-lang.org/nomicon/pin.html`

Rustonomicon 不再维护独立的 `pin.html` 页面，官方 Pin 文档已迁移至 `std::pin` 模块。

**修复文件**：

- `concept/03_advanced/01_async/01_async.md:783`
- `concept/03_advanced/02_unsafe/11_in_place_pinned_initialization.md`（2 处）
- `concept/04_formal/03_operational_semantics/12_pin_and_self_referential_semantics.md`
- `concept/04_formal/03_operational_semantics/13_in_place_initialization_semantics.md`（2 处）

统一替换为 `https://doc.rust-lang.org/std/pin/index.html`。

### 4.3 骨架页前置概念死链

`concept/05_comparative/05_idioms_patterns_architecture/` 下部分骨架页复制了早期目录结构中的相对路径，目标页已重命名或不存在。本次按 AGENTS.md §2 权威来源规则，仅修复链接指向现有权威页，不补充正文：

| 文件 | 原死链 | 修复后指向 |
|---|---|---|
| `01_idioms/02_error_propagation.md` | `02_intermediate/03_error_handling/01_result_option.md` | `02_intermediate/03_error_handling/01_error_handling.md` |
| `01_idioms/04_newtype.md` | `01_foundation/02_type_system/03_structs.md` | `01_foundation/07_modules_and_items/04_structs.md` |
| `01_idioms/05_typestate.md` | `03_advanced/04_unsafe/02_phantom_data.md` | `https://doc.rust-lang.org/std/marker/struct.PhantomData.html` |
| `01_idioms/06_raii_cleanup.md` | `02_intermediate/02_memory_management/02_drop.md` | `04_formal/05_rustc_internals/09_destructors.md` |
| `01_idioms/07_builder.md` | `01_foundation/02_type_system/03_structs.md` | `01_foundation/07_modules_and_items/04_structs.md` |
| `01_idioms/08_defer.md` | `02_intermediate/02_memory_management/02_drop.md` | `04_formal/05_rustc_internals/09_destructors.md` |
| `02_algorithms/05_lock_free_data_structures.md` | `03_advanced/00_concurrency/02_send_sync.md` | `03_advanced/00_concurrency/02_send_sync_auto_traits.md` |
| `04_architecture/04_actor.md` | `03_advanced/00_concurrency/03_channels.md` | `03_advanced/00_concurrency/03_concurrency_patterns.md` |
| `04_architecture/06_event_bus.md` | `03_advanced/00_concurrency/03_channels.md` | `03_advanced/00_concurrency/03_concurrency_patterns.md` |

---

## 5. 术语表同步

`concept/00_meta/01_terminology/01_terminology_glossary.md` 已包含：

- `dyn 兼容性 (dyn compatibility)` — 指向 Reference 最新判定矩阵
- `Pin / Unpin` — 指向 std 文档
- `自动 trait (Auto Trait)` — 含 Unpin

本次未发现需要新增或修改的术语条目。

---

## 6. 剩余风险与后续动作

| 风险 | 说明 | 建议后续任务 |
|---|---|---|
| **25 个跨层引用问题** | `05_idioms_patterns_architecture` 骨架页缺少向 L4 的向下引用 | P10-3 填充骨架页时一并补充前置/后置概念与 L4 链接 |
| **RAG 生产化工件缺口** | golden query set、embedding 微调、reranker/hybrid search 尚未落地 | P10-5 在 `tools/kg_rag/` 实现 |
| **1.98.0 迁移窗口** | 2026-08-20 附近需将 preview 页中 5 处 `stabilized-in-beta` 迁移到 `rust_1_98_stabilized.md` | P10-6 发布响应代理 |
| **ACM/DOI 链接 403** | `dl.acm.org` 与部分 `doi.org` 对自动化请求返回 403/404，浏览器可正常访问 | 季度人工复核，必要时补充 `https://doi.org/...` 跳转或归档链接 |

---

## 7. 验证命令与结果

```bash
# 1. 新鲜度巡检
python scripts/check_authority_freshness.py --strict
# exit 0, WARN 0

# 2. 死链检查
python scripts/kb_auditor.py --link-check
# 死链 0, 跨层问题 25（集中在 idioms 骨架页）

# 3. 命名规范
python scripts/check_naming_convention.py --strict
# ERROR=0 WARN=0
```

---

## 8. 文件变更清单

- 新增报告：
  - `reports/INTERNATIONAL_ALIGNMENT_FRESHNESS_2026_09.md`
  - `reports/P10_INTERNATIONAL_SOURCE_AUDIT_2026_08.md`
- 修改的概念页（仅链接/术语修正）：
  - `concept/03_advanced/01_async/01_async.md`
  - `concept/03_advanced/01_async/03_async_patterns.md`
  - `concept/03_advanced/02_unsafe/11_in_place_pinned_initialization.md`
  - `concept/04_formal/03_operational_semantics/12_pin_and_self_referential_semantics.md`
  - `concept/04_formal/03_operational_semantics/13_in_place_initialization_semantics.md`
  - `concept/05_comparative/05_idioms_patterns_architecture/` 下 9 个骨架页的前置概念链接
- 术语表：无修改

---

*报告生成于 P10-7 执行期间，与 `reports/INTERNATIONAL_ALIGNMENT_FRESHNESS_2026_09.md` 配套使用。*
