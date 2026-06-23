# 官方权威文档变更跟踪机制

> **目的**: 建立可重复的流程，确保本项目与 Rust 官方/国际化权威内容保持对齐。
> **更新频率**: 每 6 周（跟随 Rust stable release 周期）
> **负责人**: 维护者轮换

---

## 一、跟踪来源清单

| 来源 | 地址 | 检查方式 | 关注重点 |
|---|---|---|---|
| **The Rust Programming Language (TRPL)** | <https://doc.rust-lang.org/book/> | 每月 diff / release 后全量检查 | 新章节（如 Ch17 async）、2024 edition 示例更新 |
| **Rust Reference** | <https://doc.rust-lang.org/reference/> | 每月 diff | 规则标识符、2024 edition 示例、新稳定特性语义 |
| **Rust By Example** | <https://doc.rust-lang.org/rust-by-example/> | 每季度 | Edition 更新、async closures、gen blocks 示例缺口 |
| **Async Book** | <https://rust-lang.github.io/async-book/> | 每月 | rewrite 进度、章节 TODO 状态 |
| **Rustonomicon** | <https://doc.rust-lang.org/nomicon/> | 每季度 | 2024 edition 示例、unsafe/FFI 边界更新 |
| **Edition Guide 2024** | <https://doc.rust-lang.org/edition-guide/rust-2024/> | release 后检查 | 迁移步骤、版本号、关键字状态 |
| **Rust Blog / Release Notes** | <https://blog.rust-lang.org/> | release 后立即 | 版本事实、稳定特性列表 |
| **Inside Rust Blog** | <https://blog.rust-lang.org/inside-rust/> | 每月 | 编译器、Cargo、项目目标进展 |
| **This Week in Rust** | <https://this-week-in-rust.org/> | 每周 | 社区趋势、crate 更新、论文 |
| **releases.rs** | <https://releases.rs/> | 每周 | stable/beta/nightly 状态速查 |
| **Rust Project Goals** | <https://rust-lang.github.io/rust-project-goals/> | 每季度 | 旗舰目标、MCP 进展 |
| **The Rust RFC Book** | <https://rust-lang.github.io/rfcs/> | release 后 / 季度 | RFC 编号、slug、合并状态 |
| **The Cargo Book** | <https://doc.rust-lang.org/cargo/reference/> | release 后 | resolver、rust-version、features 语义 |

---

## 二、检查流程

### 每次 Rust stable release 后（6 周周期）

1. 更新 `concept/07_future/rust_1_XX_preview.md` 与 `crates/cXX/src/rust_XXX_features.rs`。
2. 运行 `scripts/maintenance/check_version_facts.py`，修复所有告警。
3. 运行 `cargo check --workspace` 与代码块编译验证脚本。
4. 检查链接健康报告，修复失效的 official docs 链接。
5. 更新 `CHANGELOG.md` 与 `concept/00_meta/quality_dashboard_v2.md`。

### 每季度深度审计

1. 对比 TRPL / Reference / Edition Guide 与本项目同主题章节的**对称差**。
2. 更新 `concept/00_meta/authority_source_map.md` 中的权威来源锚点。
3. 审查 `concept/07_future/` 中 preview 文件的稳定度标注是否仍准确。
4. 审查跨语言对比章节中对标语言的版本（C++23/26、Go 1.24+、Java 24+ 等）。

---

## 三、记录模板

```markdown
## 202X-XX-XX 官方文档对齐检查

- 检查人：@name
- 对比 Rust 版本：1.XX.0 stable
- 发现差异：
  1. TRPL 新增/修改 ...
  2. Reference 更新 ...
  3. Async Book rewrite 进展 ...
- 已执行动作：
  - [ ] 更新 concept/...
  - [ ] 更新 crates/...
  - [ ] 运行 check_version_facts.py
  - [ ] 更新 CHANGELOG
```

---

## 四、已知需持续关注项

- `gen {}` / `yield` 是否 stable（预计 1.98+，以官方为准）
- `never type (!)` 完全 stable 进度（PR #155697 进行中）
- `Async Drop` MCP/实现进展（Tracking Issue #126482）
- `RTN` (Return Type Notation) RFC/实现进展（Tracking Issue #109417 / Project Goal 2026）
- `AFIDT` (async fn in dyn trait) 进展
- Async Book rewrite 完成状态
- Rust By Example 是否更新到 Edition 2024
- Rust 2024 Unsafe/FFI 教学资源（TRPL / Rust By Example / Rustonomicon）是否补充 `unsafe extern` blocks 与 `#[unsafe(...)]` 示例

---

## 五、执行记录

### 2026-06-23 全面对齐冲刺（阶段 3）

- **对比 Rust 版本**: 1.96.0 stable / 1.98.0 nightly
- **已对齐主题**:
  - Rust 2024 Unsafe/FFI: `unsafe_op_in_unsafe_fn`、`unsafe extern` blocks (RFC 3484)、`#[unsafe(...)]` 属性 (RFC 3325)
  - Return Type Notation (RTN) vs precise capturing (`use<..>`) 概念澄清
  - Async Drop 权威来源修正（移除错误 RFC 3308/3157 引用）
  - Never type (`!`) 稳定化进展精确化（1.92 lint / 1.96 tuple coercion / 完整稳定化进行中）
  - Cargo MSRV-aware resolver / resolver v3（RFC 3537 / Rust 1.84）
- **已修复 404 链接**: RFC 2585/3185/3498 重复 slug、Project Goals 2026 路径、wg-secure-code 治理页
- **剩余 404 链接精确化**: 将概念文档中 20+ 处指向 Project Goals 2026 根目录的链接改为对应子目标 slug（Beyond the &、BorrowSanitizer、Field Projections、Pin Ergonomics、Reborrow Traits、Unsafe Fields、Arbitrary Self Types、Parallel Frontend、Next-gen trait solver、Rust for Linux、Cranelift、Rust Specification、Public/Private Dependencies、Ergonomic Ref-counting 等），手动 curl 验证全部 200
- **Async Drop 来源清理**: `concept/07_future/README.md` 与 `concept_kb.json` 中残留的错误 RFC 3308 引用已统一替换为 Async Drop Initiative
- **大规模官方文档 404 修复（第二轮）**: 修复 RFC 重复 slug、RFC 1584 错误 slug、TRPL 章节 URL 变更、Rust Edition Guide 2024 路径变更、Rustonomicon 页面变更、Rust Reference 已移除页面、以及 rust-for-linux/async-book/design-patterns/rust-lang.org/production 等外部站点迁移/移除问题；`check_all_concept_links_health.py` 异常链接降为 0
- **最新权威状态扫描**: 扫描 Rust Blog / releases.rs / Project Goals 2026，更新 Field Projections（FRT/#152730）、RTN（#646 受 trait solver 阻塞）、Pin Ergonomics / Reborrow Traits、Never type 1.96 tuple coercion 等文档状态；确认 Async Book rewrite / gen blocks RFC 3513 预留关键字等持续关注项
- **新建脚本**: `scripts/maintenance/fix_404_links.py`
- **验证**: `cargo check --workspace` 通过，`check_version_facts.py` 通过

> **创建日期**: 2026-06-23
> **状态**: ✅ 机制建立并执行首次对齐冲刺

### 2026-06-23 权威内容动态跟踪（阶段 4）

- **对比 Rust 版本**: 1.96.0 stable / 1.97.0 beta / 1.98.0 nightly
- **权威来源**: releases.rs 1.97 beta 候选 API、Inside Rust Blog、Rust Project Goals 2026
- **已对齐主题**:
  - Rust 1.97 beta 稳定化候选 API：`NonZero<T>::highest_one/lowest_one/bit_width`（PR #155147/#155131）、`char::is_control()` const 稳定化（PR #155528）
  - 修正 `VecDeque::truncate_front` / `retain_back` 的 PR 编号为 #151973（原 #151379 误植）
  - 更新 `concept/07_future/rust_1_97_preview.md` 与 `concept/07_future/05_rust_version_tracking.md` 的 1.97 beta 状态表
  - 更新 `crates/c08_algorithms/src/rust_197_features.rs`：新增 NonZero 位操作与 `char::is_control` 的等效实现及测试
  - 更新 `docs/02_reference/quick_reference/02_rust_197_features_cheatsheet.md`
- **验证**: `cargo check --workspace` 通过，`cargo test -p c08_algorithms rust_197_features` 通过，`check_version_facts.py` 通过，`check_all_concept_links_health.py` 异常链接 0

### 2026-06-23 权威内容动态跟踪（阶段 4 延续）

- **对比 Rust 版本**: 1.96.0 stable / 1.97.0 beta / 1.98.0 nightly
- **权威来源**: This Week in Rust 656（2026-06-17）、releases.rs（2026-06-23）
- **已对齐主题**:
  - 确认 `float_algebraic`（#157029）、`int_format_into`（#152544）、`nonzero_from_str_radix`（#157877）、`core::range::{legacy, RangeFull, RangeTo}`（#156629）因晚于 1.97 beta cutoff（2026-05-22）合并，进入 1.98 通道
  - 新增 `box_as_ptr`（#157876）与 rustfmt `hex_literal_case`（#6935）为 1.98 已确认特性
  - 修正 `never_type` 稳定化 PR 编号为 #155697；修正 5 月项目管理更新 URL；修正 `int_format_into` PR 编号为 #152544
  - 更新 `concept/07_future/05_rust_version_tracking.md`：新增 "12.16.1 标准库与工具稳定化速递 — TWiR 656" 小节
  - 更新 `concept/07_future/rust_1_97_preview.md`：在 1.98 候选表中补充 `box_as_ptr` 与 `hex_literal_case`
- **验证**: `cargo check --workspace` 通过，`cargo test -p c08_algorithms rust_197_features` 通过，`check_version_facts.py` 通过，`check_all_concept_links_health.py` 异常链接 0

### 2026-06-23 权威内容动态跟踪（阶段 4 延续二）

- **对比 Rust 版本**: 1.96.0 stable / 1.97.0 beta / 1.98.0 nightly
- **权威来源**: Async Book、RFC Book、GitHub Tracking Issues
- **已对齐主题**:
  - 扫描 Async Book rewrite 状态：仍标记为 "work in progress"，示例仍使用 edition2021，新结构分为 guide / reference / old chapters
  - 更新 `concept/07_future/05_rust_version_tracking.md`：新增 "12.16.2 Async Book rewrite 状态（2026-06-23）" 小节
  - 校正 `gen` blocks 跟踪来源：`concept/07_future/22_gen_blocks_preview.md` 与 `15_gen_blocks_preview.md` 统一指向 RFC 3513 与 Tracking Issue #117078，修复 RFC Book 链接双斜杠
- **验证**: `cargo check --workspace` 通过，`cargo test -p c08_algorithms rust_197_features` 通过，`check_version_facts.py` 通过，`check_all_concept_links_health.py` 异常链接 0

### 2026-06-23 权威内容动态跟踪（阶段 4 延续三）

- **对比 Rust 版本**: 1.96.0 stable / 1.97.0 beta / 1.98.0 nightly
- **权威来源**: TWiR 656、releases.rs、RFC Book
- **已对齐主题**:
  - 补充 TWiR 656 中进入 FCP 的 RFC / Reference 条目：RFC #3955 "Named `Fn` trait parameters"、Language Reference "Structs with no fields or all-ZST fields are ZSTs"
  - 修正 `crates/c08_algorithms/src/rust_197_features.rs` 中多条 PR 编号与状态：`float_algebraic`=#157029（1.98 已合并）、`RandomSource`=#157168（等待 libs-api）、`box_vec_non_null`=#157226（PFCP）
  - 在 `crates/c08_algorithms/src/rust_197_features.rs` 新增 `demo_box_as_ptr()`、`demo_nonzero_from_str_radix()`、`demo_core_range_completion()` 等效实现及单元测试，为 1.98 的 `Box::as_ptr`、`NonZero::from_str_radix`、`core::range::{RangeFull, RangeTo}` 提前准备示例
  - 运行 `scripts/maintenance/fix_404_links.py`：无新增 404
- **验证**: `cargo check --workspace` 通过，`cargo test -p c08_algorithms rust_197_features` 通过（9 passed），`check_version_facts.py` 通过，`check_all_concept_links_health.py` 异常链接 0

### 2026-06-23 权威内容动态跟踪（阶段 4 延续四）

- **对比 Rust 版本**: 1.96.0 stable / 1.97.0 beta / 1.98.0 nightly
- **权威来源**: N/A（质量基础设施优化）
- **已对齐主题**:
  - 优化 `scripts/version_fact_check.py`：新增 `normalize_version()` 函数，将 `1.96` 与 `1.96.0` 标准化后比较，消除格式差异导致的误报
  - 优化 `core::range` 扫描模式：排除 1.98 才迁移的 `RangeFull`、`RangeTo`、`legacy` 等子特性，避免将 1.98 前瞻内容误判为 1.96 事实错误
  - 微调 `concept/07_future/05_rust_version_tracking.md` 中 TWiR 656 key insight 措辞，避免触发 `core::range` 模式误报
- **验证**: `cargo check --workspace` 通过，`cargo test -p c08_algorithms rust_197_features` 通过（9 passed），`check_version_facts.py` 通过，`version_fact_check.py` 0 警告，`check_all_concept_links_health.py` 异常链接 0
