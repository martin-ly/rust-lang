# Rust 1.98.0 稳定特性（跟踪骨架）

> **EN**: Rust 1.98.0 Stabilized Features (Tracking Skeleton)
> **Summary**: Rust 1.98.0 稳定特性的权威汇总页骨架：特性矩阵已迁移自 1.98 周期跟踪清单，正文待 2026-08-20 稳定后按官方发布笔记实测填充。
>
> **受众**: [进阶] / [专家]
> **Bloom 层级**: L2-L3
> **内容分级**: [参考级]
> **权威来源**: 本文件为 `concept/` 权威页（Rust 1.98 稳定特性的 canonical 汇总；稳定生效日为 2026-08-20，此前以 [`rust_1_98_preview.md`](rust_1_98_preview.md) 为周期跟踪入口）。
> **Rust 版本**: 1.98.0+ (Edition 2024) —— **预计 2026-08-20 进入 stable 通道，当前为跟踪骨架**
> **最后更新**: 2026-07-14
> **状态**: ⏳ 骨架（1.98.0 已于 2026-07-03 分支进入 beta；正文待稳定后实测填充）
>
> **权威来源**: · [Rust 1.98.0 Release Notes (beta)](https://releases.rs/docs/1.98.0/) · [Rust Reference](https://doc.rust-lang.org/reference/introduction.html) · [TRPL](https://doc.rust-lang.org/book/title-page.html) · [RFC Book](https://rust-lang.github.io/rfcs/)
>
> **前置概念**: [Rust 版本跟踪](01_rust_version_tracking.md) · [Rust 1.97 稳定特性](rust_1_97_stabilized.md)
> **后置概念**: [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md)

> **Canonical 分工（preview ↔ stabilized）**
>
> - [`rust_1_98_preview.md`](rust_1_98_preview.md)：1.98+ **周期跟踪页**——nightly 特性、RFC 进展、API 探测，随每两周巡检滚动更新；1.98.0 发布后滚动为 1.99+ 跟踪。
> - 本页：1.98.0 **稳定特性权威汇总**——稳定后唯一记录「1.98 实际稳定了什么」的 canonical 页；稳定前仅保留特性矩阵骨架与状态快照，不重复 preview 页的跟踪正文。

---

## 0. 1.98 特性矩阵（迁移自 preview 跟踪清单，2026-07-14 快照）

> 来源：[`rust_1_98_preview.md`](rust_1_98_preview.md) §零「1.98 周期跟踪清单」（12 项）。本表为稳定前状态快照；1.98.0 发布后将按官方发布笔记重排为「已稳定 / 未随 1.98 稳定」两类。

| # | 特性 | 当前状态 | 稳定后归属节 | 跟踪链接 |
|:---:|:---|:---|:---|:---|
| 1 | `Panic[Hook]Info` 中 `Location<'_>` 生命周期改为 `'static` | stabilized in 1.98 beta | §1.1 | [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/) |
| 2 | mingw-w64 C 工具链更新 | stabilized in 1.98 beta | §1.2 | [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/) |
| 3 | 移除 Solaris 上 `File::lock` 实现（语义错误） | stabilized in 1.98 beta | §1.3 | [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/) |
| 4 | 移除 `-Zemscripten-wasm-eh` | stabilized in 1.98 beta | §1.4 | [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/) |
| 5 | Named `Fn` trait parameters（RFC #3955） | RFC merged（2026-07-08） | §2 | [RFC Book](https://rust-lang.github.io/rfcs/3955-named-fn-trait-parameters.html) |
| 6 | `#![register_{attribute,lint}_tool]`（RFC #3808） | RFC merged（2026-06-10） | §2 | [RFC Book](https://rust-lang.github.io/rfcs/3808-register-tool.html) |
| 7 | `todo!()` 不再触发 `unreachable_code`（RFC #3928） | RFC merged（2026-06-25） | §2 | [RFC Book](https://rust-lang.github.io/rfcs/3928-todo-overreach.html) |
| 8 | Public/Private Dependencies（RFC #3516） | RFC merged，Cargo 实现跟踪中 | §2 | [RFC Book](https://rust-lang.github.io/rfcs/3516-public-private-dependencies.html) |
| 9 | Safety Tags（RFC #3842） | FCP / 讨论中 | §3 | [rfcs#3842](https://github.com/rust-lang/rfcs/pull/3842) |
| 10 | Pin Ergonomics（`&pin mut` / `&pin const`） | nightly only（Project Goal 2026） | §4 | [预览页](../03_preview_features/14_pin_ergonomics_preview.md) |
| 11 | Async Drop | nightly only | §4 | [预览页](../03_preview_features/22_async_drop_preview.md) |
| 12 | Return Type Notation（RTN） | nightly only | §4 | [预览页](../03_preview_features/09_return_type_notation_preview.md) |

---

## 1. stabilized-in-beta 特性（4 项，随 1.98.0 beta 分支合入）

以下 4 项已随 1.98.0 beta 分支（2026-07-03 切分）合入，预计 2026-08-20 转 stable；各节当前仅登记状态与来源，稳定后按 §6 checklist 填充实测内容。

### 1.1 `Panic[Hook]Info` 中 `Location<'_>` 生命周期改为 `'static`

**状态**: stabilized in 1.98 beta（2026-08-20 转正） · **来源**: [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/)

> ⏳ **待稳定后实测填充**：稳定后补充——变更动机（`Location` 非 `'static` 对 panic hook 签名与 `Send + Sync` 约束的影响）、迁移影响（持有 `PanicHookInfo` / 自定义 panic hook 的代码）、最小示例与反例。

### 1.2 mingw-w64 C 工具链更新

**状态**: stabilized in 1.98 beta（2026-08-20 转正） · **来源**: [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/)

> ⏳ **待稳定后实测填充**：稳定后补充——捆绑的 mingw-w64/GCC 版本变化、对 `x86_64-pc-windows-gnu` 目标的影响（链接行为、异常模型）、Windows GNU 工具链迁移检查清单。

### 1.3 移除 Solaris 上 `File::lock` 实现（语义错误）

**状态**: stabilized in 1.98 beta（2026-08-20 转正） · **来源**: [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/)

> ⏳ **待稳定后实测填充**：稳定后补充——原实现的语义错误细节（Solaris `fcntl` 锁语义偏差）、移除后的行为（`File::lock` 在 Solaris 上返回错误或不支持）、受影响平台清单与替代方案。

### 1.4 移除 `-Zemscripten-wasm-eh`

**状态**: stabilized in 1.98 beta（2026-08-20 转正） · **来源**: [releases.rs 1.98.0](https://releases.rs/docs/1.98.0/)

> ⏳ **待稳定后实测填充**：稳定后补充——该 nightly 标志的历史用途（Emscripten WASM 异常处理）、移除原因（上游 LLVM/Emscripten 支持路径变化）、`wasm32-unknown-emscripten` 用户的迁移路径。

---

## 2. RFC merged 跟踪项（实现中，未必随 1.98 稳定）

> 以下为 RFC 已合并、实现与稳定化落在 1.98+ 周期的条目；稳定时逐一确认是否实际进入 1.98.0，未进入者留在 preview 页继续跟踪。

| 特性 | RFC | 合并日期 | 稳定后填充要点 |
|:---|:---|:---|:---|
| Named `Fn` trait parameters | [#3955](https://rust-lang.github.io/rfcs/3955-named-fn-trait-parameters.html) | 2026-07-08 | ⏳ 待稳定后实测填充：命名参数语法、对高阶回调 API 的影响 |
| `#![register_{attribute,lint}_tool]` | [#3808](https://rust-lang.github.io/rfcs/3808-register-tool.html) | 2026-06-10 | ⏳ 待稳定后实测填充：工具注册语义、Rust for Linux 依赖链 |
| `todo!()` 不再触发 `unreachable_code` | [#3928](https://rust-lang.github.io/rfcs/3928-todo-overreach.html) | 2026-06-25 | ⏳ 待稳定后实测填充：lint 行为变化前后对比 |
| Public/Private Dependencies | [#3516](https://rust-lang.github.io/rfcs/3516-public-private-dependencies.html) | —（Cargo 实现跟踪中） | ⏳ 待稳定后实测填充：`public = true` 语义、SemVer 检查影响 |

---

## 3. FCP / 讨论中（1.98 窗口内观察）

| 特性 | 状态 | 稳定后填充要点 |
|:---|:---|:---|
| Safety Tags（RFC #3842） | FCP / 讨论中（[rfcs#3842](https://github.com/rust-lang/rfcs/pull/3842)） | ⏳ 待稳定后实测填充：`#[safety(...)]` 属性语义与工具链支持；深度背景见 [Safety Tags 预览](../03_preview_features/03_safety_tags_preview.md) |

---

## 4. nightly only 跟踪项（1.98 不预期稳定）

> 以下条目稳定化路径在 1.99+，本页仅登记状态行；跟踪正文维护在 preview 页与各自预览页。

| 特性 | 状态 | 深度文档 |
|:---|:---|:---|
| Pin Ergonomics（`&pin mut` / `&pin const`） | nightly only（Project Goal 2026） | [Pin Ergonomics 预览](../03_preview_features/14_pin_ergonomics_preview.md) |
| Async Drop | nightly only（MCP #727 已通过） | [Async Drop 预览](../03_preview_features/22_async_drop_preview.md) |
| Return Type Notation（RTN） | nightly only（RFC 3654） | [RTN 预览](../03_preview_features/09_return_type_notation_preview.md) |

---

## 5. 标准库 API 候选（跟踪中，稳定后核对）

> 已确认进入 1.98 通道的 std API 清单当前维护在 [`rust_1_98_preview.md`](rust_1_98_preview.md) §2.1（`float_algebraic`、`int_format_into`、`core::range::{RangeFull, RangeTo}`、`NonZero<T>::from_str_radix`、`Box::as_ptr` / `as_mut_ptr` 等）。稳定后将逐条迁移到本节并补充示例。

- ⏳ **待稳定后实测填充**：§2.1 全部 API 的最终签名、稳定版本标注、可编译示例（stable 通道实测）。

---

## 6. 稳定后填充计划（2026-08-20 之后执行）

- [ ] 按官方 1.98.0 release notes 重排 §0 矩阵为「已稳定 / 未随 1.98 稳定」
- [ ] §1 四项 stabilized-in-beta 特性补动机/迁移影响/示例与反例（rustc 1.98 stable 实测）
- [ ] §2/§3 逐项确认是否实际进入 1.98.0，未进入者回退 preview 页
- [ ] §5 std API 清单迁移并补 stable 通道可编译示例
- [ ] preview 页移除已迁移条目并滚动为 1.99+ 跟踪（[`check_authority_freshness.py`](../../../scripts/check_authority_freshness.py) 检查 3 将在此后清零 WARN）
- [ ] 同步术语表（`concept/00_meta/01_terminology/01_terminology_glossary.md`）与 MSRV 评估

---

## 7. 关联文档

- [Rust 1.98+ 前沿特性预览](rust_1_98_preview.md)（周期跟踪入口，canonical 分工见文首）
- [Rust 1.97 稳定特性](rust_1_97_stabilized.md)
- [Rust 版本跟踪](01_rust_version_tracking.md)
- [Rust 发布流程](03_rust_release_process.md)
- [Rust 工具链（L6）](../../06_ecosystem/00_toolchain/01_toolchain.md)
- [1.97/1.98 API 等效实现与测试](../../../crates/c08_algorithms/src/rust_197_features.rs)

## ⚠️ 反例与陷阱

即使未来版本引入更多安全抽象，unsafe 操作必须显式标记这一底线不变。

### 反例：unsafe 块外解引用裸指针（rustc 1.97.0，--edition 2024 实测）

```rust,compile_fail,E0133
fn main() {
    let p: *const i32 = std::ptr::null();
    let _u = *p; // ❌ 裸指针解引用必须在 unsafe 块内
}
```

**实测错误**：`error[E0133]: dereference of raw pointer is unsafe and requires unsafe block`。

### ✅ 修正：把裸指针解引用放进 `unsafe` 块，并自行保证有效性

```rust
fn main() {
    let p: *const i32 = std::ptr::null();
    // ✅ unsafe 块显式承担不变量责任（此处仅示意，勿解引用空指针）
    if !p.is_null() {
        let _u = unsafe { *p };
    }
}
```
