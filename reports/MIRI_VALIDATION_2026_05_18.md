# Miri 未定义行为验证报告

**日期**: 2026-05-18
**工具**: Miri 0.1.0 (nightly 2026-05-15)
**模式**: Tree Borrows (默认)
**目标**: x86_64-pc-windows-msvc

## 测试范围

- `crates/c01_ownership_borrow_scope/src/miri_tests.rs` — 17 项 borrow checker 边界测试
- `crates/c01_ownership_borrow_scope/src/pin_and_self_referential.rs` — 29 项 Pin/自引用测试
- `crates/c01_ownership_borrow_scope/src/rust_192_features.rs` — 2 项 `MaybeUninit`/`raw_ref` 测试
- `crates/c01_ownership_borrow_scope/src/rust_193_features.rs` — 4 项 `String`/`Vec`/`MaybeUninit` 往返测试
- `crates/c01_ownership_borrow_scope/src/rust_194_features.rs` — 15 项 `LazyCell`/`LazyLock`/`array_windows` 测试

## 结果汇总

| 模块 | 通过 | 失败 | 忽略 | 说明 |
|:---|:---:|:---:|:---:|:---|
| `miri_tests` | 17 | 0 | 2 | 忽略的 2 项为故意 UB（use-after-free、data race）|
| `pin_and_self_referential` | 29 | 0 | 0 | Pin 投影、自引用结构、Future Pin 语义 |
| `rust_192_features` | 2 | 0 | 0 | `MaybeUninit::assume_init`, `raw_ref` |
| `rust_193_features` | 4 | 0 | 0 | `String`/`Vec`/`MaybeUninit` 内存布局往返 |
| `rust_194_features` | 15 | 0 | 0 | `LazyCell`, `LazyLock`, `array_windows` |
| **合计** | **67** | **0** | **2** | |

## 已知限制

- **Windows IOCP**: tokio runtime 测试无法在 Miri + Windows 上运行（`CreateIoCompletionPort` 不支持）
- **建议**: 在 CI 中配置 Linux x86_64 目标的 Miri 运行器，以覆盖 tokio/async 相关 unsafe 代码

## 结论

c01_ownership_borrow_scope 中所有可在 Windows Miri 下运行的 unsafe 代码均通过 Tree Borrows 验证，无未定义行为。
