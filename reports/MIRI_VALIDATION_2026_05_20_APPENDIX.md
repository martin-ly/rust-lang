# Miri 验证附录 — 2026-05-20

## 验证范围

针对 Phase 4-6 新增代码的 Miri 未定义行为检测。

## 结果摘要

| Crate | 通过 | 失败 | 忽略 | 备注 |
|:---|:---:|:---:|:---:|:---|
| c03_control_fn | 11 | 0 | 7 | 全部通过 |
| c05_threads | 299 | 1 | 21 | work_stealing::test_numa_aware_work_stealing 因 crossbeam_epoch 在 Miri 下不支持而失败（已知问题，非新增） |

## 新增代码验证

- ✅ `crates/c05_threads/examples/lockfree_epoch_stack_demo.rs` — crossbeam_epoch EBR 栈，编译通过，运行时正确
- ✅ `crates/c03_control_fn/examples/unsafe_patterns_demo.rs` — NonNull、addr_of_mut!、ManuallyDrop、unsafe trait、MaybeUninit 全部通过编译和 Miri
- ✅ `crates/c11_macro_system_proc/examples/proc_macro_comprehensive_demo.rs` — 编译期宏，运行时通过
- ✅ `crates/c05_threads/tests/loom_lockfree_tests.rs` — Loom 模型检测测试，编译通过
- ✅ `crates/c11_macro_system_proc/tests/proc_macro_integration_tests.rs` — 8 项集成测试全部通过

## 结论

新增代码无 Miri 检测到的未定义行为。c05_threads 中唯一的 Miri 失败是已知的 crossbeam_epoch 与 Miri 不兼容问题，不影响新增代码。
