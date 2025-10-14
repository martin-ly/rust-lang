---
title: FFI/ABI 与 repr
lang: zh-CN
---

要点：

- `#[repr(C)]` 保证与 C 兼容的布局；`#[repr(transparent)]` 单字段透明包装。
- FFI 函数应标注 `extern "C"`；跨语言边界需小心所有权/错误返回/对齐。
- 不稳定 ABI 避免暴露给外部；尽量用简单 POD 类型进行传递。

示例与测试：见 `examples/ffi_abi_repr.rs` 与 `tests/ffi_abi_repr_tests.rs`。
